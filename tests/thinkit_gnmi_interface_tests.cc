// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "tests/thinkit_gnmi_interface_tests.h"

#include <algorithm>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "include/nlohmann/json.hpp"
#include "lib/gnmi/gnmi_helper.h"
#include "p4_pdpi/pd.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "tests/thinkit_gnmi_interface_util.h"
#include "tests/thinkit_util.h"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

namespace pins_test {
namespace {

using ::nlohmann::json;
using ::testing::HasSubstr;
using ::testing::Not;

}  // namespace

void BreakoutDuringPortInUse(thinkit::Switch &sut,
                             gnmi::gNMI::StubInterface *sut_gnmi_stub,
                             RandomPortBreakoutInfo port_info,
                             absl::string_view platform_json_contents,
                             absl::string_view port_in_use,
                             const p4::config::v1::P4Info &p4_info,
                             const bool expect_breakout_failure) {
  // Get the original breakout info on the port.
  // This contains the state values of physical channels and
  // operational status information for ports in original breakout mode.
  ASSERT_OK_AND_ASSIGN(
      auto orig_breakout_info,
      GetBreakoutStateInfoForPort(sut_gnmi_stub, port_info.port_name,
                                  port_info.curr_breakout_mode));

  LOG(INFO) << "Using port " << port_info.port_name
            << " with current breakout mode " << port_info.curr_breakout_mode
            << " and port in use " << port_in_use;

  // Verify that all ports for the selected port are operationally up.
  for (const auto& p : orig_breakout_info) {
    ASSERT_OK_AND_ASSIGN(
        pins_test::AdminStatus port_admin_status,
        pins_test::GetInterfaceAdminStatusOverGnmi(*sut_gnmi_stub, p.first));
    if (port_admin_status != AdminStatus::kUp) continue;
    EXPECT_OK(pins_test::CheckInterfaceOperStateOverGnmi(*sut_gnmi_stub,
                                                         kStateUp, {p.first}));
  }

  // Get the p4rt port index of the port on which to install router interface.
  ASSERT_OK_AND_ASSIGN(auto port_id_by_interface,
                       GetAllInterfaceNameToPortId(*sut_gnmi_stub));
  ASSERT_OK_AND_ASSIGN(std::string in_use_port_index_value,
                       gutil::FindOrStatus(port_id_by_interface, port_in_use));
  int in_use_port_index;
  ASSERT_TRUE(absl::SimpleAtoi(in_use_port_index_value, &in_use_port_index));

  // Configure router interface on selected port to install port dependency.
  std::unique_ptr<pdpi::P4RuntimeSession> sut_p4_session;
  ASSERT_OK_AND_ASSIGN(sut_p4_session, pdpi::P4RuntimeSession::Create(sut));
  const sai::TableEntry pd_entry =
      gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
          R"pb(
            router_interface_table_entry {
              match { router_interface_id: "router-interface-1" }
              action {
                unicast_set_port_and_src_mac {
                  port: "$0"
                  src_mac: "02:2a:10:00:00:03"
                }
              }
            }
          )pb",
          in_use_port_index));
  ASSERT_OK(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      sut_p4_session.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      p4_info))
      << "SetForwardingPipelineConfig: Failed to push P4Info: ";
  ASSERT_OK(pdpi::ClearTableEntries(sut_p4_session.get()));

  ASSERT_OK_AND_ASSIGN(auto ir_p4info, pdpi::CreateIrP4Info(p4_info));
  ASSERT_OK_AND_ASSIGN(const p4::v1::TableEntry pi_entry,
                       pdpi::PartialPdTableEntryToPiTableEntry(pdpi::IrP4Info(), pd_entry));

  LOG(INFO) << "Installing router interface on port " << port_in_use
            << " on SUT";
  ASSERT_OK(pdpi::InstallPiTableEntry(sut_p4_session.get(), pi_entry));

  // Get breakout config for the new breakout mode.
  gnmi::SetRequest req;
  gnmi::SetResponse resp;
  grpc::ClientContext context;
  ASSERT_OK_AND_ASSIGN(auto port_index, GetPortIndex(platform_json_contents,
                                                     port_info.port_name));
  ASSERT_OK(GetBreakoutModeConfigFromString(req, sut_gnmi_stub, port_index,
                                            port_info.port_name,
                                            port_info.supported_breakout_mode));

  // Get expected port information for new breakout mode.
  ASSERT_OK_AND_ASSIGN(
      auto new_breakout_info,
      GetExpectedPortInfoForBreakoutMode(port_info.port_name,
                                         port_info.supported_breakout_mode));

  // Apply breakout config on port.
  LOG(INFO) << "Configuring breakout mode " << port_info.supported_breakout_mode
            << " on port " << port_info.port_name << " on DUT";
  auto status = sut_gnmi_stub->Set(&context, req, &resp);
  if (expect_breakout_failure) {
    // Expect the set operation to fail since the port/its child is in use.
    ASSERT_THAT(status, Not(gutil::IsOk()));
    EXPECT_THAT(status.error_message(),
                HasSubstr(absl::StrCat(
                    "SET failed: YangToDb_port_breakout_subtree_xfmr: port ",
                    port_in_use, " is in use")));
    auto non_existing_port_list = GetNonExistingPortsAfterBreakout(
        orig_breakout_info, new_breakout_info, false);
    // Verify breakout related state paths.
    ASSERT_OK(ValidateBreakoutState(sut_gnmi_stub, orig_breakout_info,
                                    non_existing_port_list));

    // Delete the created router interface on the port using P4 interface.
    LOG(INFO) << "Deleting router interface on SUT";
    ASSERT_OK(pdpi::ClearTableEntries(sut_p4_session.get()));

    // Retry port breakout.
    grpc::ClientContext context2;
    status = sut_gnmi_stub->Set(&context2, req, &resp);
  }
  ASSERT_OK(status);

  // Wait for breakout config to go through.
  // TODO: Investigate changing to polling loop.
  absl::SleepFor(absl::Seconds(60));

  // Verify that the config is successfully applied now.
  auto non_existing_port_list = GetNonExistingPortsAfterBreakout(
      orig_breakout_info, new_breakout_info, true);
  // Oper-status is expected to be down as breakout is applied on one side
  // only.
  for (auto& port : new_breakout_info) {
    port.second.oper_status = kStateDown;
    // For the logical ports that do not change on breakout, expect them to be
    // operationally up.
    auto it = orig_breakout_info.find(port.first);
    if (it != orig_breakout_info.end()) {
      if (it->second.physical_channels == port.second.physical_channels &&
          it->second.breakout_speed == port.second.breakout_speed) {
        port.second.oper_status = kStateUp;
      }
    }
  }
  ASSERT_OK(ValidateBreakoutState(sut_gnmi_stub, new_breakout_info,
                                  non_existing_port_list));
}

void TestGNMIParentPortInUseDuringBreakout(
    thinkit::Switch& sut, std::string& platform_json_contents,
    const p4::config::v1::P4Info& p4_info) {
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());
  // Get a random port from list of front panel ports that supports at least
  // one breakout mode of required type other than its current mode.
  ASSERT_OK_AND_ASSIGN(auto port, GetRandomPortWithSupportedBreakoutModes(
                                      *sut_gnmi_stub, platform_json_contents,
                                      BreakoutType::kAny));
  BreakoutDuringPortInUse(sut, sut_gnmi_stub.get(), port,
                          platform_json_contents,
                          /*port_in_use=*/port.port_name, p4_info,
                          /*expect_breakout_failure=*/true);
}

void TestGNMIChildPortInUseDuringBreakout(
    thinkit::Switch& sut, std::string& platform_json_contents,
    const p4::config::v1::P4Info& p4_info) {
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());
  // Get a random port from list of front panel ports that supports at least
  // one breakout mode of required type other than its current mode.
  auto port = GetRandomPortWithSupportedBreakoutModes(
      *sut_gnmi_stub, platform_json_contents,
      /*new_breakout_type=*/BreakoutType::kAny,
      /*current_breakout_type=*/BreakoutType::kChannelized);
  // Get a child port to install the router interface on.
  // Get the original breakout info on the port.
  // This contains the state values of physical channels and
  // operational status information for ports in original breakout mode.
  if (port.ok()) {
    ASSERT_OK_AND_ASSIGN(auto orig_breakout_info,
                         GetBreakoutStateInfoForPort(sut_gnmi_stub.get(),
                                                     port->port_name,
                                                     port->curr_breakout_mode));
    std::string port_in_use;
    for (const auto &p : orig_breakout_info) {
      if (p.first != port->port_name) {
        port_in_use = p.first;
        break;
      }
    }
    ASSERT_FALSE(port_in_use.empty());
    BreakoutDuringPortInUse(sut, sut_gnmi_stub.get(), *port,
                            platform_json_contents, port_in_use, p4_info,
                            /*expect_breakout_failure=*/true);
  } else {
    LOG(ERROR) << "Failed to get random port with new breakout type: "
               << BreakoutType::kAny
               << " and current breakout type: " << BreakoutType::kChannelized;
  }
}

void TestGNMIOtherMasterPortInUseDuringBreakout(
    thinkit::Switch &sut, std::string &platform_json_contents,
    const p4::config::v1::P4Info &p4_info) {
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());
  // Get a random port from list of front panel ports that supports at least
  // one breakout mode of required type other than its current mode.
  ASSERT_OK_AND_ASSIGN(auto port, GetRandomPortWithSupportedBreakoutModes(
                                      *sut_gnmi_stub, platform_json_contents,
                                      BreakoutType::kAny));
  // Get another random port from list of front panel ports to install router
  // interface on.
  std::vector<absl::string_view> allow_list;
  absl::flat_hash_map<std::string, std::string> interfaces_map;
  ASSERT_OK_AND_ASSIGN(interfaces_map, GetInterfaceToOperStatusMapOverGnmi(
                                           *sut_gnmi_stub,
                                           /*timeout=*/absl::Seconds(60)));
  interfaces_map.erase(port.port_name);
  for (const auto& p : interfaces_map) allow_list.push_back(p.first);

  ASSERT_OK_AND_ASSIGN(auto port_in_use,
                       GetRandomPortWithSupportedBreakoutModes(
                           *sut_gnmi_stub, platform_json_contents,
                           BreakoutType::kAny, BreakoutType::kAny, allow_list));
  BreakoutDuringPortInUse(sut, sut_gnmi_stub.get(), port,
                          platform_json_contents, port_in_use.port_name,
                          p4_info,
                          /*expect_breakout_failure=*/false);
}
}  // namespace pins_test
