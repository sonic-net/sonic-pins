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
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "glog/logging.h"
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

}  // namespace

void BreakoutDuringPortInUse(thinkit::Switch& sut,
                             gnmi::gNMI::StubInterface* sut_gnmi_stub,
                             RandomPortBreakoutInfo port_info,
                             const std::string& platform_json_contents,
                             bool test_child_port_in_use) {
  // Get the original breakout info on the port.
  // This contains the state values of physical channels and
  // operational status information for ports in original breakout mode.
  ASSERT_OK_AND_ASSIGN(
      auto orig_breakout_info,
      GetBreakoutStateInfoForPort(sut_gnmi_stub, port_info.port_name,
                                  port_info.curr_breakout_mode));

  // Verify that all ports for the selected port are operationally up.
  auto resp_parse_str = "openconfig-interfaces:oper-status";
  for (const auto& p : orig_breakout_info) {
    auto if_state_path = absl::StrCat("interfaces/interface[name=", p.first,
                                      "]/state/oper-status");
    ASSERT_OK_AND_ASSIGN(
        auto state_path_response,
        GetGnmiStatePathInfo(sut_gnmi_stub, if_state_path, resp_parse_str));
    EXPECT_THAT(state_path_response, HasSubstr(kStateUp));
  }

  // Determine port to install router interface on.
  auto in_use_port = port_info.port_name;
  if (test_child_port_in_use) {
    for (const auto& p : orig_breakout_info) {
      if (p.first != port_info.port_name) {
        in_use_port = p.first;
        break;
      }
    }
    ASSERT_NE(in_use_port, port_info.port_name);
  }

  // Get the p4rt port index of the port on which to install router interface.
  ASSERT_OK_AND_ASSIGN(auto port_id_by_interface,
                       GetAllInterfaceNameToPortId(*sut_gnmi_stub));
  ASSERT_OK_AND_ASSIGN(std::string in_use_port_index_value,
                       gutil::FindOrStatus(port_id_by_interface, in_use_port));
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
                set_port_and_src_mac { port: "$0" src_mac: "02:2a:10:00:00:03" }
              }
            }
          )pb",
          in_use_port_index));
  ASSERT_OK(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      sut_p4_session.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      sai::GetP4Info(sai::Instantiation::kMiddleblock)))
      << "SetForwardingPipelineConfig: Failed to push P4Info: ";
  ASSERT_OK(pdpi::ClearTableEntries(sut_p4_session.get()));

  p4::config::v1::P4Info p4info =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);
  ASSERT_OK_AND_ASSIGN(auto ir_p4info, pdpi::CreateIrP4Info(p4info));
  ASSERT_OK_AND_ASSIGN(const p4::v1::TableEntry pi_entry,
                       pdpi::PartialPdTableEntryToPiTableEntry(pdpi::IrP4Info(), pd_entry));

  LOG(INFO) << "Installing router interface on port " << in_use_port
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

  // Apply breakout config on port. Expect the set operation to fail
  // since the port/its child is in use.
  LOG(INFO) << "Configuring breakout mode " << port_info.supported_breakout_mode
            << " on port " << port_info.port_name << " on DUT";
  auto status = sut_gnmi_stub->Set(&context, req, &resp);
  ASSERT_NE(status.ok(), true);
  EXPECT_THAT(status.error_message(),
              HasSubstr(absl::StrCat(
                  "SET failed: YangToDb_port_breakout_subtree_xfmr: port ",
                  in_use_port, " is in use")));

  // Get expected port information for new breakout mode.
  ASSERT_OK_AND_ASSIGN(
      auto new_breakout_info,
      GetExpectedPortInfoForBreakoutMode(port_info.port_name,
                                         port_info.supported_breakout_mode));
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
  ASSERT_EQ(status.ok(), true);

  // Wait for breakout config to go through.
  absl::SleepFor(absl::Seconds(30));

  // Verify that the config is successfully applied now.
  non_existing_port_list = GetNonExistingPortsAfterBreakout(
      orig_breakout_info, new_breakout_info, true);
  ASSERT_OK(ValidateBreakoutState(sut_gnmi_stub, new_breakout_info,
                                  non_existing_port_list));

  // Restore original port breakout config on port under test.
  ASSERT_OK(GetBreakoutModeConfigFromString(req, sut_gnmi_stub, port_index,
                                            port_info.port_name,
                                            port_info.curr_breakout_mode));

  LOG(INFO) << "Restoring original breakout mode "
            << port_info.curr_breakout_mode << " on port "
            << port_info.port_name << " on DUT";
  grpc::ClientContext context3;
  ASSERT_OK(sut_gnmi_stub->Set(&context3, req, &resp));
  absl::SleepFor(absl::Seconds(60));

  // Verify that the config is successfully applied.
  non_existing_port_list = GetNonExistingPortsAfterBreakout(
      orig_breakout_info, new_breakout_info, false);
  ASSERT_OK(ValidateBreakoutState(sut_gnmi_stub, orig_breakout_info,
                                  non_existing_port_list));
}

void TestGNMIParentPortInUseDuringBreakout(
    thinkit::Switch& sut, std::string& platform_json_contents) {
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());
  // Get a random port from list of front panel ports that supports at least
  // one breakout mode of required type other than its current mode.
  ASSERT_OK_AND_ASSIGN(auto port, GetRandomPortWithSupportedBreakoutModes(
                                      *sut_gnmi_stub, platform_json_contents,
                                      BreakoutType::kAny));
  BreakoutDuringPortInUse(sut, sut_gnmi_stub.get(), port,
                          platform_json_contents, false);
}

void TestGNMIChildPortInUseDuringBreakout(thinkit::Switch& sut,
                                          std::string& platform_json_contents) {
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());
  // Get a random port from list of front panel ports that supports at least
  // one breakout mode of required type other than its current mode.
  ASSERT_OK_AND_ASSIGN(auto port, GetRandomPortWithSupportedBreakoutModes(
                                      *sut_gnmi_stub, platform_json_contents,
                                      BreakoutType::kChannelized));
  BreakoutDuringPortInUse(sut, sut_gnmi_stub.get(), port,
                          platform_json_contents, true);
}
}  // namespace pins_test
