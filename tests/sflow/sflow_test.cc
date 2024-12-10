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

#include "tests/sflow/sflow_test.h"

#include <cmath>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/synchronization/mutex.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/ixia_helper.h"
#include "lib/validator/validator_lib.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/pd.h"
#include "p4_pdpi/string_encodings/decimal_string.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/mirror_testbed_fixture.h"
#include "thinkit/ssh_client.h"

namespace pins {

namespace {
constexpr absl::string_view kSpeed100GB =
    "\"openconfig-if-ethernet:SPEED_100GB\"";
constexpr absl::string_view kSpeed200GB =
    "\"openconfig-if-ethernet:SPEED_200GB\"";

// Set port speed by configuraing interface/ethernet/config/port-speed value.
absl::Status SetPortSpeed(absl::string_view port_speed, absl::string_view iface,
                          gnmi::gNMI::StubInterface& gnmi_stub) {
  std::string ops_config_path = absl::StrCat(
      "interfaces/interface[name=", iface, "]/ethernet/config/port-speed");
  std::string ops_val =
      absl::StrCat("{\"openconfig-if-ethernet:port-speed\":", port_speed, "}");

  RETURN_IF_ERROR(pins_test::SetGnmiConfigPath(
      &gnmi_stub, ops_config_path, pins_test::GnmiSetType::kUpdate, ops_val));

  return absl::OkStatus();
}

// Get port speed by reading interface/ethernet/state/port-speed path.
absl::StatusOr<std::string> GetPortSpeed(absl::string_view iface,
                                         gnmi::gNMI::StubInterface* gnmi_stub) {
  std::string ops_state_path = absl::StrCat("interfaces/interface[name=", iface,
                                            "]/ethernet/state/port-speed");

  std::string ops_parse_str = "openconfig-if-ethernet:port-speed";
  return pins_test::GetGnmiStatePathInfo(gnmi_stub, ops_state_path,
                                         ops_parse_str);
}

// Check interface/state/oper-status value to validate if link is up.
absl::StatusOr<bool> CheckLinkUp(absl::string_view interface,
                                 gnmi::gNMI::StubInterface& gnmi_stub) {
  std::string oper_status_state_path = absl::StrCat(
      "interfaces/interface[name=", interface, "]/state/oper-status");

  std::string parse_str = "openconfig-interfaces:oper-status";
  ASSIGN_OR_RETURN(std::string ops_response,
                   pins_test::GetGnmiStatePathInfo(
                       &gnmi_stub, oper_status_state_path, parse_str));

  return ops_response == "\"UP\"";
}

// Returns a vector of SUT interfaces that are connected to Ixia and up.
absl::StatusOr<std::vector<IxiaLink>> GetIxiaConnectedUpLinks(
    thinkit::GenericTestbed& generic_testbed,
    gnmi::gNMI::StubInterface& gnmi_stub) {
  std::vector<IxiaLink> ixia_links;

  absl::flat_hash_map<std::string, thinkit::InterfaceInfo> interface_info =
      generic_testbed.GetSutInterfaceInfo();
  absl::flat_hash_map<std::string, std::string> port_id_per_port_name;
  ASSIGN_OR_RETURN(port_id_per_port_name,
                   pins_test::GetAllInterfaceNameToPortId(gnmi_stub));
  // Loop through the interface_info looking for Ixia/SUT interface pairs,
  // checking if the link is up.  Add the pair to connections.
  for (const auto& [interface, info] : interface_info) {
    if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR)) {
      ASSIGN_OR_RETURN(bool sut_link_up, CheckLinkUp(interface, gnmi_stub));
      auto port_id = gutil::FindOrNull(port_id_per_port_name, interface);
      EXPECT_NE(port_id, nullptr) << absl::Substitute(
          "No corresponding p4rt id for interface $0", interface);
      if (sut_link_up) {
        LOG(INFO) << "Ixia interface:" << info.peer_interface_name
                  << ". Sut interface:" << interface << ". Port id:"
                  << *port_id;
        ixia_links.push_back(IxiaLink{
            .ixia_interface = info.peer_interface_name,
            .sut_interface = interface,
            .port_id = std::stoi(*port_id),
        });
      }
    }
  }

  return ixia_links;
}

}  // namespace

void SflowTestFixture::SetUp() {
  // Pick a testbed with an Ixia Traffic Generator.
  auto requirements =
      gutil::ParseProtoOrDie<thinkit::TestRequirements>(
          R"pb(interface_requirements {
                 count: 1
                 interface_modes: TRAFFIC_GENERATOR
               })pb");

  ASSERT_OK_AND_ASSIGN(
      testbed_,
      GetParam().testbed_interface->GetTestbedWithRequirements(requirements));

  const std::string gnmi_config = GetParam().gnmi_config;
  ASSERT_OK(testbed_->Environment().StoreTestArtifact("gnmi_config.txt",
                                                      gnmi_config));
  ASSERT_OK(testbed_->Environment().StoreTestArtifact(
      "p4info.pb.txt", GetP4Info().DebugString()));
  ASSERT_OK_AND_ASSIGN(sut_p4_session_,
                       pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
                           testbed_->Sut(), gnmi_config, GetP4Info()));
  ASSERT_OK_AND_ASSIGN(ir_p4_info_, pdpi::CreateIrP4Info(GetP4Info()));

  ASSERT_OK_AND_ASSIGN(gnmi_stub_, testbed_->Sut().CreateGnmiStub());
  // Go through all the ports that connect to the Ixia and set them
  // first to 200GB.
  absl::flat_hash_map<std::string, thinkit::InterfaceInfo> interface_info =
      testbed_->GetSutInterfaceInfo();
  for (const auto& [interface, info] : interface_info) {
    if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR)) {
      ASSERT_OK(SetPortSpeed(kSpeed200GB, interface, *gnmi_stub_));
    }
  }

  auto speed_config_applied =
      [&interface_info](absl::string_view expected_speed,
                        gnmi::gNMI::StubInterface* gnmi_stub) -> absl::Status {
    for (const auto& [interface, info] : interface_info) {
     if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR)) {
        ASSIGN_OR_RETURN(auto port_speed, GetPortSpeed(interface, gnmi_stub));
        if (port_speed != expected_speed) {
          return absl::FailedPreconditionError(absl::Substitute(
              "Port speed is not converged. Interface $0 "
              "speed state path value is $1, expected speed is $2.",
              interface, port_speed, expected_speed));
        }
      }
    }
    return absl::OkStatus();
  };

  // Wait to let the links come up. Switch guarantees state paths to reflect
  // in 10s. Lets wait for a bit more.
  EXPECT_OK(pins_test::WaitForCondition(speed_config_applied, absl::Seconds(30),
                                        kSpeed200GB, gnmi_stub_.get()));

  ASSERT_OK_AND_ASSIGN(ready_links_,
                       GetIxiaConnectedUpLinks(*testbed_, *gnmi_stub_));

  // If links didn't come, lets try 100GB as some testbeds have 100GB
  // IXIA connections.
  if (ready_links_.empty()) {
    for (const auto& [interface, info] : interface_info) {
     if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR)) {
        ASSERT_OK(SetPortSpeed(kSpeed100GB, interface, *gnmi_stub_));
      }
    }
    // Wait to let the links come up. Switch guarantees state paths to reflect
    // in 10s. Lets wait for a bit more.
    EXPECT_OK(pins_test::WaitForCondition(speed_config_applied,
                                          absl::Seconds(30), kSpeed100GB,
                                          gnmi_stub_.get()));
    ASSERT_OK_AND_ASSIGN(ready_links_,
                         GetIxiaConnectedUpLinks(*testbed_, *gnmi_stub_));
  }
  ASSERT_FALSE(ready_links_.empty()) << "Ixia links are not ready";
}

void SflowTestFixture::TearDown() {
  // Clear table entries and stop RPC sessions.
  LOG(INFO) << "\n------ TearDown START ------\n";
  if (sut_p4_session_ != nullptr) {
    EXPECT_OK(sut_p4_session_->Finish());
  }
  GetParam().testbed_interface->TearDown();
  if (ssh_client_ != nullptr) {
    delete ssh_client_;
    ssh_client_ = nullptr;
  }
  if (GetParam().testbed_interface != nullptr) {
    delete GetParam().testbed_interface;
  }
  LOG(INFO) << "\n------ TearDown END ------\n";
}

}  // namespace pins
