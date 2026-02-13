// Copyright 2025 Google LLC
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

#ifndef PINS_TESTS_GNOI_BERT_TESTS_H_
#define PINS_TESTS_GNOI_BERT_TESTS_H_

#include <memory>
#include <string>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "diag/diag.grpc.pb.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "thinkit/control_device.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/generic_testbed_fixture.h"
#include "thinkit/ssh_client.h"

namespace bert {

struct BertTestParams {
  thinkit::GenericTestbedInterface *testbed_interface;
  std::string gnmi_config;
  p4::config::v1::P4Info p4_info;
  thinkit::SSHClient *ssh_client;
  bool nsf_supported;
};

class BertTest : public ::testing::TestWithParam<BertTestParams> {
public:
  BertTest()
      : generic_testbed_(nullptr), sut_gnmi_stub_(nullptr),
        sut_diag_stub_(nullptr) {}

  void SetUp() override {
    GetParam().testbed_interface->SetUp();
    GetParam().testbed_interface->ExpectLinkFlaps();
    LOG(INFO) << "SetUp complete";
  }

  void TearDown() override {
    if (GetParam().ssh_client != nullptr) {
      delete GetParam().ssh_client;
    }

    if (GetParam().testbed_interface != nullptr) {
      GetParam().testbed_interface->TearDown();
      delete GetParam().testbed_interface;
    }
    LOG(INFO) << "TearDown complete";
  }

  void InitializeTestEnvironment(absl::string_view test_id) {
    thinkit::TestRequirements requirements =
        gutil::ParseProtoOrDie<thinkit::TestRequirements>(
            R"pb(interface_requirements {
                   count: 1
                   interface_mode: CONTROL_INTERFACE
                 })pb");

    ASSERT_OK_AND_ASSIGN(
        generic_testbed_,
        GetParam().testbed_interface->GetTestbedWithRequirements(requirements));

    absl::flat_hash_map<std::string, thinkit::InterfaceInfo> interface_info =
        generic_testbed_->GetSutInterfaceInfo();

    ASSERT_OK_AND_ASSIGN(sut_gnmi_stub_,
                         generic_testbed_->Sut().CreateGnmiStub());
    ASSERT_OK_AND_ASSIGN(sut_diag_stub_,
                         generic_testbed_->Sut().CreateGnoiDiagStub());

    absl::flat_hash_set<std::string> model_sut_interfaces;
    absl::flat_hash_set<std::string> model_peer_interfaces;
    for (const auto &[interface, info] : interface_info) {
      if (info.interface_modes.contains(thinkit::CONTROL_INTERFACE)) {
        model_sut_interfaces.insert(interface);
        model_peer_interfaces.insert(info.peer_interface_name);
      }
    }
    ASSERT_OK_AND_ASSIGN(auto sut_interface_to_lane_speed,
                         pins_test::GetInterfaceToLaneSpeedMap(
                             *sut_gnmi_stub_, model_sut_interfaces));

    thinkit::ControlDevice &control_device = generic_testbed_->ControlDevice();
    bool check_control_switch = false;
    absl::flat_hash_map<std::string, int> control_interface_to_lane_speed;

    absl::StatusOr<absl::flat_hash_map<std::string, int>> statusor =
        control_device.GetInterfaceLaneSpeed(model_peer_interfaces);
    if (statusor.ok()) {
      check_control_switch = true;
      control_interface_to_lane_speed = statusor.value();
    } else {
      // ASSERT if there was an error in getting the lane speed if API to get
      // the lane speed is implemented.
      ASSERT_EQ(statusor.status().code(), absl::StatusCode::kUnimplemented);
    }

    for (const auto &[interface, info] : interface_info) {
      if (info.interface_modes.contains(thinkit::CONTROL_INTERFACE)) {
        if (!pins_test::InterfaceSupportsBert(interface,
                                              sut_interface_to_lane_speed)) {
          continue;
        }
        if (check_control_switch &&
            (pins_test::InterfaceSupportsBert(
                 info.peer_interface_name, control_interface_to_lane_speed) ==
             false)) {
          continue;
        }

        sut_interfaces_.push_back(interface);
        peer_interfaces_.push_back(info.peer_interface_name);
        sut_to_peer_interface_mapping_[interface] = info.peer_interface_name;
        control_to_peer_interface_mapping_[info.peer_interface_name] =
            interface;
      }
    }
  }

  absl::StatusOr<std::vector<std::string>> GetPeerInterfacesForSutInterfaces(
      const std::vector<std::string> &sut_interfaces) {
    std::vector<std::string> peer_interfaces;
    peer_interfaces.reserve(sut_interfaces.size());
    for (const std::string &sut_interface : sut_interfaces) {
      if (sut_to_peer_interface_mapping_.count(sut_interface) == 0) {
        return absl::NotFoundError(absl::Substitute(
            "Failed to find peer for SUT interface $0", sut_interface));
      }
      peer_interfaces.push_back(sut_to_peer_interface_mapping_[sut_interface]);
    }
    return peer_interfaces;
  }

  absl::StatusOr<std::vector<std::string>> GetSutInterfacesForControlInterfaces(
      const std::vector<std::string> &control_interfaces) {
    std::vector<std::string> sut_interfaces;
    sut_interfaces.reserve(control_interfaces.size());
    for (const std::string &control_interface : control_interfaces) {
      if (control_to_peer_interface_mapping_.count(control_interface) == 0) {
        return absl::NotFoundError("Failed to find peer.");
      }
      sut_interfaces.push_back(
          control_to_peer_interface_mapping_[control_interface]);
    }
    return sut_interfaces;
  }

 protected:
  std::unique_ptr<thinkit::GenericTestbed> generic_testbed_;
  std::unique_ptr<gnmi::gNMI::StubInterface> sut_gnmi_stub_;
  std::unique_ptr<gnoi::diag::Diag::StubInterface> sut_diag_stub_;
  // List of SUT interfaces.
  std::vector<std::string> sut_interfaces_;
  // List of control switch interfaces.
  std::vector<std::string> peer_interfaces_;
  // List of SUT interfaces that are under test.
  std::vector<std::string> sut_test_interfaces_;
  // List of control switch interfaces that are under test.
  std::vector<std::string> peer_test_interfaces_;
  // A mapping of SUT interface and its peer interface on control switch.
  absl::flat_hash_map<std::string, std::string> sut_to_peer_interface_mapping_;
  // A mapping of control switch interface and its peer interface on SUT.
  absl::flat_hash_map<std::string, std::string>
      control_to_peer_interface_mapping_;
};

}  // namespace bert

#endif  // PINS_TESTS_GNOI_BERT_TESTS_H_
