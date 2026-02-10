// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#ifndef PINS_TESTS_INTEGRATION_SYSTEM_ALPM_MISS_COUNTER_TESTS_H_
#define PINS_TESTS_INTEGRATION_SYSTEM_ALPM_MISS_COUNTER_TESTS_H_

#include <memory>
#include <string>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/log/log.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/generic_testbed_fixture.h"
#include "thinkit/switch.h"

namespace pins_test {

struct AlpmMissCountersTestParams {
  thinkit::GenericTestbedInterface *testbed_interface;
  std::string gnmi_config;
  p4::config::v1::P4Info p4_info;
  bool not_supported;
};

struct AlpmRouteParams {
  std::string neighbor_id;
  std::string vrf;
  std::string rif;
  std::string nexthop;
  std::string p4_port_id;
};

class AlpmMissCountersTest
    : public ::testing::TestWithParam<AlpmMissCountersTestParams> {
public:
  AlpmMissCountersTest() : generic_testbed_(nullptr), sut_gnmi_stub_(nullptr) {}

  void SetUp() override {
    GetParam().testbed_interface->SetUp();
    LOG(INFO) << "SetUp complete";
  }

  void TearDown() override {
    if (GetParam().testbed_interface != nullptr) {
      GetParam().testbed_interface->TearDown();
      delete GetParam().testbed_interface;
    }
    LOG(INFO) << "Tear down complete";
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
    generic_testbed_->Environment().SetTestCaseID(test_id);

    absl::flat_hash_map<std::string, thinkit::InterfaceInfo> interface_info =
        generic_testbed_->GetSutInterfaceInfo();

    ASSERT_OK_AND_ASSIGN(sut_gnmi_stub_,
                         generic_testbed_->Sut().CreateGnmiStub());

    for (const auto &[interface, info] : interface_info) {
      if (info.interface_modes.contains(thinkit::CONTROL_INTERFACE)) {
        sut_interfaces_.push_back(interface);
        peer_interfaces_.push_back(info.peer_interface_name);
        sut_to_peer_interface_mapping_[interface] = info.peer_interface_name;
      }
    }
  }

 protected:
  std::unique_ptr<thinkit::GenericTestbed> generic_testbed_;
  std::unique_ptr<gnmi::gNMI::StubInterface> sut_gnmi_stub_;
  // List of SUT interfaces.
  std::vector<std::string> sut_interfaces_;
  // List of control switch interfaces.
  std::vector<std::string> peer_interfaces_;
  // A mapping of SUT interface and its peer interface on control switch.
  absl::flat_hash_map<std::string, std::string> sut_to_peer_interface_mapping_;
  struct AlpmRouteParams route_params_;
};

}  // namespace pins_test

#endif  // PINS_TESTS_INTEGRATION_SYSTEM_ALPM_MISS_COUNTER_TESTS_H_
