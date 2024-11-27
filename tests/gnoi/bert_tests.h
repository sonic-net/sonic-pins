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

#ifndef PINS_TESTS_GNOI_BERT_TESTS_H_
#define PINS_TESTS_GNOI_BERT_TESTS_H_

#include "absl/strings/substitute.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "thinkit/generic_testbed_fixture.h"

namespace bert {

class BertTest : public thinkit::GenericTestbedFixture<> {
 public:
  BertTest()
      : generic_testbed_(nullptr),
        sut_gnmi_stub_(nullptr),
        sut_diag_stub_(nullptr) {}

  void InitializeTestEnvironment(absl::string_view test_id) {
    thinkit::TestRequirements requirements =
        gutil::ParseProtoOrDie<thinkit::TestRequirements>(
            R"pb(interface_requirements {
                   count: 1
                   interface_mode: CONTROL_INTERFACE
                 })pb");

    ASSERT_OK_AND_ASSIGN(generic_testbed_,
                         GetTestbedWithRequirements(requirements));
    generic_testbed_->Environment().SetTestCaseID(test_id);

    absl::flat_hash_map<std::string, thinkit::InterfaceInfo> interface_info =
        generic_testbed_->GetSutInterfaceInfo();

    for (const auto &[interface, info] : interface_info) {
      if ((info.interface_modes.contains(thinkit::CONTROL_INTERFACE)) == thinkit::CONTROL_INTERFACE) {
        sut_interfaces_.push_back(interface);
        peer_interfaces_.push_back(info.peer_interface_name);
        sut_to_peer_interface_mapping_[interface] = info.peer_interface_name;
      }
    }

    ASSERT_OK_AND_ASSIGN(sut_gnmi_stub_,
                         generic_testbed_->Sut().CreateGnmiStub());
    ASSERT_OK_AND_ASSIGN(sut_diag_stub_,
                         generic_testbed_->Sut().CreateGnoiDiagStub());
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
};

}  // namespace bert

#endif  // PINS_TESTS_GNOI_BERT_TESTS_H_
