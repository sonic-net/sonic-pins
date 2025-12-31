// Copyright 2025 Google LLC
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
#include "tests/integration/system/nsf/nsf_acl_flow_coverage_test.h"

#include <memory>
#include <vector>

#include "absl/log/log.h"
#include "absl/strings/str_cat.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "tests/integration/system/nsf/compare_p4flows.h"
#include "tests/integration/system/nsf/interfaces/image_config_params.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "tests/integration/system/nsf/util.h"
#include "thinkit/switch.h"
#include "thinkit/test_environment.h"

namespace pins_test {

using ::p4::v1::ReadResponse;

void NsfAclFlowCoverageTestFixture::SetUp() {
  flow_programmer_ = GetParam().create_flow_programmer();
  traffic_helper_ = GetParam().create_traffic_helper();
  testbed_interface_ = GetParam().create_testbed_interface();
  component_validators_ = GetParam().create_component_validators();
  ssh_client_ = GetParam().create_ssh_client();
  SetupTestbed(testbed_interface_);
  ASSERT_OK_AND_ASSIGN(testbed_, GetTestbed(testbed_interface_));
}
void NsfAclFlowCoverageTestFixture::TearDown() {
  TearDownTestbed(testbed_interface_);
}

TEST_P(NsfAclFlowCoverageTestFixture, NsfAclFlowCoverageTest) {
  thinkit::TestEnvironment& environment = GetTestEnvironment(testbed_);
  // The test needs at least 1 image_config_param to run.
  if (GetParam().image_config_params.empty()) {
    GTEST_SKIP() << "No image config params provided";
  }
  // Pick the first image config param.
  ImageConfigParams image_config_param = GetParam().image_config_params[0];
  thinkit::Switch& sut = GetSut(testbed_);

  LOG(INFO) << "Clearing the flows before the start of the test";
  ASSERT_OK(flow_programmer_->ClearFlows(testbed_));

  ASSERT_OK(ValidateTestbedState(testbed_, *ssh_client_, &image_config_param));

  // P4 snapshot before programming flows and starting the traffic.
  LOG(INFO) << "Capturing P4 snapshot before programming flows and starting "
               "the traffic";
  ASSERT_OK_AND_ASSIGN(ReadResponse p4flow_snapshot1, TakeP4FlowSnapshot(sut));
  ASSERT_OK(SaveP4FlowSnapshot(
      p4flow_snapshot1,
      absl::StrCat(sut.ChassisName(),
                   "p4flow_snapshot1_before_programming_flows.txt"),
      environment));

  // Program all the flows.
  LOG(INFO) << "Programming L3 flows before starting the traffic";
  ASSERT_OK(flow_programmer_->ProgramFlows(image_config_param, testbed_,
                                           *ssh_client_));
  LOG(INFO) << "Programming ACL flows";
  ASSERT_OK(ProgramAclFlows(sut, image_config_param.p4_info,
                            GetParam().sut_instantiation));

  LOG(INFO) << "Starting the traffic";
  ASSERT_OK(traffic_helper_->StartTraffic(testbed_));

  // P4 snapshot before NSF reboot.
  LOG(INFO) << "Capturing P4 snapshot before NSF reboot";
  ASSERT_OK_AND_ASSIGN(ReadResponse p4flow_snapshot2, TakeP4FlowSnapshot(sut));
  ASSERT_OK(SaveP4FlowSnapshot(
      p4flow_snapshot2,
      absl::StrCat(sut.ChassisName(), "p4flow_snapshot2_before_nsf.txt"),
      environment));

  ASSERT_OK(DoNsfRebootAndWaitForSwitchReadyOrRecover(testbed_, *ssh_client_,
                                                      &image_config_param));

  // P4 snapshot after upgrade and NSF reboot.
  LOG(INFO) << "Capturing P4 snapshot after NSF reboot";
  ASSERT_OK_AND_ASSIGN(ReadResponse p4flow_snapshot3, TakeP4FlowSnapshot(sut));
  ASSERT_OK(SaveP4FlowSnapshot(
      p4flow_snapshot3,
      absl::StrCat(sut.ChassisName(), "p4flow_snapshot3_after_nsf.txt"),
      environment));

  // Stop and validate traffic
  LOG(INFO) << "Stopping the traffic";
  ASSERT_OK(traffic_helper_->StopTraffic(testbed_));

  // TODO: For now, we validate traffic only after stopping
  // traffic. Ideally we would want to validate traffic while injection is in
  // progress to narrow down when the traffic loss occurred (i.e. before
  // reboot, during reboot or after reconciliation).
  LOG(INFO) << "Validating the traffic";
  ASSERT_OK(traffic_helper_->ValidateTraffic(testbed_));

  // Selectively clear flows (eg. not clearing nexthop entries for host
  // testbeds).
  LOG(INFO) << "Clearing the flows";
  ASSERT_OK(flow_programmer_->ClearFlows(testbed_));

  // P4 snapshot after cleaning up flows.
  LOG(INFO) << "Capturing P4 snapshot after cleaning up flows";
  ASSERT_OK_AND_ASSIGN(ReadResponse p4flow_snapshot4, TakeP4FlowSnapshot(sut));
  ASSERT_OK(SaveP4FlowSnapshot(
      p4flow_snapshot4,
      absl::StrCat(sut.ChassisName(),
                   "p4flow_snapshot4_after_clearing_flows.txt"),
      environment));

  LOG(INFO) << "Comparing P4 snapshots - Before Programming Flows Vs After "
               "Clearing Flows";
  ASSERT_OK(CompareP4FlowSnapshots(p4flow_snapshot1, p4flow_snapshot4));

  LOG(INFO)
      << "Comparing P4 snapshots - Before NSF Reboot Vs. After NSF Reboot";
  ASSERT_OK(CompareP4FlowSnapshots(p4flow_snapshot2, p4flow_snapshot3));
}
}  // namespace pins_test
