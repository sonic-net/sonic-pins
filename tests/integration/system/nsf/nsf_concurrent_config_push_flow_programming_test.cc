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
#include "tests/integration/system/nsf/nsf_concurrent_config_push_flow_programming_test.h"

#include <memory>
#include <string>
#include <thread>
#include <vector>

#include "absl/random/random.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "lib/gnmi/gnmi_helper.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "tests/integration/system/nsf/compare_p4flows.h"
#include "tests/integration/system/nsf/interfaces/image_config_params.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "tests/integration/system/nsf/util.h"
#include "thinkit/switch.h"
#include "thinkit/test_environment.h"

namespace pins_test {
using ::p4::v1::ReadResponse;

constexpr int kIsolatedLacpSystemPriority = 512;
// Here is the criteria for the NSF delay duration window:
// 1. ACL flows used in the test takes ~1s to get programmed. Hence the minimum
//    delay is set to 1s.
// 2. Config push takes ~10s to complete. Hence the maximum delay is set to 15s.
// In future, if the config or the flows are modified, consider calculating the
// time needed for both and set the NSF delay duration window accordingly.
constexpr int kMinNsfDelayDuration = 1;
constexpr int kMaxNsfDelayDuration = 15;
constexpr absl::Duration kTurnUpTimeout = absl::Minutes(6);
constexpr char kInterfaceToRemove[] = "Ethernet1/10/1";

void NsfConcurrentConfigPushFlowProgrammingTestFixture::SetUp() {
  flow_programmer_ = GetParam().create_flow_programmer();
  traffic_helper_ = GetParam().create_traffic_helper();
  testbed_interface_ = GetParam().create_testbed_interface();
  component_validators_ = GetParam().create_component_validators();
  ssh_client_ = GetParam().create_ssh_client();
  SetupTestbed(testbed_interface_);
  ASSERT_OK_AND_ASSIGN(testbed_, GetTestbed(testbed_interface_));
}
void NsfConcurrentConfigPushFlowProgrammingTestFixture::TearDown() {
  if (!GetParam().image_config_params.empty()) {
    LOG(INFO) << "Restoring the original config";
    ASSERT_OK(PushConfig(GetParam().image_config_params[0], GetSut(testbed_),
                         *ssh_client_));
    ASSERT_OK(WaitForSwitchState(GetSut(testbed_), SwitchState::kReady,
                                 kTurnUpTimeout, *ssh_client_,
                                 GetConnectedInterfacesForSut(testbed_)));
  }
  TearDownTestbed(testbed_interface_);
}

TEST_P(NsfConcurrentConfigPushFlowProgrammingTestFixture,
       NsfConcurrentConfigPushFlowProgrammingTest) {
  thinkit::TestEnvironment &environment = GetTestEnvironment(testbed_);

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
  ASSERT_OK(SaveP4FlowSnapshot(p4flow_snapshot1,
                               "p4flow_snapshot1_before_programming_flows.txt",
                               environment));

  // Program all the flows.
  LOG(INFO) << "Programming L3 flows before starting the traffic";
  ASSERT_OK(flow_programmer_->ProgramFlows(image_config_param, testbed_,
                                           *ssh_client_));
  LOG(INFO) << "Starting the traffic";
  ASSERT_OK(traffic_helper_->StartTraffic(testbed_));
  // Modifying existing config.
  // Creating a copy.
  ImageConfigParams modified_image_config_param = image_config_param;
  ASSERT_OK(environment.StoreTestArtifact("original_gnmi_config.json",
                                          image_config_param.gnmi_config));
  ASSERT_OK(environment.StoreTestArtifact(
      "modified_gnmi_config.json", modified_image_config_param.gnmi_config));

  ASSERT_OK(StoreSutDebugArtifacts(
      absl::StrCat(
          "before_nsf_reboot_",
          absl::FormatTime("%H_%M_%S", absl::Now(), absl::LocalTimeZone())),
      sut, environment));
  absl::BitGen gen;
  int nsf_delay_duration = absl::uniform_int_distribution<int>(
      kMinNsfDelayDuration, kMaxNsfDelayDuration)(gen);

  // Config Push thread.
  absl::Status config_push_status = absl::UnknownError("Yet to push config");
  auto config_push_func = [&sut,
                           &modified_image_config_param]() -> absl::Status {
    LOG(INFO) << "Pushing modified config on " << sut.ChassisName();
    RETURN_IF_ERROR(
        PushGnmiConfig(sut, modified_image_config_param.gnmi_config));
    LOG(INFO) << "Successfully pushed modified config on " << sut.ChassisName();
    return absl::OkStatus();
  };
  std::thread config_push_thread(
      [&]() { config_push_status = config_push_func(); });

  // Flow Programming thread.
  absl::Status flow_programming_status =
      absl::UnknownError("Yet to program flows");
  auto flow_programming_func = [&sut, &image_config_param]() -> absl::Status {
    LOG(INFO) << "Programming ACL flows";
    RETURN_IF_ERROR(ProgramAclFlows(sut, image_config_param.p4_info));
    LOG(INFO) << "Successfully programmed ACL flows on " << sut.ChassisName();
    return absl::OkStatus();
  };
  std::thread flow_programming_thread(
      [&]() { flow_programming_status = flow_programming_func(); });

  // NSF Reboot thread.
  absl::Status nsf_reboot_status = absl::UnknownError("Yet to do nsf reboot");
  ReadResponse p4flow_snapshot2;
  auto nsf_reboot_func = [&nsf_delay_duration, &sut, &environment,
                          &p4flow_snapshot2]() -> absl::Status {
    // Sleeping for few seconds before joining NSF thread. This is to make sure
    // config push and flow programming are initiated before NSF.
    LOG(INFO) << "Sleeping for " << nsf_delay_duration
              << " seconds before triggering NSF reboot";
    absl::SleepFor(absl::Seconds(nsf_delay_duration));
    // P4 snapshot before NSF reboot.
    LOG(INFO) << "Capturing P4 snapshot before NSF reboot";
    ASSIGN_OR_RETURN(p4flow_snapshot2, TakeP4FlowSnapshot(sut));
    LOG(INFO) << "Initiating NSF reboot";
    // Using generic Reboot helper instead of Nsf specific helper as that has an
    // initial delay to collect the debug artifacts. The below call will trigger
    // NSF reboot immediately.
    RETURN_IF_ERROR(
        pins_test::Reboot(gnoi::system::RebootMethod::NSF, sut, environment,
                          /*collect_debug_artifacts_before_reboot=*/false));
    LOG(INFO) << "Successfully triggered NSF reboot on " << sut.ChassisName();
    return absl::OkStatus();
  };
  std::thread nsf_reboot_thread(
      [&]() { nsf_reboot_status = nsf_reboot_func(); });

  // Joining all threads.
  config_push_thread.join();
  flow_programming_thread.join();
  nsf_reboot_thread.join();
  // Calling the SaveP4FlowSnapshot function after the NSF reboot thread is
  // joined. This is to avoid the delay that might get introduced by the
  // SaveP4FlowSnapshot function before the NSF reboot.
  EXPECT_OK(SaveP4FlowSnapshot(p4flow_snapshot2,
                               "p4flow_snapshot2_before_nsf.txt", environment));
  EXPECT_OK(config_push_status) << "Failed to push config";
  EXPECT_OK(flow_programming_status) << "Failed to program flows";
  ASSERT_OK(nsf_reboot_status) << "Failed to initiate NSF reboot";
  ASSERT_OK(
      WaitForNsfReboot(testbed_, *ssh_client_, &modified_image_config_param));

  // P4 snapshot after upgrade and NSF reboot.
  LOG(INFO) << "Capturing P4 snapshot after NSF reboot";
  ASSERT_OK_AND_ASSIGN(ReadResponse p4flow_snapshot3, TakeP4FlowSnapshot(sut));
  ASSERT_OK(SaveP4FlowSnapshot(p4flow_snapshot3,
                               "p4flow_snapshot3_after_nsf.txt", environment));

  // Stop and validate traffic
  LOG(INFO) << "Stopping the traffic";
  ASSERT_OK(traffic_helper_->StopTraffic(testbed_));

  // TODO: For now, we validate traffic only after stopping
  // traffic. Ideally we would want to validate traffic while injection is in
  // progress to narrow down when the traffic loss occurred (i.e. before
  // reboot, during reboot or after reconciliation).
  LOG(INFO) << "Validating the traffic";
  ASSERT_OK(traffic_helper_->ValidateTraffic(testbed_));

  LOG(INFO) << "Clearing the flows";
  ASSERT_OK(flow_programmer_->ClearFlows(testbed_));

  // P4 snapshot after clearing flows.
  LOG(INFO) << "Capturing P4 snapshot after clearing flows";
  ASSERT_OK_AND_ASSIGN(ReadResponse p4flow_snapshot4, TakeP4FlowSnapshot(sut));
  ASSERT_OK(SaveP4FlowSnapshot(p4flow_snapshot4,
                               "p4flow_snapshot4_after_clearing_flows.txt",
                               environment));

  LOG(INFO) << "Comparing P4 snapshots - Before Programming Flows Vs After "
               "Clearing Flows";
  EXPECT_OK(CompareP4FlowSnapshots(p4flow_snapshot1, p4flow_snapshot4));

  LOG(INFO) << "Comparing P4 snapshots - Before Vs. After NSF Reboot";
  ASSERT_OK(CompareP4FlowSnapshots(p4flow_snapshot2, p4flow_snapshot3));
}
}  // namespace pins_test
