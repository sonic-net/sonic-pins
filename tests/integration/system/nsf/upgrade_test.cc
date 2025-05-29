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

#include "tests/integration/system/nsf/upgrade_test.h"

#include <memory>
#include <string>
#include <vector>

#include "absl/flags/flag.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"  // NOLINT: Need to add status_matchers.h for using `ASSERT_OK` in upstream code.
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "tests/integration/system/nsf/interfaces/component_validator.h"
#include "tests/integration/system/nsf/interfaces/flow_programmer.h"
#include "tests/integration/system/nsf/interfaces/test_params.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "tests/integration/system/nsf/interfaces/traffic_helper.h"
#include "tests/integration/system/nsf/milestone.h"
#include "tests/integration/system/nsf/util.h"
#include "thinkit/proto/generic_testbed.pb.h"

ABSL_FLAG(pins_test::NsfMilestone, milestone, pins_test::NsfMilestone::kAll,
          "The NSF milestone to test.");

namespace pins_test {

using ::p4::v1::ReadResponse;

// Since the validation is while the traffic is in progress, error margin needs
// to be defined.
constexpr int kErrorPercentage = 1;
constexpr absl::Duration kTrafficRunDuration = absl::Minutes(15);

// TODO: Compare and look into possibility of using a better
// approach than using std::variant (eg. type-erasure or typed tests).
void NsfUpgradeTest::SetUp() {
  flow_programmer_ = GetParam().create_flow_programmer();
  traffic_helper_ = GetParam().create_traffic_helper();
  testbed_interface_ = GetParam().create_testbed_interface();
  component_validators_ = GetParam().create_component_validators();
  ssh_client_ = GetParam().create_ssh_client();
  SetupTestbed(testbed_interface_);
  ASSERT_OK_AND_ASSIGN(testbed_, GetTestbed(testbed_interface_));
}
void NsfUpgradeTest::TearDown() { TearDownTestbed(testbed_interface_); }

absl::Status NsfUpgradeTest::NsfUpgradeOrReboot(
    const ImageConfigParams& curr_image_config,
    const ImageConfigParams& next_image_config) {
  LOG(INFO) << "Initiating NSF Upgrade from: " << curr_image_config.image_label
            << " to: " << next_image_config.image_label;

  RETURN_IF_ERROR(
      ValidateTestbedState(testbed_, *ssh_client_, &curr_image_config));
  RETURN_IF_ERROR(ValidateComponents(&ComponentValidator::OnInit,
                                     component_validators_,
                                     curr_image_config.image_label, testbed_));
  RETURN_IF_ERROR(StoreSutDebugArtifacts(
      absl::StrCat(curr_image_config.image_label, "_before_nsf_reboot"),
      testbed_));

  // P4 snapshot before programming flows and starting the traffic.
  LOG(INFO) << "Capturing P4 snapshot before programming flows and starting "
               "the traffic";
  ASSIGN_OR_RETURN(ReadResponse p4flow_snapshot1, TakeP4FlowSnapshot(testbed_));
  RETURN_IF_ERROR(
      SaveP4FlowSnapshot(testbed_, p4flow_snapshot1,
                         "p4flow_snapshot1_before_programming_flows.txt"));

  // Program all the flows.
  LOG(INFO) << "Programming flows before starting the traffic";
  RETURN_IF_ERROR(flow_programmer_->ProgramFlows(curr_image_config.p4_info,
                                                 testbed_, *ssh_client_));
  RETURN_IF_ERROR(ValidateComponents(&ComponentValidator::OnFlowProgram,
                                     component_validators_,
                                     curr_image_config.image_label, testbed_));

  LOG(INFO) << "Starting the traffic";
  RETURN_IF_ERROR(traffic_helper_->StartTraffic(testbed_));
  RETURN_IF_ERROR(ValidateComponents(&ComponentValidator::OnStartTraffic,
                                     component_validators_,
                                     curr_image_config.image_label, testbed_));

  // P4 snapshot before Upgrade and NSF reboot.
  LOG(INFO) << "Capturing P4 snapshot before Upgrade and NSF reboot";
  ASSIGN_OR_RETURN(ReadResponse p4flow_snapshot2, TakeP4FlowSnapshot(testbed_));
  RETURN_IF_ERROR(
      SaveP4FlowSnapshot(testbed_, p4flow_snapshot2,
                         "p4flow_snapshot2_before_upgrade_and_nsf.txt"));

  LOG(INFO) << "Starting NSF Upgrade";
  // Copy image to the switch for installation.
  ASSIGN_OR_RETURN(
      std::string image_version,
      ImageCopy(next_image_config.image_label, testbed_, *ssh_client_));
  RETURN_IF_ERROR(ValidateComponents(&ComponentValidator::OnImageCopy,
                                     component_validators_,
                                     next_image_config.image_label, testbed_));
  // TODO: Validate uptime and boot-type once they are supported.

  // Perform NSF Reboot.
  RETURN_IF_ERROR(NsfReboot(testbed_));
  RETURN_IF_ERROR(WaitForNsfReboot(testbed_, *ssh_client_));

  // Perform validations after reboot is completed.
  RETURN_IF_ERROR(
      ValidateTestbedState(testbed_, *ssh_client_, &next_image_config));
  RETURN_IF_ERROR(ValidateComponents(&ComponentValidator::OnNsfReboot,
                                     component_validators_,
                                     next_image_config.image_label, testbed_));
  RETURN_IF_ERROR(StoreSutDebugArtifacts(
      absl::StrCat(curr_image_config.image_label, "_after_nsf_reboot"),
      testbed_));

  // P4 snapshot after upgrade and NSF reboot.
  LOG(INFO) << "Capturing P4 snapshot after Upgrade and NSF reboot";
  ASSIGN_OR_RETURN(ReadResponse p4flow_snapshot3, TakeP4FlowSnapshot(testbed_));
  RETURN_IF_ERROR(
      SaveP4FlowSnapshot(testbed_, p4flow_snapshot3,
                         "p4flow_snapshot3_after_upgrade_and_nsf.txt"));

  // Push the new config and validate.
  RETURN_IF_ERROR(PushConfig(next_image_config, testbed_, *ssh_client_));
  RETURN_IF_ERROR(
      ValidateTestbedState(testbed_, *ssh_client_, &next_image_config));
  RETURN_IF_ERROR(ValidateComponents(&ComponentValidator::OnConfigPush,
                                     component_validators_,
                                     next_image_config.image_label, testbed_));

  // Wait for transmission duration.
  LOG(INFO) << "Wait for " << kTrafficRunDuration << " for transmit completion";
  absl::SleepFor(kTrafficRunDuration);

  // Stop and validate traffic
  LOG(INFO) << "Stopping the traffic";
  RETURN_IF_ERROR(traffic_helper_->StopTraffic(testbed_));

  // TODO: For now, we validate traffic only after stopping
  // traffic. Ideally we would want to validate traffic while injection is in
  // progress to narrow down when the traffic loss occurred (i.e. before reboot,
  // during reboot or after reconciliation). Although this is possible in OTG
  // traffic generator, DVaaS traffic generator for now does not support traffic
  // validation before stopping the traffic. This is a good-to-have feature and
  // we will update the skeleton to validate traffic while injection is ongoing
  // once this feature is available in DVaaS.
  LOG(INFO) << "Validating the traffic";
  RETURN_IF_ERROR(traffic_helper_->ValidateTraffic(testbed_, kErrorPercentage));
  RETURN_IF_ERROR(ValidateComponents(&ComponentValidator::OnStopTraffic,
                                     component_validators_,
                                     next_image_config.image_label, testbed_));

  // TODO: Look into resetting the testbed state, including the
  // flows on the SUT, in the same state as that before the test.
  LOG(INFO) << "Clearing the flows from SUT";
  RETURN_IF_ERROR(flow_programmer_->ClearFlows(testbed_));

  RETURN_IF_ERROR(ValidateComponents(&ComponentValidator::OnFlowCleanup,
                                     component_validators_,
                                     next_image_config.image_label, testbed_));

  // P4 snapshot after cleaning up flows.
  LOG(INFO) << "Capturing P4 snapshot after cleaning up flows";
  ASSIGN_OR_RETURN(ReadResponse p4flow_snapshot4, TakeP4FlowSnapshot(testbed_));
  RETURN_IF_ERROR(SaveP4FlowSnapshot(
      testbed_, p4flow_snapshot4, "p4flow_snapshot4_after_clearing_flows.txt"));

  LOG(INFO) << "Comparing P4 snapshots - Before Programming Flows Vs After "
               "Clearing Flows";
  RETURN_IF_ERROR(CompareP4FlowSnapshots(p4flow_snapshot1, p4flow_snapshot4));
  LOG(INFO) << "Comparing P4 snapshots - Before Upgrade + NSF Reboot Vs. After "
               "Upgrade + NSF Reboot";
  RETURN_IF_ERROR(CompareP4FlowSnapshots(p4flow_snapshot2, p4flow_snapshot3));
  LOG(INFO) << "NSF Upgrade from: " << curr_image_config.image_label
            << " to: " << next_image_config.image_label << " is complete.";
  return absl::OkStatus();
}

TEST_P(NsfUpgradeTest, UpgradeAndReboot) {
  // The test needs at least 1 image_config_param to run.
  if (GetParam().image_config_params.empty()) {
    GTEST_SKIP() << "No image config params provided";
  }

  // The first element of the given `image_config_params` is considered as the
  // "base" image that will be installed and configured on the SUT before going
  // ahead with NSF Upgrade/Reboot for the following `image_config_params` (if
  // present) in order.
  ASSERT_OK(InstallRebootPushConfig(GetParam().image_config_params[0], testbed_,
                                    *ssh_client_));
  // If only a single config param is provided, we do an N to N upgrade.
  if (GetParam().image_config_params.size() == 1) {
    ASSERT_OK(NsfUpgradeOrReboot(GetParam().image_config_params[0],
                                 GetParam().image_config_params[0]));
    return;
  }
  // If multiple config params are provided, we do N - 1 to N upgrades.
  for (auto image_config_param = GetParam().image_config_params.begin();
       image_config_param + 1 != GetParam().image_config_params.end();
       ++image_config_param) {
    ASSERT_OK(
        NsfUpgradeOrReboot(*image_config_param, *(image_config_param + 1)));
  }
}

}  // namespace pins_test
