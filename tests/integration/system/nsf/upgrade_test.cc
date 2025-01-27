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
#include <vector>

#include "absl/flags/flag.h"
#include "absl/status/status.h"
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

// Assumption: Valid config (gNMI and P4Info) has been pushed (to avoid
// duplicate config push)
absl::Status NsfUpgradeTest::NsfUpgrade(absl::string_view prev_version,
                                        absl::string_view version) {
  RETURN_IF_ERROR(ValidateSutState(prev_version, testbed_, *ssh_client_));
  RETURN_IF_ERROR(ValidateComponents(&ComponentValidator::OnInit,
                                     component_validators_, prev_version,
                                     testbed_));
  RETURN_IF_ERROR(CaptureDbState());

  // P4 Snapshot before programming flows and starting the traffic.
  ReadResponse p4flow_snapshot1 = TakeP4FlowSnapshot();

  // Program all the flows.
  RETURN_IF_ERROR(flow_programmer_->ProgramFlows(testbed_));
  RETURN_IF_ERROR(ValidateComponents(&ComponentValidator::OnFlowProgram,
                                     component_validators_, prev_version,
                                     testbed_));

  RETURN_IF_ERROR(traffic_helper_->StartTraffic(testbed_));
  RETURN_IF_ERROR(ValidateComponents(&ComponentValidator::OnStartTraffic,
                                     component_validators_, prev_version,
                                     testbed_));


  // P4 Snapshot before Upgrade and NSF reboot.
  ReadResponse p4flow_snapshot2 = TakeP4FlowSnapshot();

  // Copy image to the switch for installation.
  RETURN_IF_ERROR(Upgrade(version));
  RETURN_IF_ERROR(ValidateComponents(&ComponentValidator::OnUpgrade,
                                     component_validators_, version, testbed_));

  // Perform NSF Reboot.
  RETURN_IF_ERROR(NsfReboot(testbed_, *ssh_client_));
  RETURN_IF_ERROR(WaitForReboot(testbed_, *ssh_client_));

  // Perform validations after reboot is completed.
  RETURN_IF_ERROR(ValidateComponents(&ComponentValidator::OnNsfReboot,
                                     component_validators_, version, testbed_));
  RETURN_IF_ERROR(ValidateSutState(version, testbed_, *ssh_client_));
  RETURN_IF_ERROR(ValidateDbState());

  // P4 Snapshot after upgrade and NSF reboot.
  ReadResponse p4flow_snapshot3 = TakeP4FlowSnapshot();

  // Push the new config and validate.
  RETURN_IF_ERROR(PushConfig(version));
  RETURN_IF_ERROR(ValidateSutState(version, testbed_, *ssh_client_));
  RETURN_IF_ERROR(ValidateComponents(&ComponentValidator::OnConfigPush,
                                     component_validators_, version, testbed_));

  // Wait for transmission duration.
  LOG(INFO) << "Wait for " << kTrafficRunDuration << " for transmit completion";
  absl::SleepFor(kTrafficRunDuration);

  // Stop and validate traffic
  RETURN_IF_ERROR(traffic_helper_->StopTraffic(testbed_));

  RETURN_IF_ERROR(traffic_helper_->ValidateTraffic(kErrorPercentage, testbed_));
  RETURN_IF_ERROR(ValidateComponents(&ComponentValidator::OnStopTraffic,
                                     component_validators_, version, testbed_));

  // Selectively clear flows (eg. not clearing nexthop entries for host
  // testbeds).
  RETURN_IF_ERROR(flow_programmer_->ClearFlows(testbed_));

  RETURN_IF_ERROR(ValidateComponents(&ComponentValidator::OnFlowCleanup,
                                     component_validators_, version, testbed_));

  ReadResponse p4flow_snapshot4 = TakeP4FlowSnapshot();

  RETURN_IF_ERROR(CompareP4FlowSnapshots(p4flow_snapshot1, p4flow_snapshot4));
  return CompareP4FlowSnapshots(p4flow_snapshot2, p4flow_snapshot3);
}

TEST_P(NsfUpgradeTest, UpgradeAndReboot) {
  static constexpr absl::string_view kThirdLastImage = "third_last_image";
  static constexpr absl::string_view kSecondLastImage = "second_last_image";
  static constexpr absl::string_view kLastImage = "last_image";
  static constexpr absl::string_view kCurrentImage = "current_image";

  ASSERT_OK(InstallRebootPushConfig(kThirdLastImage));

  // NSF Upgrade to N - 2 (once a week)
  ASSERT_OK(NsfUpgrade(kThirdLastImage, kSecondLastImage));

  // NSF Upgrade to N - 1
  ASSERT_OK(NsfUpgrade(kSecondLastImage, kLastImage));

  // NSF Upgrade to N
  ASSERT_OK(NsfUpgrade(kLastImage, kCurrentImage));
}

}  // namespace pins_test
