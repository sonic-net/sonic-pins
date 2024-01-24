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

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"  // NOLINT: Need to add status_matchers.h for using `ASSERT_OK` in upstream code.
#include "gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "tests/integration/system/nsf/interfaces/component_validator.h"
#include "tests/integration/system/nsf/interfaces/flow_programmer.h"
#include "tests/integration/system/nsf/interfaces/traffic_helper.h"
#include "tests/integration/system/nsf/util.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/proto/generic_testbed.pb.h"

namespace pins_test {

using ::p4::v1::ReadResponse;

constexpr int kErrorPercentage = 1;

void NsfUpgradeTest::SetUp() {
  flow_programmer_ = GetParam().create_flow_programmer();
  traffic_helper_ = GetParam().create_traffic_helper();
  testbed_interface_ = GetParam().create_testbed_interface();
  component_validators_ = GetParam().create_component_validators();
  testbed_interface_->SetUp();
}
void NsfUpgradeTest::TearDown() { testbed_interface_->TearDown(); }

// Assumption: Valid config (gNMI and P4Info) has been pushed (to avoid
// duplicate config push)
absl::Status NsfUpgradeTest::NsfUpgrade(absl::string_view prev_version,
                                        absl::string_view version) {
  // Pick a testbed with SUT connected to an Ixia on 2 ports, one ingress and
  // one egress port.
  auto requirements = gutil::ParseProtoOrDie<thinkit::TestRequirements>(
      R"pb(
        interface_requirements { count: 2 interface_mode: TRAFFIC_GENERATOR }
      )pb");
  ASSIGN_OR_RETURN(
      std::unique_ptr<thinkit::GenericTestbed> testbed,
      testbed_interface_->GetTestbedWithRequirements(requirements));

  RETURN_IF_ERROR(ValidateSwitchState(prev_version));
  RETURN_IF_ERROR(ValidateComponents(&ComponentValidator::OnInit,
                                     component_validators_, prev_version,
                                     *testbed));
  RETURN_IF_ERROR(CaptureDbState());

  // P4 Snapshot before programming flows and starting the
  // traffic.
  ReadResponse snapshot1 = TakeP4FlowSnapshot();

  // Program all the flows
  RETURN_IF_ERROR(flow_programmer_->ProgramFlows(IpVersion::kIpv4,
                                                 Protocol::kTcp, *testbed));
  RETURN_IF_ERROR(ValidateComponents(&ComponentValidator::OnFlowProgram,
                                     component_validators_, prev_version,
                                     *testbed));

  RETURN_IF_ERROR(traffic_helper_->StartTraffic(*testbed));
  RETURN_IF_ERROR(ValidateComponents(&ComponentValidator::OnStartTraffic,
                                     component_validators_, prev_version,
                                     *testbed));
  RETURN_IF_ERROR(traffic_helper_->ValidateTraffic(kErrorPercentage, *testbed));
  // Since the validation is while the traffic is in progress,
  // error margin needs to be defined.

  // P4 Snapshot before Upgrade and NSF reboot.
  ReadResponse snapshot2 = TakeP4FlowSnapshot();

  // Perform Upgrade
  RETURN_IF_ERROR(Upgrade(version));
  RETURN_IF_ERROR(ValidateComponents(&ComponentValidator::OnUpgrade,
                                     component_validators_, version, *testbed));

  // Perform NSF Reboot
  RETURN_IF_ERROR(NsfReboot(version));
  RETURN_IF_ERROR(ValidateComponents(&ComponentValidator::OnNsfReboot,
                                     component_validators_, version, *testbed));

  RETURN_IF_ERROR(ValidateSwitchState(version));
  RETURN_IF_ERROR(ValidateDbState());

  // P4 Snapshot after upgrade and NSF reboot.
  ReadResponse snapshot3 = TakeP4FlowSnapshot();

  RETURN_IF_ERROR(traffic_helper_->ValidateTraffic(kErrorPercentage, *testbed));
  RETURN_IF_ERROR(PushConfig(version));  // Push the newer config

  RETURN_IF_ERROR(ValidateSwitchState(version));
  RETURN_IF_ERROR(ValidateComponents(&ComponentValidator::OnConfigPush,
                                     component_validators_, version, *testbed));

  // Stop and validate traffic
  RETURN_IF_ERROR(traffic_helper_->ValidateTraffic(kErrorPercentage, *testbed));
  RETURN_IF_ERROR(traffic_helper_->StopTraffic(*testbed));

  // For now, we validate traffic only after stopping traffic. Ideally we
  // would want to validate traffic while injection is in progress to narrow
  // down when the traffic loss occurred (i.e. before reboot, during reboot or
  // after reconciliation). Although this is possible in OTG traffic
  // generators, DVaaS traffic generator for now does not support traffic
  // validation until only after stopping the traffic. This is a good-to-have
  // feature and we will update the skeleton to validate traffic while
  // injection is ongoing once this feature is available in DVaaS (more
  // details).
  RETURN_IF_ERROR(traffic_helper_->ValidateTraffic(kErrorPercentage, *testbed));
  RETURN_IF_ERROR(ValidateComponents(&ComponentValidator::OnStopTraffic,
                                     component_validators_, version, *testbed));

  // Selectively clear flows (eg. not clearing nexthop entries for host
  // testbeds)
  RETURN_IF_ERROR(flow_programmer_->ClearFlows(*testbed));

  RETURN_IF_ERROR(ValidateComponents(&ComponentValidator::OnFlowCleanup,
                                     component_validators_, version, *testbed));

  ReadResponse snapshot4 = TakeP4FlowSnapshot();

  RETURN_IF_ERROR(CompareP4FlowSnapshots(snapshot1, snapshot4));
  return CompareP4FlowSnapshots(snapshot2, snapshot3);
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
