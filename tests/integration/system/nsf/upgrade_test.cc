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

#include <iterator>
#include <memory>
#include <string>
#include <vector>

#include "absl/flags/flag.h"
#include "absl/random/random.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "glog/logging.h"
#include "gutil/status_matchers.h"
#include "lib/gnmi/gnmi_helper.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "tests/integration/system/nsf/interfaces/component_validator.h"
#include "tests/integration/system/nsf/interfaces/flow_programmer.h"
#include "tests/integration/system/nsf/interfaces/image_config_params.h"
#include "tests/integration/system/nsf/interfaces/scenario.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "tests/integration/system/nsf/interfaces/traffic_helper.h"
#include "tests/integration/system/nsf/milestone.h"
#include "tests/integration/system/nsf/util.h"
#include "thinkit/proto/generic_testbed.pb.h"
#include "thinkit/switch.h"
#include "thinkit/test_environment.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"

ABSL_FLAG(pins_test::NsfMilestone, milestone, pins_test::NsfMilestone::kAll,
          "The NSF milestone to test.");

namespace pins_test {
namespace {

using ::p4::v1::ReadResponse;

NsfUpgradeScenario GetRandomNsfUpgradeScenario() {
  absl::BitGen gen;
  int random_index = absl::Uniform(
      gen, 0, static_cast<int>(NsfUpgradeScenario::kNumNsfUpgradeScenarios));

  return static_cast<NsfUpgradeScenario>(random_index);
}
}  // namespace

// approach than using std::variant (eg. type-erasure or typed tests).
void NsfUpgradeTest::SetUp() {
  flow_programmer_ = GetParam().create_flow_programmer();
  traffic_helper_ = GetParam().create_traffic_helper();
  testbed_interface_ = GetParam().create_testbed_interface();
  component_validators_ = GetParam().create_component_validators();
  ssh_client_ = GetParam().create_ssh_client();
  // TODO: Look into the possibility of initializing the link flap
  // counter after `InstallRebootPushConfig`.
  ExpectLinkFlaps(testbed_interface_);
  SetupTestbed(testbed_interface_);
  ASSERT_OK_AND_ASSIGN(testbed_, GetTestbed(testbed_interface_));
}
void NsfUpgradeTest::TearDown() { TearDownTestbed(testbed_interface_); }

// Used to append multiple errors. It enables the test to return as many errors
// as possible during the validation instead of returning on first error.
// TODO: Replace the AppendErrorStatus with StatusBuilder.
void AppendErrorStatus(absl::Status &ret_status, absl::Status status) {
  if (status.ok()) {
    return;
  }
  if (ret_status.ok()) {
    ret_status.Update(status);
  } else {
  }
}
absl::Status NsfUpgradeTest::PushConfigAndValidate(
    const ImageConfigParams& image_config_param,
    bool enable_interface_validation_during_nsf) {
  // We set the `check_interfaces_up` as `false` and not as
  // `enable_interface_validation_during_nsf`. This is because we already
  // validate the interfaces in the next statement in `ValidateTestbedState`.
  // Moreover, the interface validation in `PushConfig` is redundant because of
  // the same reason. However. the interface validation in `PushConfig` always
  // picks the interfaces from the model and does not yet support taking an
  // input of interfaces-to-check, which causes it to fail interface validation
  // in Replay scenario where DVaaS is enabled.
  RETURN_IF_ERROR(PushConfig(image_config_param, testbed_, *ssh_client_,
                             /*clear_config=*/false,
                             /*check_interfaces_up=*/false));
  std::vector<std::string> interfaces_to_check;

  RETURN_IF_ERROR(ValidateTestbedState(
      testbed_, *ssh_client_, &image_config_param,
      enable_interface_validation_during_nsf, interfaces_to_check));
  return ValidateComponents(
      &ComponentValidator::OnConfigPush, component_validators_,
      image_config_param.image_label, testbed_, *ssh_client_);
}

absl::Status NsfUpgradeTest::NsfUpgradeOrReboot(
    NsfUpgradeScenario scenario, ImageConfigParams &curr_image_config,
    ImageConfigParams &next_image_config,
    bool enable_interface_validation_during_nsf, bool &continue_on_failure) {
  continue_on_failure = false;
  absl::Status overall_status;

  std::string upgrade_path = absl::StrFormat(
      "NSF Upgrade from %s (%s) to %s (%s)", curr_image_config.image_version,
      curr_image_config.image_label, next_image_config.image_version,
      next_image_config.image_label);
  LOG(INFO) << "Initiating " << upgrade_path;

  std::vector<std::string> interfaces_to_check;
  RETURN_IF_ERROR(ValidateTestbedState(
      testbed_, *ssh_client_, &curr_image_config,
      enable_interface_validation_during_nsf, interfaces_to_check));
  absl::Status status =
      ValidateComponents(&ComponentValidator::OnInit, component_validators_,
                         curr_image_config.image_label, testbed_, *ssh_client_);
  if (!status.ok()) {
    AppendErrorStatus(
        overall_status,
        absl::InternalError(absl::StrFormat(
            "ComponentValidator::OnInit failed: %s", status.message())));
  }

  // P4 snapshot before programming flows and starting the traffic.
  LOG(INFO) << "Capturing P4 snapshot before programming flows and starting "
               "the traffic";

  ReadResponse p4flow_snapshot1;
  auto status_or_p4_snapshot1 = TakeP4FlowSnapshot(testbed_);
  if (!status_or_p4_snapshot1.ok()) {
    AppendErrorStatus(overall_status,
                      absl::InternalError(absl::StrFormat(
                          "Failed to take P4 snapshot before programming flows "
                          "and starting traffic: %s",
                          status_or_p4_snapshot1.status().message())));
  } else {
    p4flow_snapshot1 = status_or_p4_snapshot1.value();
    if (!SaveP4FlowSnapshot(
             testbed_, p4flow_snapshot1,
             absl::StrCat(curr_image_config.image_version, "_",
                          next_image_config.image_version,
                          "_p4flow_snapshot_before_programming_flows_",
                          absl::FormatTime("%H_%M_%S", absl::Now(),
                                           absl::LocalTimeZone()),
                          ".txt"))
             .ok()) {
      LOG(ERROR) << "Failed to save P4 snapshot before programming flows";
    }
  }

  // Program all the flows.
  LOG(INFO) << "Programming flows before starting the traffic";
  RETURN_IF_ERROR(flow_programmer_->ProgramFlows(curr_image_config, testbed_,
                                                 *ssh_client_));
  thinkit::Switch& sut = GetSut(testbed_);
  RETURN_IF_ERROR(ValidateTestbedState(
      testbed_, *ssh_client_, &curr_image_config,
      enable_interface_validation_during_nsf, interfaces_to_check));

  status = ValidateComponents(
      &ComponentValidator::OnFlowProgram, component_validators_,
      curr_image_config.image_label, testbed_, *ssh_client_);
  if (!status.ok()) {
    AppendErrorStatus(overall_status, absl::InternalError(absl::StrFormat(
                                          "ComponentValidator::OnFlowProgram "
                                          "failed: %s",
                                          status.message())));
  }

  LOG(INFO) << "Starting the traffic";
  status =
      traffic_helper_->StartTraffic(testbed_, curr_image_config.config_label);
  if (!status.ok()) {
    AppendErrorStatus(
        overall_status,
        absl::InternalError(absl::StrFormat(
            "StartTraffic failed before Upgrade and NSF reboot %s",
            status.message())));
  }

  status = ValidateComponents(
      &ComponentValidator::OnStartTraffic, component_validators_,
      curr_image_config.image_label, testbed_, *ssh_client_);
  if (!status.ok()) {
    AppendErrorStatus(overall_status, absl::InternalError(absl::StrFormat(
                                          "ComponentValidator::OnStartTraffic "
                                          "failed: %s",
                                          status.message())));
  }

  // P4 snapshot before Upgrade and NSF reboot.
  LOG(INFO) << "Capturing P4 snapshot before Upgrade and NSF reboot";

  ReadResponse p4flow_snapshot2;
  auto status_or_p4_snapshot2 = TakeP4FlowSnapshot(testbed_);
  if (!status_or_p4_snapshot2.ok()) {
    AppendErrorStatus(
        overall_status,
        absl::InternalError(absl::StrFormat(
            "Failed to take P4 snapshot before Upgrade and NSF reboot: %s",
            status_or_p4_snapshot2.status().message())));
  } else {
    p4flow_snapshot2 = status_or_p4_snapshot2.value();
    if (!SaveP4FlowSnapshot(
             testbed_, p4flow_snapshot2,
             absl::StrCat(curr_image_config.image_version, "_",
                          next_image_config.image_version,
                          "_p4flow_snapshot_before_upgrade_and_nsf_reboot_",
                          absl::FormatTime("%H_%M_%S", absl::Now(),
                                           absl::LocalTimeZone()),
                          ".txt"))
             .ok()) {
      LOG(ERROR) << "Failed to save P4 snapshot before upgrade and NSF reboot";
    }
  }

  ASSIGN_OR_RETURN(auto sut_gnmi_stub, sut.CreateGnmiStub());

  ASSIGN_OR_RETURN(
      PinsSoftwareComponentInfo pins_component_info_before_upgrade_reboot,
      GetPinsSoftwareComponentInfo(*sut_gnmi_stub),
      _.LogError() << "Failed to get pins software component info before "
                      "upgrade and reboot");

  LOG(INFO) << "Starting " << upgrade_path;

  // Copy image to the switch for installation.
  ASSIGN_OR_RETURN(
      std::string image_version,
      ImageCopy(next_image_config.image_label, testbed_, *ssh_client_),
      _.LogError() << "Copy image to the switch for installation failed");

  status = ValidateComponents(
      &ComponentValidator::OnImageCopy, component_validators_,
      next_image_config.image_label, testbed_, *ssh_client_);
  if (!status.ok()) {
    AppendErrorStatus(overall_status, absl::InternalError(absl::StrFormat(
                                          "ComponentValidator::OnImageCopy "
                                          "failed: %s",
                                          status.message())));
  }

  ASSIGN_OR_RETURN(
      PinsSoftwareComponentInfo pins_component_info_after_upgrade_before_reboot,
      GetPinsSoftwareComponentInfo(*sut_gnmi_stub),
      _.LogError() << "Failed to get pins software component info after "
                      "upgrade-before reboot");

  status = ValidatePinsSoftwareComponentsBeforeReboot(
      pins_component_info_after_upgrade_before_reboot,
      pins_component_info_before_upgrade_reboot, image_version);
  if (!status.ok()) {
    AppendErrorStatus(overall_status,
                      absl::InternalError(absl::StrFormat(
                          "ValidatePinsSoftwareComponentsBeforeReboot() "
                          "failed: %s",
                          status.message())));
  }

  // Perform NSF Reboot and validate switch state after reboot is completed.
  // Since the new config is not pushed yet, passing the existing config for
  // validation.
  RETURN_IF_ERROR(DoNsfRebootAndWaitForSwitchReady(
      testbed_, *ssh_client_, &curr_image_config,
      enable_interface_validation_during_nsf, interfaces_to_check));
  ASSIGN_OR_RETURN(sut_gnmi_stub, sut.CreateGnmiStub(),
                   _.LogError()
                       << "Failed to create GNMI stub after NSF reboot");

  ASSIGN_OR_RETURN(
      PinsSoftwareComponentInfo pins_component_info_after_upgrade_reboot,
      GetPinsSoftwareComponentInfo(*sut_gnmi_stub),
      _.LogError() << "Failed to get pins software component info after upgrade"
                      " and reboot");

  status = ValidatePinsSoftwareComponentsAfterReboot(
      pins_component_info_before_upgrade_reboot,
      pins_component_info_after_upgrade_reboot, image_version);
  if (!status.ok()) {
    AppendErrorStatus(overall_status,
                      absl::InternalError(absl::StrFormat(
                          "ValidatePinsSoftwareComponentsAfterReboot() "
                          "failed: %s",
                          status.message())));
  }

  LOG(INFO) << upgrade_path << ": NSF Reboot completed";

  status = ValidateComponents(
      &ComponentValidator::OnNsfReboot, component_validators_,
      next_image_config.image_label, testbed_, *ssh_client_);
  if (!status.ok()) {
    AppendErrorStatus(
        overall_status,
        absl::InternalError(absl::StrFormat(
            "ComponentValidator::OnNsfReboot failed %s", status.message())));
  }

  // P4 snapshot after upgrade and NSF reboot.
  LOG(INFO) << "Capturing P4 snapshot after Upgrade and NSF reboot";

  ReadResponse p4flow_snapshot3;
  auto status_or_p4_snapshot3 = TakeP4FlowSnapshot(testbed_);
  if (!status_or_p4_snapshot3.ok()) {
    AppendErrorStatus(
        overall_status,
        absl::InternalError(absl::StrFormat(
            "Failed to take P4 snapshot after Upgrade and NSF reboot: %s",
            status_or_p4_snapshot3.status().message())));
  } else {
    p4flow_snapshot3 = status_or_p4_snapshot3.value();
    if (!SaveP4FlowSnapshot(
             testbed_, p4flow_snapshot3,
             absl::StrCat(curr_image_config.image_version, "_",
                          next_image_config.image_version,
                          "_p4flow_snapshot_after_upgrade_and_nsf_reboot_",
                          absl::FormatTime("%H_%M_%S", absl::Now(),
                                           absl::LocalTimeZone()),
                          ".txt"))
             .ok()) {
      LOG(ERROR) << "Failed to save P4 snapshot after upgrade and NSF reboot";
    }
  }

  switch (scenario) {
    case NsfUpgradeScenario::kNoConfigPush:
      LOG(INFO) << upgrade_path << ": Proceeding with no config push scenario";
      RETURN_IF_ERROR(ValidateTestbedState(
          testbed_, *ssh_client_, &curr_image_config,
          enable_interface_validation_during_nsf, interfaces_to_check));
      break;
    case NsfUpgradeScenario::kOnlyConfigPush:
      LOG(INFO) << upgrade_path << ": Proceeding with only config push";

      status = PushConfigAndValidate(next_image_config,
                                     enable_interface_validation_during_nsf);
      if (!status.ok()) {
        AppendErrorStatus(overall_status,
                          absl::InternalError(absl::StrFormat(
                              "PushConfigAndValidate failed during "
                              "ConfigPushOnly scenario: %s",
                              status.message())));
      }

      break;
    case NsfUpgradeScenario::kConfigPushAfterAclFlowProgram:
      LOG(INFO) << upgrade_path
                << ": Proceeding with config push after ACL flow program";

      status = ProgramAclFlows(GetSut(testbed_), curr_image_config.p4_info);
      if (!status.ok()) {
        AppendErrorStatus(overall_status,
                          absl::InternalError(absl::StrFormat(
                              "ProgramAclFlows failed during "
                              "ConfigPushAfterAclFlowProgram scenario: %s",
                              status.message())));
      }

      status = PushConfigAndValidate(next_image_config,
                                     enable_interface_validation_during_nsf);
      if (!status.ok()) {
        AppendErrorStatus(overall_status,
                          absl::InternalError(absl::StrFormat(
                              "PushConfigAndValidate failed during "
                              "ConfigPushAfterAclFlowProgram scenario: %s",
                              status.message())));
      }

      break;

    case NsfUpgradeScenario::kConfigPushBeforeAclFlowProgram:
      LOG(INFO) << upgrade_path
                << ": Proceeding with config push before ACL flow program";
      status = PushConfigAndValidate(next_image_config,
                                     enable_interface_validation_during_nsf);
      if (!status.ok()) {
        AppendErrorStatus(overall_status,
                          absl::InternalError(absl::StrFormat(
                              "PushConfigAndValidate failed during "
                              "ConfigPushBeforeAclFlowProgram scenario: %s",
                              status.message())));
      }

      status = ProgramAclFlows(GetSut(testbed_), next_image_config.p4_info);
      if (!status.ok()) {
        AppendErrorStatus(overall_status,
                          absl::InternalError(absl::StrFormat(
                              "ProgramAclFlows failed during "
                              "ConfigPushBeforeAclFlowProgram scenario: %s",
                              status.message())));
      }

      break;
    case NsfUpgradeScenario::kNumNsfUpgradeScenarios:
      return absl::InvalidArgumentError("Invalid NSF Upgrade scenario.");
      break;
  }

  // Stop and validate traffic
  LOG(INFO) << "Stopping the traffic";
  status = traffic_helper_->StopTraffic(testbed_);
  if (!status.ok()) {
    AppendErrorStatus(overall_status,
                      absl::InternalError(absl::StrFormat(
                          "StopTraffic failed %s", status.message())));
  }

  // TODO: For now, we validate traffic only after stopping
  // traffic. Ideally we would want to validate traffic while injection is in
  // progress to narrow down when the traffic loss occurred (i.e. before
  // reboot, during reboot or after reconciliation). Although this is possible
  // in OTG traffic generator, DVaaS traffic generator for now does not
  // support traffic validation before stopping the traffic. This is a
  // good-to-have feature and we will update the skeleton to validate traffic
  // while injection is ongoing once this feature is available in DVaaS.
  LOG(INFO) << upgrade_path << ": Validating the traffic";

  status = traffic_helper_->ValidateTraffic(
      testbed_, next_image_config.max_acceptable_outage);
  if (!status.ok()) {
    AppendErrorStatus(overall_status,
                      absl::InternalError(absl::StrFormat(
                          "ValidateTraffic failed %s", status.message())));
  }

  status = ValidateComponents(
      &ComponentValidator::OnStopTraffic, component_validators_,
      next_image_config.image_label, testbed_, *ssh_client_);
  if (!status.ok()) {
    AppendErrorStatus(
        overall_status,
        absl::InternalError(absl::StrFormat(
            "ComponentValidator::OnStopTraffic failed %s", status.message())));
  }

  // TODO: Look into resetting the testbed state, including the
  // flows on the SUT, in the same state as that before the test.
  LOG(INFO) << "Clearing the flows from SUT";

  status = flow_programmer_->ClearFlows(testbed_);
  if (!status.ok()) {
    AppendErrorStatus(overall_status,
                      absl::InternalError(absl::StrFormat(
                          "ClearFlows failed %s", status.message())));
  }

  status = ValidateComponents(
      &ComponentValidator::OnFlowCleanup, component_validators_,
      next_image_config.image_label, testbed_, *ssh_client_);
  if (!status.ok()) {
    AppendErrorStatus(
        overall_status,
        absl::InternalError(absl::StrFormat(
            "ComponentValidator::OnFlowCleanup failed %s", status.message())));
  }

  // P4 snapshot after cleaning up flows.
  LOG(INFO) << "Capturing P4 snapshot after cleaning up flows";

  ReadResponse p4flow_snapshot4;
  auto status_or_p4_snapshot4 = TakeP4FlowSnapshot(testbed_);
  if (!status_or_p4_snapshot4.ok()) {
    AppendErrorStatus(
        overall_status,
        absl::InternalError(absl::StrFormat(
            "Failed to take P4 snapshot after cleaning up flows: %s",
            status_or_p4_snapshot4.status().message())));
  } else {
    p4flow_snapshot4 = status_or_p4_snapshot4.value();
    if (!SaveP4FlowSnapshot(
             testbed_, p4flow_snapshot4,
             absl::StrCat(curr_image_config.image_version, "_",
                          next_image_config.image_version,
                          "_p4flow_snapshot_after_clearing_flows_",
                          absl::FormatTime("%H_%M_%S", absl::Now(),
                                           absl::LocalTimeZone()),
                          ".txt"))
             .ok()) {
      LOG(ERROR) << "Failed to save P4 snapshot after clearing flows";
    }
  }

  if (status_or_p4_snapshot1.ok() && status_or_p4_snapshot4.ok()) {
    LOG(INFO) << upgrade_path
              << ": Comparing P4 snapshots - Before Programming Flows Vs After "
                 "Clearing Flows";
    status = CompareP4FlowSnapshots(p4flow_snapshot1, p4flow_snapshot4);
    if (!status.ok()) {
      GetTestEnvironment(testbed_)
          .StoreTestArtifact(
              absl::StrCat(
                  curr_image_config.image_version, "_",
                  next_image_config.image_version,
                  "_compare_p4flow_snapshot_before_programming_flows_and_after_"
                  "clearing_flows_",
                  absl::FormatTime("%H_%M_%S", absl::Now(),
                                   absl::LocalTimeZone()),
                  ".txt"),
              status.message())
          .IgnoreError();
      AppendErrorStatus(overall_status,
                        absl::InternalError(absl::StrFormat(
                            "Comparing P4 snapshots - Before Programming Flows "
                            "Vs After Clearing Flows failed")));
    }
  }

  if (status_or_p4_snapshot2.ok() && status_or_p4_snapshot3.ok()) {
    LOG(INFO) << upgrade_path
              << ": Comparing P4 snapshots - Before Upgrade + NSF Reboot Vs."
                 "After Upgrade + NSF Reboot";
    status = CompareP4FlowSnapshots(p4flow_snapshot2, p4flow_snapshot3);
    if (!status.ok()) {
      GetTestEnvironment(testbed_)
          .StoreTestArtifact(
              absl::StrCat(curr_image_config.image_version, "_",
                           next_image_config.image_version,
                           "_compare_p4flow_snapshot_before_upgrade_nsf_reboot_"
                           "and_after_"
                           "upgrade_nsf_reboot_",
                           absl::FormatTime("%H_%M_%S", absl::Now(),
                                            absl::LocalTimeZone()),
                           ".txt"),
              status.message())
          .IgnoreError();
      AppendErrorStatus(overall_status,
                        absl::InternalError(absl::StrFormat(
                            "Comparing P4 snapshots - Before Upgrade + NSF "
                            "Reboot Vs After Upgrade + NSF Reboot failed")));
    }
  }

  LOG(INFO) << upgrade_path << " is complete.";

  if (!overall_status.ok()) {
    LOG(ERROR) << "Failures encountered during " << upgrade_path << ": "
               << overall_status;
    continue_on_failure = true;
  }

  return overall_status;
}

TEST_P(NsfUpgradeTest, UpgradeAndReboot) {
  NsfUpgradeScenario scenario = GetRandomNsfUpgradeScenario();
  GetTestEnvironment(testbed_).SetTestCaseIDs(
      GetParam().get_test_case_ids(scenario));
  std::vector<ImageConfigParams> image_config_params =
      GetParam().image_config_params;
  // The test needs at least 1 image_config_param to run.
  if (image_config_params.empty()) {
    GTEST_SKIP() << "No image config params provided";
  }

  // In case the NSF Upgrade scenario is chosen to be the one where in each
  // iteration we skip pushing the config after NSF Upgrade, we intend to keep
  // the gNMI config and P4 Info constant throughout all the NSF Upgrade
  // iterations. Hence, we override the gNMI config and P4 Info, along with
  // other values except the image label, of all the `image_config_params` to be
  // the same, so that, in case required (eg. by a specific implementation of
  // `FlowProgrammer` in `ProgramFlows()`), we use the exact same gNMI config,
  // label, and P4 Info.
  if (scenario == NsfUpgradeScenario::kNoConfigPush) {
    LOG(INFO) << "Upgrading with no config push scenario. Overriding the gNMI "
                 "config and P4 Info of all the items in `image_config_params` "
                 "to be the same.";
    for (auto image_config_param = image_config_params.begin() + 1;
         image_config_param != image_config_params.end();
         ++image_config_param) {
      image_config_param->gnmi_config =
          image_config_params.begin()->gnmi_config;
      image_config_param->config_label =
          image_config_params.begin()->config_label;
      image_config_param->p4_info = image_config_params.begin()->p4_info;
    }
  }

  // The first element of the given `image_config_params` is considered
  // as the "base" image that will be installed and configured on the
  // SUT before going ahead with NSF Upgrade/Reboot for the following
  // `image_config_params` (if present) in order.

  ASSERT_OK(InstallRebootPushConfig(testbed_, *ssh_client_,
                                    image_config_params.front()));

  bool continue_on_failure;
  std::vector<std::string> error_msgs;
  absl::Status upgrade_status;
  // N - 1 to N upgrades.
  for (auto image_config_param = image_config_params.begin();
       image_config_param + 1 != image_config_params.end();
       ++image_config_param) {
    upgrade_status = (NsfUpgradeOrReboot(
        scenario, *image_config_param, *(image_config_param + 1),
        GetParam().enable_interface_validation_during_nsf,
        continue_on_failure));
    if (!upgrade_status.ok()) {
      error_msgs.push_back(absl::StrFormat(
          "%s -> %s: %s", image_config_param->image_version,
          (image_config_param + 1)->image_version, upgrade_status.ToString()));
      if (!continue_on_failure) {
        FAIL() << absl::StrJoin(error_msgs, "\n");
      }
    }
  }

  // N to N upgrade
  upgrade_status = NsfUpgradeOrReboot(
      scenario, image_config_params.back(), image_config_params.back(),
      GetParam().enable_interface_validation_during_nsf, continue_on_failure);
  if (!upgrade_status.ok()) {
    error_msgs.push_back(absl::StrFormat(
        "%s -> %s: %s", image_config_params.back().image_version,
        image_config_params.back().image_version, upgrade_status.ToString()));
  }
  if (!error_msgs.empty()) {
    FAIL() << absl::StrJoin(error_msgs, "\n");
  }
}

}  // namespace pins_test
