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

#include "tests/integration/system/nsf/util.h"

#include <array>
#include <cstdint>
#include <functional>
#include <iterator>
#include <memory>
#include <string>
#include <string_view>
#include <utility>
#include <variant>
#include <vector>

#include "absl/base/nullability.h"
#include "absl/random/random.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "glog/logging.h"
#include "google/protobuf/util/message_differencer.h"
#include "grpcpp/client_context.h"
#include "gutil/gutil/overload.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/utils/generic_testbed_utils.h"
#include "lib/validator/validator_lib.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_runtime/p4_runtime_session.h"
#include "p4_infra/p4_runtime/p4_runtime_session_extras.h"
#include "p4_infra/p4_pdpi/pd.h"
#include "p4_infra/p4_pdpi/sequencing.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "sai_p4/instantiations/google/test_tools/table_entry_generator.h"
#include "system/system.pb.h"
#include "tests/integration/system/nsf/interfaces/component_validator.h"
#include "tests/integration/system/nsf/interfaces/image_config_params.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/generic_testbed_fixture.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/mirror_testbed_fixture.h"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

namespace pins_test {
namespace {

using ::gnoi::system::RebootMethod;
using ::gnoi::system::RebootMethod_Name;
using ::gnoi::system::RebootRequest;
using ::gnoi::system::RebootResponse;
using ::gnoi::system::RebootStatusRequest;
using ::gnoi::system::RebootStatusResponse;
using ::google::protobuf::util::MessageDifferencer;
using ::grpc::ClientContext;
using ::p4::config::v1::P4Info;
using ::p4::v1::Entity;
using ::p4::v1::ReadRequest;
using ::p4::v1::ReadResponse;
using ::p4::v1::Update;

constexpr absl::Duration kPollingInterval = absl::Seconds(10);
constexpr absl::Duration kTurnUpTimeout = absl::Minutes(6);
constexpr absl::Duration kTurnDownTimeout = absl::Minutes(2);
constexpr int kEpochMarginalError = 2;
constexpr std::array<absl::string_view, 2> kAclFlows = {
    R"pb(
      entries {
        acl_ingress_table_entry {
          match { ether_type { value: "0x88cc" mask: "0xffff" } }
          action { acl_trap { qos_queue: "INBAND_PRIORITY_4" } }
          priority: 2050
        }
      }
      entries {
        acl_ingress_qos_table_entry {
          match { ether_type { value: "0x88cc" mask: "0xffff" } }
          action {
            set_qos_queue_and_cancel_copy_above_rate_limit {
              qos_queue: "INBAND_PRIORITY_4"
            }
          }
          priority: 4600
          meter_config { bytes_per_second: 28000 burst_bytes: 7000 }
        }
      }
    )pb",
    R"pb(
      entries {
        acl_ingress_table_entry {
          match { ether_type { value: "0x0806" mask: "0xffff" } }
          action { acl_trap { qos_queue: "INBAND_PRIORITY_3" } }
          priority: 2031
        }
      }
      entries {
        acl_ingress_qos_table_entry {
          match { ether_type { value: "0x0806" mask: "0xffff" } }
          action {
            set_qos_queue_and_cancel_copy_above_rate_limit {
              qos_queue: "INBAND_PRIORITY_3"
            }
          }
          priority: 4600
          meter_config { bytes_per_second: 32000 burst_bytes: 8000 }
        }
      }
    )pb"};

std::string GetSwitchStateString(SwitchState state) {
  switch (state) {
    case SwitchState::kUp:
      return "Up";
    case SwitchState::kDown:
      return "Down";
    case SwitchState::kReady:
      return "Ready";
    case SwitchState::kReadyWithoutInterfacesUp:
      return "ReadyWithoutInterfacesUp";
    default:
      return "Unknown";
  }
}

// Inverts a given status, returning an error if it is ok and returning ok if it
// is an error.
absl::Status Not(const absl::Status& status, absl::string_view status_tag) {
  if (status.ok()) {
    return absl::InternalError(absl::StrCat(status_tag, " is still ok."));
  }
  return absl::OkStatus();
}

// Fields in P4 snapshot which needs to be ignored during comparison.
void AppendIgnoredP4SnapshotFields(MessageDifferencer* differencer) {
  if (differencer == nullptr) return;
  const google::protobuf::Descriptor& descriptor =
      *p4::v1::TableEntry().GetDescriptor();
  differencer->IgnoreField(descriptor.FindFieldByName("counter_data"));
  differencer->IgnoreField(descriptor.FindFieldByName("meter_counter_data"));
  differencer->set_report_ignores(false);
  differencer->set_report_moves(false);
  differencer->set_repeated_field_comparison(MessageDifferencer::AS_SET);
}

sai::TableEntries GetAclFlowEntries() {
  absl::BitGen gen;
  int random_index = absl::Uniform<int>(gen, 0, kAclFlows.size());
  return gutil::ParseProtoOrDie<sai::TableEntries>(kAclFlows[random_index]);
}

}  // namespace

absl::StatusOr<PinsSoftwareInfo> GetPinsSoftwareInfo(
    gnmi::gNMI::StubInterface* gnmi_stub, absl::string_view key) {
  PinsSoftwareInfo pins_sw_info;
  ASSIGN_OR_RETURN(pins_sw_info.name, GetOcOsNetworkStackGnmiStatePathInfo(
                                          *gnmi_stub, key, "name"));
  ASSIGN_OR_RETURN(
      pins_sw_info.oper_status,
      GetOcOsNetworkStackGnmiStatePathInfo(*gnmi_stub, key, "oper-status"));
  ASSIGN_OR_RETURN(pins_sw_info.parent, GetOcOsNetworkStackGnmiStatePathInfo(
                                            *gnmi_stub, key, "parent"));
  ASSIGN_OR_RETURN(std::string version,
                   GetOcOsNetworkStackGnmiStatePathInfo(*gnmi_stub, key,
                                                        "software-version"));
  pins_sw_info.version = std::string(pins_test::StripQuotes(version));
  ASSIGN_OR_RETURN(pins_sw_info.type, GetOcOsNetworkStackGnmiStatePathInfo(
                                          *gnmi_stub, key, "type"));
  return pins_sw_info;
}

absl::StatusOr<PinsSoftwareComponentInfo> GetPinsSoftwareComponentInfo(
    gnmi::gNMI::StubInterface& gnmi_stub) {
  PinsSoftwareComponentInfo pins_sw_component_info;
  ASSIGN_OR_RETURN(pins_sw_component_info.primary_network_stack,
                   GetPinsSoftwareInfo(&gnmi_stub, "network_stack0"));
  ASSIGN_OR_RETURN(pins_sw_component_info.secondary_network_stack,
                   GetPinsSoftwareInfo(&gnmi_stub, "network_stack1"));
  ASSIGN_OR_RETURN(pins_sw_component_info.primary_os,
                   GetPinsSoftwareInfo(&gnmi_stub, "os0"));
  ASSIGN_OR_RETURN(pins_sw_component_info.secondary_os,
                   GetPinsSoftwareInfo(&gnmi_stub, "os1"));

  LOG(INFO) << "Fetching Pins Software Component information.";
  LOG(INFO) << "Primary network stack: "
            << pins_sw_component_info.primary_network_stack;
  LOG(INFO) << "Secondary network stack: "
            << pins_sw_component_info.secondary_network_stack;
  LOG(INFO) << "Primary OS: " << pins_sw_component_info.primary_os;
  LOG(INFO) << "Secondary OS: " << pins_sw_component_info.secondary_os;

  return pins_sw_component_info;
}

bool IsPinsSoftwareInfoSame(PinsSoftwareInfo& pins_sw_info_1,
                            PinsSoftwareInfo& pins_sw_info_2) {
  return (pins_sw_info_1.name == pins_sw_info_2.name ||
          pins_sw_info_1.oper_status == pins_sw_info_2.oper_status ||
          pins_sw_info_1.parent == pins_sw_info_2.parent ||
          pins_sw_info_1.type == pins_sw_info_2.type);
}

absl::Status ValidatePinsSoftwareComponentsBeforeReboot(
    PinsSoftwareComponentInfo& pins_component_info_after_install_before_reboot,
    PinsSoftwareComponentInfo& pins_component_info_before_install_reboot,
    absl::string_view expected_version) {
  // After image upgrade and before reboot, all secondary network stack and OS
  // attributes must match (except software version which might have changed).
  LOG(INFO) << "Validating components after install/upgrade and before reboot";
  LOG(INFO) << "Validating if the secondary network stack details remain same";
  if (!IsPinsSoftwareInfoSame(
          pins_component_info_after_install_before_reboot
              .secondary_network_stack,
          pins_component_info_before_install_reboot.secondary_network_stack)) {
    return gutil::InternalErrorBuilder()
           << "Secondary network stack attributes match failed after "
              "install / upgrade and before reboot (name, oper-status, parent, "
              "storage-side, type).\nSecondary network stack (after "
              "install / upgrade): "
           << pins_component_info_after_install_before_reboot
                  .secondary_network_stack
           << "\nSecondary network stack (before install / upgrade): "
           << pins_component_info_before_install_reboot.secondary_network_stack;
  }

  LOG(INFO) << "Validating if the secondary network stack version is different";
  if (pins_component_info_after_install_before_reboot.secondary_network_stack
          .version != expected_version) {
    return gutil::InternalErrorBuilder()
           << "Secondary network stack version match failed after install / "
              "upgrade and before reboot.\nSecondary network stack version: "
           << pins_component_info_after_install_before_reboot
                  .secondary_network_stack.version
           << "\nExpected version: " << expected_version;
  }

  LOG(INFO) << "Validating if the secondary OS details remain same";
  if (!IsPinsSoftwareInfoSame(
          pins_component_info_after_install_before_reboot.secondary_os,
          pins_component_info_before_install_reboot.secondary_os)) {
    return gutil::InternalErrorBuilder()
           << "Secondary OS attributes match failed after install / upgrade "
              "and before reboot (name, oper-status, parent, storage-side, "
              "type).\nSecondary OS (after install / upgrade): "
           << pins_component_info_after_install_before_reboot.secondary_os
           << "\nSecondary OS (before install / upgrade): "
           << pins_component_info_before_install_reboot.secondary_os;
  }

  // Primary network stack and OS information should not change.
  LOG(INFO) << "Validating if the primary network stack details remain same";
  if (pins_component_info_after_install_before_reboot.primary_network_stack !=
      pins_component_info_before_install_reboot.primary_network_stack) {
    return gutil::InternalErrorBuilder()
           << "Primary network stack attributes match failed after install / "
              "upgrade and before reboot.\nPrimary network stack (after "
              "install / upgrade): "
           << pins_component_info_after_install_before_reboot
                  .primary_network_stack
           << "\nPrimary network stack (before install / upgrade): "
           << pins_component_info_before_install_reboot.primary_network_stack;
  }

  LOG(INFO) << "Validating if the primary OS details remain same";
  if (pins_component_info_after_install_before_reboot.primary_os !=
      pins_component_info_before_install_reboot.primary_os) {
    return gutil::InternalErrorBuilder()
           << "Primary OS attributes match failed after install / upgrade and "
              "before reboot.\nPrimary OS (after install / upgrade): "
           << pins_component_info_after_install_before_reboot.primary_os
           << "\nPrimary OS (before install / upgrade): "
           << pins_component_info_before_install_reboot.primary_os;
  }

  return absl::OkStatus();
}

absl::Status ValidatePinsSoftwareComponentsAfterReboot(
    const PinsSoftwareComponentInfo& pins_component_info_before_install_reboot,
    const PinsSoftwareComponentInfo& pins_component_info_after_install_reboot,
    absl::string_view expected_version) {
  // Validate that switch has booted to the expected version after
  // install / upgrade and reboot.
  LOG(INFO) << "Validating components after install / upgrade and reboot";
  LOG(INFO) << "Validating if the primary network stack version is different";
  PinsSoftwareInfo primary_before_install_reboot =
      pins_component_info_before_install_reboot.primary_network_stack;
  PinsSoftwareInfo primary_after_install_reboot =
      pins_component_info_after_install_reboot.primary_network_stack;
  PinsSoftwareInfo secondary_after_install_reboot =
      pins_component_info_after_install_reboot.secondary_network_stack;
  if (!expected_version.empty() &&
      primary_after_install_reboot.version != expected_version) {
    return gutil::InternalErrorBuilder()
           << "Primary after reboot version match failed.\nPrimary version "
              "after reboot: "
           << primary_after_install_reboot.version
           << "\nExpected version: " << expected_version;
  }

  // Primary component before and after reboot share the following attributes:
  // name, oper-status, parent, type.
  LOG(INFO) << "Validating if the primary network stack component details such "
               "as name, oper-status, parent, type remain same";
  if (primary_before_install_reboot.name != primary_after_install_reboot.name ||
      primary_before_install_reboot.oper_status !=
          primary_after_install_reboot.oper_status ||
      primary_before_install_reboot.parent !=
          primary_after_install_reboot.parent ||
      primary_before_install_reboot.type != primary_after_install_reboot.type) {
    return gutil::InternalErrorBuilder()
           << "Primary before and after reboot attributes match failed which "
              "are expected to remain same "
              "(name, oper-status, parent, type).\nPrimary before reboot: "
           << primary_before_install_reboot
           << "\nPrimary after reboot: " << primary_after_install_reboot;
  }

  // Primary component before reboot should be the same as secondary component
  // after reboot, except for name and oper-status.
  LOG(INFO)
      << "Validating if the secondary network stack component details such as "
         "parent, type, software-version, storage-side after reboot remain "
         "same as primary network stack component details before reboot";
  if (primary_before_install_reboot.parent !=
          secondary_after_install_reboot.parent ||
      primary_before_install_reboot.type !=
          secondary_after_install_reboot.type ||
      primary_before_install_reboot.version !=
          secondary_after_install_reboot.version) {
    return gutil::InternalErrorBuilder()
           << "Primary before reboot and secondary after reboot attributes "
              "match failed which are expected to remain same (parent, type, "
              "software-version, "
              "storage-side).\nPrimary before reboot: "
           << primary_before_install_reboot
           << "\nSecondary after reboot: " << secondary_after_install_reboot;
  }

  LOG(INFO) << "Validating if the primary network stack component details such "
               "as name, oper-status before reboot are different compared to "
               "the secondary network stack after reboot";
  if (primary_before_install_reboot.name ==
          secondary_after_install_reboot.name ||
      primary_before_install_reboot.oper_status ==
          secondary_after_install_reboot.oper_status) {
    return gutil::InternalErrorBuilder()
           << "Primary before reboot and secondary after reboot "
              "name/oper-status should be different.\nPrimary before reboot: "
           << primary_before_install_reboot
           << "\nSecondary after reboot: " << secondary_after_install_reboot;
  }
  return absl::OkStatus();
}

std::vector<std::string> GetConnectedInterfacesForSut(const Testbed &testbed) {
  return std::visit(gutil::Overload{[&](thinkit::GenericTestbed *testbed) {
                                      return FromTestbed(
                                          GetAllConnectedInterfaces, *testbed);
                                    },
                                    [&](thinkit::MirrorTestbed *testbed) {
                                      return testbed->GetConnectedInterfaces();
                                    }},
                    testbed);
}

absl::Status RunReadyValidations(thinkit::Switch& thinkit_switch,
                                 thinkit::SSHClient& ssh_client,
                                 absl::Span<const std::string> interfaces,
                                 bool check_interfaces_state,
                                 bool with_healthz) {
  RETURN_IF_ERROR(SwitchReadyWithSsh(thinkit_switch, ssh_client, interfaces,
                                     check_interfaces_state, with_healthz));

  return absl::OkStatus();
}

absl::Status WaitForSwitchState(thinkit::Switch& thinkit_switch,
                                SwitchState state, absl::Duration timeout,
                                thinkit::SSHClient& ssh_client,
                                absl::Span<const std::string> interfaces) {
  absl::string_view chassis = thinkit_switch.ChassisName();
  absl::Status validator_status =
      absl::InternalError("No validators have run.");
  absl::Time start_time = absl::Now();
  while (absl::Now() - start_time < timeout) {
    switch (state) {
      case SwitchState::kUp:
        validator_status = SSHable(chassis, ssh_client);
        break;
      case SwitchState::kDown:
        validator_status = Not(SSHable(chassis, ssh_client), "SSHable");
        break;
      case SwitchState::kReady:
        validator_status =
            RunReadyValidations(thinkit_switch, ssh_client, interfaces,
                                /*check_interfaces_state=*/true,
                                /*with_healthz=*/false);
        break;
      case SwitchState::kReadyWithoutInterfacesUp:
        validator_status =
            RunReadyValidations(thinkit_switch, ssh_client, interfaces,
                                /*check_interfaces_state=*/false);
        break;
      default:
        return absl::UnimplementedError("State not recognized");
    }
    if (validator_status.ok()) {
      break;
    }
  }

  std::string elapsed_time = absl::FormatDuration(absl::Now() - start_time);
  if (validator_status.ok()) {
    LOG(INFO) << absl::Substitute("$0 $1 state reached in $2.", chassis,
                                  GetSwitchStateString(state), elapsed_time);
    return absl::OkStatus();
  }

  // If a ready validation was requested, there is a chance that some ports
  // were down that caused it to fail. If so, check that ports are up,
  // including healthz debug data.
  if (state == SwitchState::kReady) {
    absl::Status ports_up = PortsUp(thinkit_switch, interfaces);
    LOG_IF(WARNING, !ports_up.ok()) << ports_up;
  }
  return absl::DeadlineExceededError(absl::Substitute(
      "$0 $1 state not reached after $2. Status: $3", chassis,
      GetSwitchStateString(state), elapsed_time, validator_status.message()));
}

absl::Status Reboot(RebootMethod method, thinkit::Switch& sut,
                    thinkit::TestEnvironment& env,
                    bool collect_debug_artifacts_before_reboot) {
  LOG(INFO) << "Initiating Switch reboot. Reboot method: "
            << RebootMethod_Name(method);
  ASSIGN_OR_RETURN(auto sut_gnoi_system_stub, sut.CreateGnoiSystemStub());
  RebootRequest request;
  request.set_method(method);
  request.set_message(
      absl::StrCat("Performing ", RebootMethod_Name(method), " Reboot"));
  RebootResponse response;
  ClientContext context;

  if (collect_debug_artifacts_before_reboot) {
    RETURN_IF_ERROR(StoreSutDebugArtifacts(
        absl::StrCat(
            "before_", RebootMethod_Name(method), "_reboot_",
            absl::FormatTime("%H_%M_%S", absl::Now(), absl::LocalTimeZone())),
        sut, env));
  }

  return gutil::GrpcStatusToAbslStatus(
      sut_gnoi_system_stub->Reboot(&context, request, &response));
}

void SetupTestbed(TestbedInterface& testbed_interface) {
  std::visit([](auto &&testbed) { testbed->SetUp(); }, testbed_interface);
}

void TearDownTestbed(TestbedInterface& testbed_interface) {
  std::visit([](auto &&testbed) { testbed->TearDown(); }, testbed_interface);
}

absl::StatusOr<TestbedHolder> GetTestbed(TestbedInterface& testbed_interface,
                                         bool is_inband_testbed) {
  return std::visit(
      gutil::Overload{
          [&](std::unique_ptr<thinkit::GenericTestbedInterface>& testbed)
              -> absl::StatusOr<TestbedHolder> {
            // Pick a testbed with SUT connected to a traffic generator, be it a
            // software (eg. on a host) or a hardware (eg. Ixia), on 2 ports,
            // one ingress and one egress port.
            if (is_inband_testbed) {
              return testbed->GetTestbedWithRequirements(
                  gutil::ParseProtoOrDie<thinkit::TestRequirements>(
                      R"pb(
                        interface_requirements {
                          count: 0
                          interface_mode: DISCONNECTED
                        }
                      )pb"));
            }
            return testbed->GetTestbedWithRequirements(
                gutil::ParseProtoOrDie<thinkit::TestRequirements>(
                    R"pb(
                      interface_requirements {
                        count: 2
                        interface_mode: TRAFFIC_GENERATOR
                      }
                    )pb"));
          },
          [](std::unique_ptr<thinkit::MirrorTestbedInterface>& testbed)
              -> absl::StatusOr<TestbedHolder> {
            return &testbed->GetMirrorTestbed();
          }},
      testbed_interface);
}

thinkit::Switch &GetSut(const Testbed &testbed) {
  return std::visit(
      [](auto &&testbed) -> thinkit::Switch & { return testbed->Sut(); },
      testbed);
}

thinkit::TestEnvironment &GetTestEnvironment(const Testbed &testbed) {
  return std::visit(
      [](auto &&testbed) -> thinkit::TestEnvironment & {
        return testbed->Environment();
      },
      testbed);
}

void ExpectLinkFlaps(TestbedInterface &testbed_interface) {
  std::visit(
      [](auto &&testbed_interface) { testbed_interface->ExpectLinkFlaps(); },
      testbed_interface);
}

absl::StatusOr<std::string> ImageCopy(const std::string& image_label,
                                      thinkit::Switch& sut,
                                      thinkit::SSHClient& ssh_client) {
  return "";
}

absl::Status InstallRebootPushConfig(
    const Testbed& testbed, thinkit::SSHClient& ssh_client,
    const ImageConfigParams& sut_image_config_param,
    const ImageConfigParams& cs_image_config_param) {
  thinkit::Switch& sut = GetSut(testbed);
  thinkit::TestEnvironment& env = GetTestEnvironment(testbed);
  ASSIGN_OR_RETURN(auto sut_gnmi_stub, sut.CreateGnmiStub());

  ASSIGN_OR_RETURN(
      PinsSoftwareComponentInfo pins_component_info_before_install_reboot,
      GetPinsSoftwareComponentInfo(*sut_gnmi_stub));
  LOG(INFO) << "gNOI Install: Copying image to inactive partition";
  ASSIGN_OR_RETURN(
      std::string image_version,
      ImageCopy(sut_image_config_param.image_label, sut, ssh_client));

  ASSIGN_OR_RETURN(
      PinsSoftwareComponentInfo pins_component_info_after_install_before_reboot,
      GetPinsSoftwareComponentInfo(*sut_gnmi_stub));
  RETURN_IF_ERROR(ValidatePinsSoftwareComponentsBeforeReboot(
      pins_component_info_after_install_before_reboot,
      pins_component_info_before_install_reboot, image_version));

  RETURN_IF_ERROR(Reboot(RebootMethod::COLD, sut, env));

  ASSIGN_OR_RETURN(auto sut_gnoi_os_stub, sut.CreateGnoiOsStub());

  // Wait for SSH and containers to be up before pushing config.
  RETURN_IF_ERROR(
      WaitForReboot(testbed, ssh_client, /*check_interfaces_up=*/false));

  LOG(INFO) << "gNOI install is complete.";
  LOG(INFO) << "Proceeding with config push on SUT.";
  RETURN_IF_ERROR(PushConfig(sut_image_config_param, sut, ssh_client,
                             /*clear_config=*/true));
  std::vector<std::string> interfaces_to_check =
      GetConnectedInterfacesForSut(testbed);
  SwitchState intent_state = SwitchState::kReady;
  RETURN_IF_ERROR(WaitForSwitchState(sut, intent_state, kTurnUpTimeout,
                                     ssh_client, interfaces_to_check));

  LOG(INFO) << "Initial setup of image install, cold reboot and config push is "
               "complete.";
  return absl::OkStatus();
}

absl::Status ValidateTestbedState(
    const Testbed &testbed, thinkit::SSHClient &ssh_client,
    absl::Nullable<const ImageConfigParams *> image_config_param,
    bool check_interfaces_up, absl::Span<const std::string> interfaces) {
  // TODO: Add validation for SUT stack image label.
  LOG(INFO) << "Validating SUT state";
  thinkit::Switch& sut = GetSut(testbed);
  std::vector<std::string> interfaces_to_validate;
  if (check_interfaces_up && interfaces.empty()) {
    interfaces_to_validate = GetConnectedInterfacesForSut(testbed);
    interfaces = interfaces_to_validate;
  }
  absl::Status sut_status = RunReadyValidations(
      sut, ssh_client, interfaces, check_interfaces_up, /*with_healthz=*/true);

  absl::StatusOr<thinkit::MirrorTestbed*> mirror_testbed =
      GetMirrorTestbed(testbed);
  if (!mirror_testbed.ok()) {
    LOG(INFO) << "No control switch found in the testbed. Skipping control "
                 "switch validation.";
    return sut_status;
  }
  absl::Status control_status;
  if (!(*mirror_testbed)->ControlSwitch().ChassisName().empty()) {
    control_status =
        RunReadyValidations((*mirror_testbed)->ControlSwitch(), ssh_client,
                            interfaces, check_interfaces_up,
                            /*with_healthz=*/true);
  }
  RETURN_IF_ERROR(sut_status);
  return control_status;
}

absl::Status ValidateComponents(
    absl::Status (ComponentValidator::*validate)(absl::string_view,
                                                 const Testbed &,
                                                 thinkit::SSHClient &),
    const absl::Span<const std::unique_ptr<ComponentValidator>> validators,
    absl::string_view version, const Testbed &testbed,
    thinkit::SSHClient &ssh_client) {
  absl::Status overall_status;
  for (const std::unique_ptr<ComponentValidator>& validator : validators) {
    AppendErrorStatus(overall_status, std::invoke(validate, validator, version,
                                                  testbed, ssh_client));
  }
  return overall_status;
}

absl::Status NsfReboot(const Testbed &testbed) {
  thinkit::Switch& sut = GetSut(testbed);
  thinkit::TestEnvironment& env = GetTestEnvironment(testbed);
  return Reboot(RebootMethod::NSF, sut, env);
}

absl::Status WaitForReboot(const Testbed& testbed,
                           thinkit::SSHClient& ssh_client,
                           bool check_interfaces_up,
                           absl::Span<const std::string> interfaces) {
  LOG(INFO) << "Waiting for switch to go down and come back up";
  // Wait for switch to go down and come back up.
  thinkit::Switch& sut = GetSut(testbed);
  std::vector<std::string> interfaces_to_validate;
  if (check_interfaces_up && interfaces.empty()) {
    interfaces_to_validate = GetConnectedInterfacesForSut(testbed);
    interfaces = interfaces_to_validate;
  }

  RETURN_IF_ERROR(WaitForSwitchState(sut, SwitchState::kDown, kTurnDownTimeout,
                                     ssh_client));
  return WaitForSwitchState(sut,
                            check_interfaces_up
                                ? SwitchState::kReady
                                : SwitchState::kReadyWithoutInterfacesUp,
                            kTurnUpTimeout, ssh_client, interfaces);
}

absl::Status
WaitForNsfReboot(const Testbed &testbed, thinkit::SSHClient &ssh_client,
                 absl::Nullable<const ImageConfigParams *> image_config_param,
                 bool check_interfaces_up,
                 absl::Span<const std::string> interfaces,
                 bool collect_debug_logs_for_nsf_success) {
  LOG(INFO) << "Waiting for switch to go down and come back up post NSF reboot";
  // Wait for switch to do NSF reboot.
  thinkit::Switch& sut = GetSut(testbed);
  thinkit::TestEnvironment& env = GetTestEnvironment(testbed);
  absl::Time start_time = absl::Now();
  std::unique_ptr<gnoi::system::System::StubInterface> sut_gnoi_system_stub;
  // Start polling to check for NSF reboot completion.
  while (absl::Now() < (start_time + kNsfRebootWaitTime)) {
    absl::SleepFor(kPollingInterval);
    ASSIGN_OR_RETURN(sut_gnoi_system_stub, sut.CreateGnoiSystemStub());
    ClientContext context;
    RebootStatusRequest req;
    RebootStatusResponse resp;
    // Invoke the RPC and validate the results.
    grpc::Status reboot_status =
        sut_gnoi_system_stub->RebootStatus(&context, req, &resp);
    // If the RPC fails or the NSF reboot is still active, continue to poll.
    if (!reboot_status.ok() || resp.active()) {
      LOG(WARNING) << "Reboot Status: " << reboot_status.error_message();
      LOG(WARNING) << "Reboot Status Response: " << resp.DebugString();
      continue;
    }
    LOG(INFO) << "NSF Reboot succeeded: " << resp.DebugString()
              << "\nProceeding with Switch State Validation.";
    if (collect_debug_logs_for_nsf_success) {
      RETURN_IF_ERROR(StoreSutDebugArtifacts(
          absl::StrCat(
              "after_nsf_reboot_success_",
              absl::FormatTime("%H_%M_%S", absl::Now(), absl::LocalTimeZone())),
          sut, env));
    }
    return ValidateTestbedState(testbed, ssh_client, image_config_param,
                                check_interfaces_up, interfaces);
  }
  return gutil::InternalErrorBuilder()
         << "NSF Reboot validation failed after polling for "
         << absl::FormatDuration(kNsfRebootWaitTime) << " .";
}

absl::Status DoNsfRebootAndWaitForSwitchReady(
    const Testbed &testbed, thinkit::SSHClient &ssh_client,
    absl::Nullable<const ImageConfigParams *> image_config_param,
    bool check_interfaces_up, absl::Span<const std::string> interfaces) {
  thinkit::Switch& sut = GetSut(testbed);
  ASSIGN_OR_RETURN(auto sut_gnmi_stub, sut.CreateGnmiStub());
  ASSIGN_OR_RETURN(uint64_t up_time_before_nsf,
                   pins_test::GetGnmiSystemUpTime(*sut_gnmi_stub));
  RETURN_IF_ERROR(NsfReboot(testbed));
  RETURN_IF_ERROR(WaitForNsfReboot(testbed, ssh_client, image_config_param,
                                   check_interfaces_up, interfaces));
  // Recreating the gNMI stub as the switch rebooted.
  ASSIGN_OR_RETURN(sut_gnmi_stub, sut.CreateGnmiStub());
  ASSIGN_OR_RETURN(uint64_t up_time_after_nsf,
                   pins_test::GetGnmiSystemUpTime(*sut_gnmi_stub));
  if (up_time_after_nsf - up_time_before_nsf <= kEpochMarginalError) {
    return gutil::InternalErrorBuilder()
           << "Switch up-time after NSF reboot is not greater than the up-time "
              "before NSF reboot. Before: "
           << up_time_before_nsf << " After: " << up_time_after_nsf;
  }
  return absl::OkStatus();
}

absl::Status DoNsfRebootAndWaitForSwitchReadyOrRecover(
    const Testbed& testbed, thinkit::SSHClient& ssh_client,
    absl::Nullable<const ImageConfigParams*> image_config_param,
    bool check_interfaces_up, absl::Span<const std::string> interfaces) {
  thinkit::Switch& sut = GetSut(testbed);
  thinkit::TestEnvironment& env = GetTestEnvironment(testbed);
  absl::Status nsf_reboot_status;
  nsf_reboot_status = DoNsfRebootAndWaitForSwitchReady(
      testbed, ssh_client, image_config_param, check_interfaces_up, interfaces);
  if (!nsf_reboot_status.ok()) {
    ADD_FAILURE() << "NSF reboot failed with: " << nsf_reboot_status;
    LOG(ERROR) << "Attempting to recover the switch through cold "
                  "reboot.";
    thinkit::TestEnvironment& env = GetTestEnvironment(testbed);
    RETURN_IF_ERROR(Reboot(RebootMethod::COLD, sut, env,
                           /*collect_debug_artifacts_before_reboot=*/false));
    RETURN_IF_ERROR(
        WaitForReboot(testbed, ssh_client, check_interfaces_up, interfaces));
    return gutil::InternalErrorBuilder()
           << "NSF reboot failed. Switch recovered successfully through cold "
              "reboot.";
  }
  return nsf_reboot_status;
}

// In cases where `clear_config` is not set, we do not use the
// `ConfigureSwitchAndReturnP4RuntimeSession` method (which does some additional
// workarounds along with clearing the config).
//
// Instead we directly use the `PushGnmiConfig` and
// `SetMetadataAndSetForwardingPipelineConfig` methods to push the gNMI config
// and P4 Info respectively.
//
absl::Status PushConfig(thinkit::Switch& thinkit_switch,
                        absl::string_view gnmi_config,
                        const p4::config::v1::P4Info& p4_info,
                        absl::string_view config_label, bool clear_config,
                        bool is_inband_testbed) {
  // TestEnvironment.StoreTestArtifact.
  if (config_label.empty()) {
    LOG(INFO) << "Pushing config on " << thinkit_switch.ChassisName();
  } else {
    LOG(INFO) << "Pushing config with config label: " << config_label
              << " on chassis: " << thinkit_switch.ChassisName();
  }
  if (clear_config) {
    // In case of inband testbeds, only gNMI config will be pushed initially.
    // This is because, pushing P4Info along with gNMI config will delete the
    // default route on the inband testbed and breaks the gNMI connection. It
    // is necessary to install the P4 flows to re-establish the connectivity.
    // Hence we skip the P4Info push for inband testbeds initially. Subsequently
    // the P4Info will be pushed along with the P4 flows as part of flow
    // programming.
    if (is_inband_testbed) {
      return PushGnmiConfig(thinkit_switch, gnmi_config);
    }
    return ConfigureSwitchAndReturnP4RuntimeSession(thinkit_switch, gnmi_config,
                                                    p4_info)
        .status();
  }

  RETURN_IF_ERROR(PushGnmiConfig(thinkit_switch, gnmi_config));
  ASSIGN_OR_RETURN(std::unique_ptr<p4_runtime::P4RuntimeSession> session,
                   p4_runtime::P4RuntimeSession::Create(thinkit_switch));
  return p4_runtime::SetMetadataAndSetForwardingPipelineConfig(
      session.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      p4_info);
}

absl::Status PushConfig(const ImageConfigParams& image_config_param,
                        thinkit::Switch& thinkit_switch,
                        thinkit::SSHClient& ssh_client, bool clear_config,
                        bool is_inband_testbed) {
  // The gNMI configuration's device ID is dynamically updated with the actual
  // device ID of the target thinkit switch. This ensures successful config
  // convergence, as the switch-reported device ID matches the device ID used
  // for convergence checks. Without this update, a mismatch would occur between
  // the actual device ID and the original device ID in the gNMI config, leading
  // to convergence failures.
  const std::string gnmi_config = pins_test::UpdateDeviceIdInJsonConfig(
      image_config_param.gnmi_config, absl::StrCat(thinkit_switch.DeviceId()));
  RETURN_IF_ERROR(PushConfig(
      thinkit_switch, gnmi_config, image_config_param.p4_info,
      image_config_param.config_label, clear_config, is_inband_testbed));
  return absl::OkStatus();
}

absl::Status ProgramAclFlows(thinkit::Switch& thinkit_switch,
                             const P4Info& p4_info) {
  sai::TableEntries entries = GetAclFlowEntries();
  ASSIGN_OR_RETURN(std::unique_ptr<p4_runtime::P4RuntimeSession> sut_p4rt,
                   p4_runtime::P4RuntimeSession::Create(thinkit_switch));
  ASSIGN_OR_RETURN(pdpi::IrP4Info ir_p4info, pdpi::CreateIrP4Info(p4_info));
  std::vector<Entity> pi_entities;
  pi_entities.reserve(entries.entries_size());
  for (const sai::TableEntry& entry : entries.entries()) {
    ASSIGN_OR_RETURN(pi_entities.emplace_back(),
                     pdpi::PdTableEntryToPiEntity(ir_p4info, entry));
  }
  LOG(INFO) << "Installing PI table entries on "
            << thinkit_switch.ChassisName();
  return p4_runtime::InstallPiEntities(sut_p4rt.get(), ir_p4info, pi_entities);
}

// Program flows based on table_name to the capacity.
absl::Status ProgramFlowsBasedOnTable(thinkit::Switch& thinkit_switch,
                                      const P4Info& p4_info,
                                      absl::string_view table_name) {
  ASSIGN_OR_RETURN(pdpi::IrP4Info ir_p4info, pdpi::CreateIrP4Info(p4_info));
  const pdpi::IrTableDefinition& table =
      ir_p4info.tables_by_name().at(table_name);
  ASSIGN_OR_RETURN(auto generator, sai::GetGenerator(table),
                   _ << "Failed to get table entry generator for table "
                     << table.preamble().alias());
  ASSIGN_OR_RETURN(std::unique_ptr<p4_runtime::P4RuntimeSession> sut_p4rt,
                   p4_runtime::P4RuntimeSession::Create(thinkit_switch));

  if (!generator.prerequisites.empty()) {
    LOG(INFO) << "Installing prerequisite table entries";
    for (const auto& prerequisite : generator.prerequisites) {
      RETURN_IF_ERROR(p4_runtime::InstallIrTableEntry(*sut_p4rt, prerequisite))
          << "Failed to install prerequisite table entry "
          << absl::StrCat(prerequisite);
    }
  }

  // Fetch the capacity of the table.
  int capacity = static_cast<int>(table.size());
  LOG(INFO) << "Table '" << table_name << "' has advertised capacity "
            << capacity;

  // Generate entries.
  pdpi::IrTableEntries pre_capacity_entries;
  for (int i = 0; i < capacity; ++i) {
    SCOPED_TRACE(absl::StrCat("Failed to generate table entry #", i + 1));
    *pre_capacity_entries.add_entries() = generator.generator(i);
  }
  ASSIGN_OR_RETURN(pdpi::IrP4Info info, GetIrP4Info(*sut_p4rt),
                   _.SetPrepend() << "cannot install entries on switch: failed "
                                     "to pull P4Info from switch: ");
  ASSIGN_OR_RETURN(std::vector<p4::v1::TableEntry> pi_entries,
                   IrTableEntriesToPi(info, pre_capacity_entries));
  std::vector<Entity> pi_entities;
  pi_entities.reserve(pi_entries.size());
  for (const auto& pi_entry : pi_entries) {
    *pi_entities.emplace_back().mutable_table_entry() = pi_entry;
  }
  std::vector<Entity> sorted_pi_entities{pi_entities.begin(),
                                         pi_entities.end()};
  RETURN_IF_ERROR(pdpi::StableSortEntities(ir_p4info, sorted_pi_entities));

  // Install entries.
  LOG(INFO) << "Installing entries to capacity on "
            << thinkit_switch.ChassisName();
  absl::Time start = absl::Now();
  RETURN_IF_ERROR(p4_runtime::SendPiUpdates(
      sut_p4rt.get(),
      p4_runtime::CreatePiUpdates(sorted_pi_entities, Update::INSERT),
      pre_capacity_entries.entries_size() + 1))
      << "Failed to install entries to capacity";

  LOG(INFO) << "Took " << absl::Now() - start << " to install " << capacity
            << " entries into " << table_name << ".";
  return absl::OkStatus();
}

absl::StatusOr<ReadResponse> TakeP4FlowSnapshot(thinkit::Switch& sut) {
  ReadRequest read_request;
  read_request.add_entities()->mutable_table_entry();
  read_request.add_entities()->mutable_packet_replication_engine_entry();
  ASSIGN_OR_RETURN(std::unique_ptr<p4_runtime::P4RuntimeSession> session,
                   p4_runtime::P4RuntimeSession::Create(sut));
  return p4_runtime::SetMetadataAndSendPiReadRequest(session.get(),
                                                     read_request);
}

absl::Status SaveP4FlowSnapshot(ReadResponse snapshot,
                                absl::string_view file_name,
                                thinkit::TestEnvironment& env) {
  return env.StoreTestArtifact(file_name, snapshot.DebugString());
}

absl::Status StoreSutDebugArtifacts(absl::string_view prefix,
                                    thinkit::Switch& sut,
                                    thinkit::TestEnvironment& env) {
  // Implement gNMI state path validation for comparison of
  // the various state paths before and after NSF Upgrade/Reboot.
  return absl::OkStatus();
}

// TODO: Replace the AppendErrorStatus with StatusBuilder.
void AppendErrorStatus(absl::Status& ret_status, absl::Status status) {
  if (status.ok()) {
    return;
  }
  if (ret_status.ok()) {
    ret_status.Update(status);
  } else {
  }
}
}  // namespace pins_test
