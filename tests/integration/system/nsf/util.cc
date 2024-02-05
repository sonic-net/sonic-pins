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

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "glog/logging.h"
#include "google/protobuf/util/message_differencer.h"
#include "grpcpp/client_context.h"
#include "gutil/overload.h"
#include "gutil/status.h"
#include "gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/utils/generic_testbed_utils.h"
#include "lib/validator/validator_lib.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "system/system.pb.h"
#include "tests/integration/system/nsf/interfaces/component_validator.h"
#include "tests/integration/system/nsf/interfaces/test_params.h"
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
using ::p4::v1::Entity;

constexpr absl::Duration kNsfRebootWaitTime = absl::Minutes(8);
constexpr absl::Duration kPollingInterval = absl::Seconds(10);
constexpr absl::Duration kTurnUpTimeout = absl::Minutes(6);
constexpr absl::Duration kTurnDownTimeout = absl::Minutes(2);

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

}  // namespace

std::vector<std::string> GetConnectedInterfacesForSut(Testbed& testbed) {
  return std::visit(
      gutil::Overload{[&](std::unique_ptr<thinkit::GenericTestbed>& testbed) {
                        return FromTestbed(GetAllConnectedInterfaces, *testbed);
                      },
                      [&](thinkit::MirrorTestbed* testbed) {
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
    absl::Status ports_up = pins_test::PortsUp(thinkit_switch, interfaces);
    LOG_IF(WARNING, !ports_up.ok()) << ports_up;
  }
  return absl::DeadlineExceededError(absl::Substitute(
      "$0 $1 state not reached after $2. Status: $3", chassis,
      GetSwitchStateString(state), elapsed_time, validator_status.message()));
}

absl::Status Reboot(RebootMethod method, Testbed& testbed) {
  LOG(INFO) << "Initiating Switch reboot. Reboot method: "
            << RebootMethod_Name(method);
  thinkit::Switch& sut = GetSut(testbed);
  ASSIGN_OR_RETURN(auto sut_gnoi_system_stub, sut.CreateGnoiSystemStub());
  RebootRequest request;
  request.set_method(method);
  request.set_message(
      absl::StrCat("Performing ", RebootMethod_Name(method), " Reboot"));
  RebootResponse response;
  ClientContext context;

  return gutil::GrpcStatusToAbslStatus(
      sut_gnoi_system_stub->Reboot(&context, request, &response));
}

void SetupTestbed(TestbedInterface& testbed_interface) {
  std::visit(
      gutil::Overload{
          [&](std::unique_ptr<thinkit::GenericTestbedInterface>& testbed) {
            return testbed->SetUp();
          },
          [&](std::unique_ptr<thinkit::MirrorTestbedInterface>& testbed) {
            return testbed->SetUp();
          }},
      testbed_interface);
}

void TearDownTestbed(TestbedInterface& testbed_interface) {
  std::visit(
      gutil::Overload{
          [&](std::unique_ptr<thinkit::GenericTestbedInterface>& testbed) {
            return testbed->TearDown();
          },
          [&](std::unique_ptr<thinkit::MirrorTestbedInterface>& testbed) {
            return testbed->TearDown();
          }},
      testbed_interface);
}

absl::StatusOr<Testbed> GetTestbed(TestbedInterface& testbed_interface) {
  return std::visit(
      gutil::Overload{
          [&](std::unique_ptr<thinkit::GenericTestbedInterface>& testbed)
              -> absl::StatusOr<Testbed> {
            // Pick a testbed with SUT connected to a traffic generator, be it a
            // software (eg. on a host) or a hardware (eg. Ixia), on 2 ports,
            // one ingress and one egress port.
            auto requirements =
                gutil::ParseProtoOrDie<thinkit::TestRequirements>(
                    R"pb(
                      interface_requirements {
                        count: 2
                        interface_mode: TRAFFIC_GENERATOR
                      }
                    )pb");
            return testbed->GetTestbedWithRequirements(requirements);
          },
          [&](std::unique_ptr<thinkit::MirrorTestbedInterface>& testbed)
              -> absl::StatusOr<Testbed> {
            return &testbed->GetMirrorTestbed();
          }},
      testbed_interface);
}

thinkit::Switch& GetSut(Testbed& testbed) {
  return std::visit(
      gutil::Overload{[&](std::unique_ptr<thinkit::GenericTestbed>& testbed)
                          -> thinkit::Switch& { return testbed->Sut(); },
                      [&](thinkit::MirrorTestbed* testbed) -> thinkit::Switch& {
                        return testbed->Sut();
                      }},
      testbed);
}

absl::StatusOr<std::string> ImageCopy(const std::string& image_label,
                                      Testbed& testbed,
                                      thinkit::SSHClient& ssh_client) {
  return "";
}

absl::Status InstallRebootPushConfig(
    const ImageConfigParams& image_config_param, Testbed& testbed,
    thinkit::SSHClient& ssh_client) {
  LOG(INFO) << "gNOI Install: Copying image to inactive partition";
  ASSIGN_OR_RETURN(
      std::string image_version,
      ImageCopy(image_config_param.image_label, testbed, ssh_client));

  RETURN_IF_ERROR(Reboot(RebootMethod::COLD, testbed));

  thinkit::Switch& sut = GetSut(testbed);
  ASSIGN_OR_RETURN(auto sut_gnoi_os_stub, sut.CreateGnoiOsStub());

  // Wait for SSH and containers to be up before pushing config.
  RETURN_IF_ERROR(WaitForReboot(testbed, ssh_client, false));

  RETURN_IF_ERROR(PushConfig(image_config_param, testbed, ssh_client));
  LOG(INFO) << "Initial setup of image install, cold reboot and config push is "
               "complete.";
  return absl::OkStatus();
}

absl::Status
ValidateTestbedState(absl::string_view version, Testbed &testbed,
                     thinkit::SSHClient &ssh_client,
                     const std::optional<absl::string_view> &gnmi_config) {
  LOG(INFO) << "Validating SUT state";
  thinkit::Switch& sut = GetSut(testbed);
  absl::Status sut_status = RunReadyValidations(
      sut, ssh_client, GetConnectedInterfacesForSut(testbed),
      /*check_interfaces_state=*/true,
      /*with_healthz=*/true);

  return std::visit(
      gutil::Overload{[&](std::unique_ptr<thinkit::GenericTestbed> &testbed) {
                        return sut_status;
                      },
                      [&](thinkit::MirrorTestbed *testbed) -> absl::Status {
                        absl::Status control_status;
                        if (!testbed->ControlSwitch().ChassisName().empty()) {
                          control_status = RunReadyValidations(
                              testbed->ControlSwitch(), ssh_client,
                              testbed->GetConnectedInterfaces(),
                              /*check_interfaces_state=*/true,
                              /*with_healthz=*/true);
                        }
                        RETURN_IF_ERROR(sut_status);
                        return control_status;
                      }},
      testbed);
}

absl::Status ValidateComponents(
    absl::Status (ComponentValidator::*validate)(absl::string_view, Testbed&),
    const absl::Span<const std::unique_ptr<ComponentValidator>> validators,
    absl::string_view version, Testbed& testbed) {
  for (const std::unique_ptr<ComponentValidator>& validator : validators) {
    RETURN_IF_ERROR((std::invoke(validate, validator, version, testbed)));
  }
  return absl::OkStatus();
}

absl::Status NsfReboot(Testbed& testbed) {
  return Reboot(RebootMethod::NSF, testbed);
}

absl::Status WaitForReboot(Testbed& testbed, thinkit::SSHClient& ssh_client,
                           bool check_interfaces_up) {
  LOG(INFO) << "Waiting for switch to go down and come back up";
  // Wait for switch to go down and come back up.
  thinkit::Switch& sut = GetSut(testbed);

  RETURN_IF_ERROR(WaitForSwitchState(sut, SwitchState::kDown, kTurnDownTimeout,
                                     ssh_client));
  return WaitForSwitchState(
      sut,
      check_interfaces_up ? SwitchState::kReady
                          : SwitchState::kReadyWithoutInterfacesUp,
      kTurnUpTimeout, ssh_client, GetConnectedInterfacesForSut(testbed));
}

absl::Status WaitForNsfReboot(Testbed& testbed, thinkit::SSHClient& ssh_client,
                              bool check_interfaces_up) {
  LOG(INFO) << "Waiting for switch to go down and come back up post NSF reboot";
  // Wait for switch to do NSF reboot.
  thinkit::Switch& sut = GetSut(testbed);
  absl::Time start_time = absl::Now();
  ASSIGN_OR_RETURN(auto sut_gnoi_system_stub, sut.CreateGnoiSystemStub());
  // Start polling to check for NSF reboot completion.
  while (absl::Now() < (start_time + kNsfRebootWaitTime)) {
    absl::SleepFor(kPollingInterval);
    ClientContext context;
    RebootStatusRequest req;
    RebootStatusResponse resp;
    // Invoke the RPC and validate the results.
    grpc::Status reboot_status =
        sut_gnoi_system_stub->RebootStatus(&context, req, &resp);
    // If the RPC fails or the NSF reboot is still active, continue to
    // poll.
    if (!reboot_status.ok() || resp.active()) {
      LOG(WARNING) << "Reboot Status: " << reboot_status.error_message();
      LOG(WARNING) << "Reboot Status Response: " << resp.DebugString();
      continue;
    }
    LOG(INFO) << "NSF Reboot succeeded: " << resp.DebugString()
              << "\nProceeding with Switch State Validation.";
    return RunReadyValidations(sut, ssh_client,
                               GetConnectedInterfacesForSut(testbed),
                               /*check_interfaces_state=*/check_interfaces_up,
                               /*with_healthz=*/true);
  }
  return gutil::InternalErrorBuilder()
         << "NSF Reboot validation failed after polling for "
         << absl::FormatDuration(kNsfRebootWaitTime) << " .";
}

absl::Status PushConfig(const ImageConfigParams& image_config_param,
                        Testbed& testbed, thinkit::SSHClient& ssh_client) {
  // Push Config.
  thinkit::Switch& sut = GetSut(testbed);
  LOG(INFO) << "Pushing config on " << sut.ChassisName();
  ASSIGN_OR_RETURN(
      std::unique_ptr<pdpi::P4RuntimeSession> p4rt_session,
      pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
          sut, image_config_param.gnmi_config, image_config_param.p4_info));

  LOG(INFO) << "Verifying config push on " << sut.ChassisName();
  return WaitForSwitchState(sut, SwitchState::kReady, kTurnUpTimeout,
                            ssh_client, GetConnectedInterfacesForSut(testbed));
}

absl::StatusOr<std::vector<Entity>> TakeP4FlowSnapshot(Testbed& testbed) {
  thinkit::Switch& sut = GetSut(testbed);
  ASSIGN_OR_RETURN(std::unique_ptr<pdpi::P4RuntimeSession> session,
                   pdpi::P4RuntimeSession::Create(sut));
  return pdpi::ReadPiEntities(session.get());
}

absl::Status CompareP4FlowSnapshots(absl::Span<const Entity> a,
                                    absl::Span<const Entity> b) {
  MessageDifferencer differencer;
  size_t iterations = std::max(a.size(), b.size());
  std::vector<std::string> differences;
  differences.reserve(iterations);
  for (int i = 0; i < iterations; ++i) {
    std::string diff;
    differencer.ReportDifferencesToString(&diff);
    const Entity& a_entity = a.size() > i ? a[i] : Entity();
    const Entity& b_entity = b.size() > i ? b[i] : Entity();
    if (!differencer.Compare(a[i], b[i])) {
      differences.push_back(std::move(diff));
    }
  }

  if (differences.empty()) return absl::OkStatus();
  return gutil::InternalErrorBuilder()
         << "Differences found between the P4 flow snapshots:\n"
         << absl::StrJoin(differences, "\n");
}

absl::Status StoreSutDebugArtifacts(absl::string_view prefix,
                                    Testbed& testbed) {
  return absl::OkStatus();
}

}  // namespace pins_test
