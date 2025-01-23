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

#include <functional>
#include <memory>
#include <string>
#include <variant>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "glog/logging.h"
#include "grpcpp/client_context.h"
#include "gutil/overload.h"
#include "gutil/status.h"
#include "gutil/testing.h"
#include "lib/utils/generic_testbed_utils.h"
#include "lib/validator/validator_lib.h"
#include "p4/config/v1/p4info.pb.h"
#include "tests/integration/system/nsf/interfaces/component_validator.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/generic_testbed_fixture.h"
#include "thinkit/mirror_testbed_fixture.h"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

namespace pins_test {
namespace {

using ::p4::v1::ReadResponse;

constexpr absl::Duration kTurnUpTimeout = absl::Minutes(6);
constexpr absl::Duration kTurnDownTimeout = absl::Minutes(2);

// State of the switch.
enum class SwitchState { kUp, kDown, kReady, kReadyWithoutInterfacesUp };
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

// Returns the list of connected interfaces for the SUT.
std::vector<std::string> GetConnectedInterfacesForSut(
    thinkit::GenericTestbed& testbed) {
  return GetSutInterfaces(FromTestbed(GetAllControlLinks, testbed));
}

// Runs validations that validate the switch to be ready. Does the switch
// respond over: ping, SSH, P4, gNMI, gNOI.
absl::Status RunReadyValidations(thinkit::Switch& thinkit_switch,
                                 thinkit::SSHClient& ssh_client,
                                 absl::Span<const std::string> interfaces = {},
                                 bool check_interfaces_state = true,
                                 bool with_healthz = true) {
  RETURN_IF_ERROR(SwitchReadyWithSsh(thinkit_switch, ssh_client, interfaces,
                                     check_interfaces_state, with_healthz));

  return absl::OkStatus();
}

// Waits for a target switch to be up or down based on the state provided.
absl::Status WaitForSwitchState(thinkit::Switch& thinkit_switch,
                                SwitchState state, absl::Duration timeout,
                                thinkit::SSHClient& ssh_client,
                                absl::Span<const std::string> interfaces = {}) {
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

}  // namespace

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
            return absl::UnimplementedError(
                "MirrorTestbedInterface not implemented");
          }},
      testbed_interface);
}

absl::Status InstallRebootPushConfig(absl::string_view version) {
  return absl::OkStatus();
}

absl::Status ValidateSutState(absl::string_view version,
                              thinkit::GenericTestbed& testbed,
                              thinkit::SSHClient& ssh_client) {
  return RunReadyValidations(testbed.Sut(), ssh_client,
                             GetConnectedInterfacesForSut(testbed),
                             /*check_interfaces_state=*/true,
                             /*with_healthz=*/true);
}

absl::Status ValidateComponents(
    absl::Status (ComponentValidator::*validate)(absl::string_view,
                                                 thinkit::GenericTestbed&),
    const absl::Span<const std::unique_ptr<ComponentValidator>> validators,
    absl::string_view version, thinkit::GenericTestbed& testbed) {
  for (const std::unique_ptr<ComponentValidator>& validator : validators) {
    RETURN_IF_ERROR((std::invoke(validate, validator, version, testbed)));
  }
  return absl::OkStatus();
}

absl::Status Upgrade(absl::string_view version) { return absl::OkStatus(); }

absl::Status NsfReboot(thinkit::GenericTestbed& testbed,
                       thinkit::SSHClient& ssh_client) {
  ASSIGN_OR_RETURN(auto sut_gnoi_system_stub,
                   testbed.Sut().CreateGnoiSystemStub());
  gnoi::system::RebootRequest gnoi_request;
  gnoi_request.set_method(gnoi::system::RebootMethod::NSF);
  gnoi_request.set_message("Performing NSF Reboot");
  gnoi::system::RebootResponse gnoi_response;
  grpc::ClientContext grpc_context;

  return gutil::GrpcStatusToAbslStatus(sut_gnoi_system_stub->Reboot(
      &grpc_context, gnoi_request, &gnoi_response));
}

absl::Status WaitForReboot(thinkit::GenericTestbed& testbed,
                           thinkit::SSHClient& ssh_client) {
  // Wait for switch to go down and come back up.
  RETURN_IF_ERROR(WaitForSwitchState(testbed.Sut(), SwitchState::kDown,
                                     kTurnDownTimeout, ssh_client));

  return WaitForSwitchState(testbed.Sut(), SwitchState::kReady, kTurnUpTimeout,
                            ssh_client, GetConnectedInterfacesForSut(testbed));
}

absl::Status PushConfig(absl::string_view version) { return absl::OkStatus(); }

ReadResponse TakeP4FlowSnapshot() { return ReadResponse(); }

absl::Status CompareP4FlowSnapshots(const ReadResponse& a,
                                    const ReadResponse& b) {
  return absl::OkStatus();
}

absl::Status CaptureDbState() { return absl::OkStatus(); }

absl::Status ValidateDbState() { return absl::OkStatus(); }

}  // namespace pins_test
