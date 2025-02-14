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

#include <cstdint>
#include <functional>
#include <memory>
#include <string>
#include <utility>
#include <variant>
#include <vector>

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
#include "lib/gnmi/gnmi_helper.h"
#include "lib/utils/generic_testbed_utils.h"
#include "lib/validator/validator_lib.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "tests/integration/system/nsf/interfaces/component_validator.h"
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
using ::grpc::ClientContext;
using ::p4::config::v1::P4Info;
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

// Reboot the SUT using the given reboot `method`.
absl::Status Reboot(RebootMethod method, Testbed& testbed) {
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
            return absl::UnimplementedError("MirrorTestbed not implemented");
          }},
      testbed_interface);
}

thinkit::Switch& GetSut(Testbed& testbed) {
  return std::visit(
      gutil::Overload{[&](std::unique_ptr<thinkit::GenericTestbed>& testbed)
                          -> thinkit::Switch& { return testbed->Sut(); },
                      [&](std::unique_ptr<thinkit::MirrorTestbed>& testbed)
                          -> thinkit::Switch& { return testbed->Sut(); }},
      testbed);
}

absl::StatusOr<std::string> ImageCopy(const std::string& image_label,
                                      Testbed& testbed,
                                      thinkit::SSHClient& ssh_client) {
  return "";
}

absl::Status InstallRebootPushConfig(const std::string& image_label,
                                     const std::string& gnmi_config,
                                     const P4Info& p4info, Testbed& testbed,
                                     thinkit::SSHClient& ssh_client) {
  ASSIGN_OR_RETURN(std::string image_version,
                   ImageCopy(image_label, testbed, ssh_client));

  RETURN_IF_ERROR(Reboot(RebootMethod::COLD, testbed));

  thinkit::Switch& sut = GetSut(testbed);
  ASSIGN_OR_RETURN(auto sut_gnoi_os_stub, sut.CreateGnoiOsStub());

  // Wait for SSH and containers to be up before pushing config.
  RETURN_IF_ERROR(WaitForReboot(testbed, ssh_client, false));

  return PushConfig(gnmi_config, p4info, testbed, ssh_client);
}

absl::Status ValidateSutState(absl::string_view version, Testbed& testbed,
                              thinkit::SSHClient& ssh_client) {
  return std::visit(
      gutil::Overload{
          [&](std::unique_ptr<thinkit::GenericTestbed>& testbed) {
            return RunReadyValidations(testbed->Sut(), ssh_client,
                                       GetConnectedInterfacesForSut(*testbed),
                                       /*check_interfaces_state=*/true,
                                       /*with_healthz=*/true);
          },
          [&](std::unique_ptr<thinkit::MirrorTestbed>& testbed) {
            // TODO: Implement RunReadyValidations for Mirror
            // testbed scenario.
            return absl::UnimplementedError("MirrorTestbed not implemented");
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
  // Wait for switch to go down and come back up.
  thinkit::Switch& sut = GetSut(testbed);

  return std::visit(
      gutil::Overload{
          [&](std::unique_ptr<thinkit::GenericTestbed>& testbed)
              -> absl::Status {
            RETURN_IF_ERROR(WaitForSwitchState(sut, SwitchState::kDown,
                                               kTurnDownTimeout, ssh_client));

            return WaitForSwitchState(
                sut,
                check_interfaces_up ? SwitchState::kReady
                                    : SwitchState::kReadyWithoutInterfacesUp,
                kTurnUpTimeout, ssh_client,
                GetConnectedInterfacesForSut(*testbed));
          },
          [&](std::unique_ptr<thinkit::MirrorTestbed>& testbed)
              -> absl::Status {
            return absl::UnimplementedError("MirrorTestbed not implemented");
          }},
      testbed);
}

absl::Status PushConfig(const std::string& gnmi_config, const P4Info& p4info,
                        Testbed& testbed, thinkit::SSHClient& ssh_client) {
  std::vector<std::string> interfaces;
  RETURN_IF_ERROR(std::visit(
      gutil::Overload{
          [&interfaces](std::unique_ptr<thinkit::GenericTestbed>& testbed)
              -> absl::Status {
            interfaces = GetConnectedInterfacesForSut(*testbed);
            return absl::OkStatus();
          },
          [&](std::unique_ptr<thinkit::MirrorTestbed>& testbed)
              -> absl::Status {
            return absl::UnimplementedError("MirrorTestbed not implemented");
          }},
      testbed));

  // Push Config.
  thinkit::Switch& sut = GetSut(testbed);
  ASSIGN_OR_RETURN(std::unique_ptr<pdpi::P4RuntimeSession> p4rt_session,
                   pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
                       sut, gnmi_config, p4info));

  LOG(INFO) << "Verifying config push on " << sut.ChassisName();
  return WaitForSwitchState(sut, SwitchState::kReady, kTurnUpTimeout,
                            ssh_client, interfaces);
}

ReadResponse TakeP4FlowSnapshot() { return ReadResponse(); }

absl::Status CompareP4FlowSnapshots(const ReadResponse& a,
                                    const ReadResponse& b) {
  return absl::OkStatus();
}

absl::Status StoreSutDebugArtifacts(absl::string_view prefix,
                                    Testbed& testbed) {
  return absl::OkStatus();
}

}  // namespace pins_test
