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
#include "lib/validator/validator_lib.h"

#include <memory>

#include "absl/memory/memory.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "grpcpp/impl/codegen/client_context.h"
#include "grpcpp/support/status.h"
#include "gutil/status.h"
#include "lib/gnmi/gnmi_helper.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "proto/gnmi/gnmi.pb.h"
#include "system/system.pb.h"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

namespace pins_test {

absl::Status Pingable(absl::string_view chassis_name, absl::Duration timeout) {
  constexpr char kPingCommand[] = R"(fping -t $0 $1; fping6 -t $0 $1)";
  FILE* in;
  char buff[1024];
  std::string pingCommand = absl::Substitute(
      kPingCommand, absl::ToInt64Seconds(timeout), chassis_name);
  if (!(in = popen(pingCommand.c_str(), "r"))) {
    return absl::UnknownError(
        absl::StrCat("Failed to run command: ", pingCommand));
  }
  std::string response;
  while (fgets(buff, sizeof(buff), in) != nullptr) {
    absl::StrAppend(&response, buff);
  }
  pclose(in);

  if (!absl::StrContains(response, "alive")) {
    return absl::UnavailableError(
        absl::StrCat("Switch ", chassis_name,
                     " is not reachable. Unexpected result: ", response));
  }
  return absl::OkStatus();
}

absl::Status Pingable(thinkit::Switch& thinkit_switch, absl::Duration timeout) {
  return Pingable(thinkit_switch.ChassisName(), timeout);
}

// The switch is SSHable if running the command "echo foo" returns "foo" in
// stdout with no errors.
absl::Status SSHable(absl::string_view chassis_name,
                     thinkit::SSHClient& ssh_client, absl::Duration timeout) {
  ASSIGN_OR_RETURN(std::string response,
                   ssh_client.RunCommand(chassis_name, "echo foo", timeout));

  if (response != "foo\n") {
    return absl::UnavailableError(
        absl::StrCat("Switch ", chassis_name,
                     " is not SSHable. Unexpected result: ", response));
  }

  return absl::OkStatus();
}

absl::Status SSHable(thinkit::Switch& thinkit_switch,
                     thinkit::SSHClient& ssh_client, absl::Duration timeout) {
  return SSHable(thinkit_switch.ChassisName(), ssh_client, timeout);
}

// Checks if a P4Runtime session could be established.
absl::Status P4rtAble(thinkit::Switch& thinkit_switch) {
  return pdpi::P4RuntimeSession::Create(thinkit_switch).status();
}

// Checks if a gNMI get all interface request can be sent and a response
// received.
absl::Status GnmiAble(thinkit::Switch& thinkit_switch, absl::Duration timeout) {
  ASSIGN_OR_RETURN(auto gnmi_stub, thinkit_switch.CreateGnmiStub());
  return pins_test::CanGetAllInterfaceOverGnmi(*gnmi_stub, timeout);
}

// Checks if a gNOI system get time request can be sent and a response
// received.
absl::Status GnoiAble(thinkit::Switch& thinkit_switch, absl::Duration timeout) {
  ASSIGN_OR_RETURN(auto gnoi_system_stub,
                   thinkit_switch.CreateGnoiSystemStub());
  gnoi::system::TimeRequest request;
  gnoi::system::TimeResponse response;
  grpc::ClientContext context;
  context.set_deadline(absl::ToChronoTime(absl::Now() + timeout));
  context.set_wait_for_ready(true);
  return gutil::GrpcStatusToAbslStatus(
      gnoi_system_stub->Time(&context, request, &response));
}

absl::Status PortsUp(thinkit::Switch& thinkit_switch,
                     absl::Span<const std::string> interfaces,
                     absl::Duration timeout) {
  ASSIGN_OR_RETURN(auto gnmi_stub, thinkit_switch.CreateGnmiStub());
  if (interfaces.empty()) {
    return pins_test::CheckAllInterfaceOperStateOverGnmi(
        *gnmi_stub, /*interface_oper_state=*/"UP",
        /*skip_non_ethernet_interfaces=*/false, timeout);
  }
  return pins_test::CheckInterfaceOperStateOverGnmi(
      *gnmi_stub, /*interface_oper_state=*/"UP", interfaces, timeout);
}

absl::Status NoAlarms(thinkit::Switch& thinkit_switch, absl::Duration timeout) {
  ASSIGN_OR_RETURN(auto gnmi_stub, thinkit_switch.CreateGnmiStub());
  ASSIGN_OR_RETURN(std::vector<std::string> alarms,
                   pins_test::GetAlarms(*gnmi_stub));
  if (alarms.empty()) {
    return absl::OkStatus();
  }
  return absl::FailedPreconditionError(
      absl::StrCat("The system has alarms set: ", absl::StrJoin(alarms, "; ")));
}

absl::Status SwitchReady(thinkit::Switch& thinkit_switch,
                         absl::Span<const std::string> interfaces,
                         absl::Duration timeout) {
  RETURN_IF_ERROR(Pingable(thinkit_switch));
  RETURN_IF_ERROR(P4rtAble(thinkit_switch));
  RETURN_IF_ERROR(GnmiAble(thinkit_switch));
  RETURN_IF_ERROR(PortsUp(thinkit_switch, interfaces));
  RETURN_IF_ERROR(GnoiAble(thinkit_switch));
  return NoAlarms(thinkit_switch);
}

absl::Status SwitchReadyWithSsh(thinkit::Switch& thinkit_switch,
                                thinkit::SSHClient& ssh_client,
                                absl::Span<const std::string> interfaces,
                                absl::Duration timeout) {
  RETURN_IF_ERROR(Pingable(thinkit_switch));
  RETURN_IF_ERROR(SSHable(thinkit_switch, ssh_client));
  RETURN_IF_ERROR(P4rtAble(thinkit_switch));
  RETURN_IF_ERROR(GnmiAble(thinkit_switch));
  RETURN_IF_ERROR(PortsUp(thinkit_switch, interfaces));
  RETURN_IF_ERROR(GnoiAble(thinkit_switch));
  return NoAlarms(thinkit_switch);
}

}  // namespace pins_test
