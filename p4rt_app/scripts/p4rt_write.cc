// Copyright 2022 Google LLC
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
#include <iostream>
#include <string>

#include "absl/flags/flag.h"
#include "absl/flags/parse.h"
#include "absl/log/initialize.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_format.h"
#include "grpcpp/client_context.h"
#include "grpcpp/security/credentials.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_runtime/p4_runtime_session.h"
#include "p4rt_app/scripts/p4rt_tool_helpers.h"

// Flags to write table updates.
ABSL_FLAG(std::string, ir_write_request_file, "",
          "Reads a pdpi::IrWriteRequest from a file and sends it to the "
          "P4RT service.");
ABSL_FLAG(bool, force_delete, false, "Forces all write reqests to be deletes.");

namespace p4rt_app {
namespace {

absl::StatusOr<pdpi::IrP4Info> GetIrP4infoFromSwitch(
    p4_runtime::P4RuntimeSession& session) {
  ASSIGN_OR_RETURN(p4::v1::GetForwardingPipelineConfigResponse response,
                   p4_runtime::GetForwardingPipelineConfig(&session));
  return pdpi::CreateIrP4Info(response.config().p4info());
}

absl::StatusOr<p4::v1::WriteRequest> GetPiWriteRequest(
    const pdpi::IrP4Info& ir_p4info) {
  std::string ir_write_request_file =
      absl::GetFlag(FLAGS_ir_write_request_file);

  if (!ir_write_request_file.empty()) {
    pdpi::IrWriteRequest ir_write_request;
    RETURN_IF_ERROR(
        gutil::ReadProtoFromFile(ir_write_request_file, &ir_write_request));
    return pdpi::IrWriteRequestToPi(ir_p4info, ir_write_request);
  }

  return gutil::InvalidArgumentErrorBuilder()
         << "No write request was selected.";
}

absl::Status SendWriteRequest(p4_runtime::P4RuntimeSession& session,
                              p4::v1::WriteRequest pi_write_request) {
  pi_write_request.set_device_id(session.DeviceId());
  *pi_write_request.mutable_election_id() = session.ElectionId();
  pi_write_request.set_role(session.Role());

  return session.Write(pi_write_request);
}

absl::Status Main() {
  // Connect to the P4RT server.
  ASSIGN_OR_RETURN(std::unique_ptr<p4_runtime::P4RuntimeSession> session,
                   CreateP4rtSession());

  // Before we can handle any requests we need to get the P4Info, and convert it
  // to an IR.
  ASSIGN_OR_RETURN(pdpi::IrP4Info ir_p4info, GetIrP4infoFromSwitch(*session));

  // Create the write request.
  ASSIGN_OR_RETURN(p4::v1::WriteRequest pi_write_request,
                   GetPiWriteRequest(ir_p4info));

  // If the user asks us to force a delete then we will change all the request
  // types to DELETE. In addition we also reverse the order of the requests.
  if (absl::GetFlag(FLAGS_force_delete)) {
    p4::v1::WriteRequest reversed_write_request;
    for (auto iter = pi_write_request.updates().rbegin();
         iter != pi_write_request.updates().rend(); ++iter) {
      auto* update = reversed_write_request.add_updates();
      *update = *iter;
      update->set_type(p4::v1::Update::DELETE);
    }
    Warning(
        "Reversing the order of write requests because of the --force_delete "
        "flag.");
    std::swap(pi_write_request, reversed_write_request);
  }

  // Finally, send the write request.
  return SendWriteRequest(*session, pi_write_request);
}

}  // namespace
}  // namespace p4rt_app

int main(int argc, char** argv) {
  absl::InitializeLog();
  absl::ParseCommandLine(argc, argv);

  absl::Status status = p4rt_app::Main();
  if (!status.ok()) {
    p4rt_app::Error(status.ToString());
    return status.raw_code();
  }

  p4rt_app::Info("Completed successfully.");
  return 0;
}
