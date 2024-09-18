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
#include "p4_fuzzer/annotation_util.h"

#include <vector>

#include "absl/log/check.h"
#include "absl/log/log.h"
#include "gutil/gutil/status.h"
#include "p4_fuzzer/fuzzer.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "thinkit/test_environment.h"

namespace p4_fuzzer {

AnnotatedTableEntry GetAnnotatedTableEntry(
    const pdpi::IrP4Info& ir_p4_info, const p4::v1::TableEntry& entry,
    const std::vector<Mutation>& mutations) {
  AnnotatedTableEntry debug_entry;
  *debug_entry.mutable_pi() = entry;

  auto status_or_ir = pdpi::PiTableEntryToIr(ir_p4_info, entry);

  if (!status_or_ir.ok()) {
    debug_entry.set_error(status_or_ir.status().ToString());
  } else {
    *debug_entry.mutable_ir() = status_or_ir.value();
  }

  for (const auto& mutation : mutations) {
    debug_entry.add_mutations(mutation);
  }

  return debug_entry;
}

AnnotatedUpdate GetAnnotatedUpdate(const pdpi::IrP4Info& ir_p4_info,
                                   const p4::v1::Update& pi_update,
                                   const std::vector<Mutation>& mutations) {
  AnnotatedUpdate update;
  *update.mutable_pi() = pi_update;

  auto ir = pdpi::PiUpdateToIr(ir_p4_info, pi_update);

  if (!ir.ok()) {
    update.set_error(ir.status().ToString());
  } else {
    *update.mutable_ir() = ir.value();
    // TODO: Converting from Ir back to Pi produces a canonical
    // encoding for the pi update. Fuzzer is limited to canonical encodings
    // until cache bug on switch is fixed.
    auto canonicalized_pi = pdpi::IrUpdateToPi(ir_p4_info, ir.value());
    CHECK(canonicalized_pi.status().ok())  // Crash OK
        << "Internal error: PDPI an IR that could not be translated back to PI";
    *update.mutable_pi() = *canonicalized_pi;
  }

  for (const auto& mutation : mutations) {
    update.add_mutations(mutation);
  }

  return update;
}

p4::v1::WriteRequest RemoveAnnotations(const AnnotatedWriteRequest& request) {
  p4::v1::WriteRequest base_request;

  base_request.set_device_id(request.device_id());
  *base_request.mutable_election_id() = request.election_id();

  for (const auto& update : request.updates()) {
    *base_request.add_updates() = update.pi();
  }

  return base_request;
}

AnnotatedWriteRequest MakeReadable(AnnotatedWriteRequest request) {
  for (auto& update : *request.mutable_updates()) {
    // Only keep IR if available.
    if (update.has_ir()) update.clear_pi();
  }
  return request;
}

absl::Status OutputInterleavedRequestAndResponseToArtifact(
    thinkit::TestEnvironment& environment, absl::string_view artifact_name,
    absl::string_view identifying_prefix,
    const AnnotatedWriteRequest& annotated_request,
    const pdpi::IrWriteRpcStatus& response) {
  // If there is an RPC-wide error, then there are no individual statuses.
  if (!response.has_rpc_response()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Expected individual update statuses in response, but got: "
           << response.DebugString();
  }

  if (response.rpc_response().statuses().size() !=
      annotated_request.updates_size()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Expected number of responses to equal number of updates, but "
              "they differed. Number of updates was "
           << annotated_request.updates_size()
           << " while number of responses was "
           << response.rpc_response().statuses().size()
           << "\n Updates: " << annotated_request.DebugString()
           << "\n Responses: " << response.DebugString();
  }

  RETURN_IF_ERROR(environment.AppendToTestArtifact(
      artifact_name,
      absl::StrCat("############################################\n",
                   "# Write Request and Response for ", identifying_prefix,
                   "\n", "############################################\n\n")));

  AnnotatedWriteRequest readable_annotated_request =
      MakeReadable(annotated_request);
  for (int update_num = 0; update_num < annotated_request.updates_size();
       update_num++) {
    RETURN_IF_ERROR(environment.AppendToTestArtifact(
        artifact_name,
        absl::StrCat(
            "--- ", identifying_prefix, ": Update ", update_num + 1,
            " ----------------------------\n",
            readable_annotated_request.updates(update_num).DebugString(), "\n",
            "--- ", identifying_prefix, ": Response ", update_num + 1,
            " --------------------------\n",
            (response.rpc_response().statuses(update_num).code() ==
                     google::rpc::Code::OK
                 ? "Update accepted by switch.\n"
                 : absl::StrCat(
                       Code_Name(
                           response.rpc_response().statuses(update_num).code()),
                       "\n",
                       response.rpc_response().statuses(update_num).message(),
                       "\n")),
            "\n")));
  }
  return absl::OkStatus();
}
}  // namespace p4_fuzzer
