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
#ifndef P4_FUZZER_ANNOTATION_UTIL_H_
#define P4_FUZZER_ANNOTATION_UTIL_H_

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_fuzzer/fuzzer.pb.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/ir_utils.h"
#include "thinkit/test_environment.h"

namespace p4_fuzzer {

// Returns an AnnotatedTableEntry.
AnnotatedTableEntry
GetAnnotatedTableEntry(const pdpi::IrP4Info &ir_p4_info,
                       const p4::v1::TableEntry &entry,
                       const std::vector<Mutation> &mutations);

// Returns an AnnotatedUpdate.
AnnotatedUpdate GetAnnotatedUpdate(const pdpi::IrP4Info &ir_p4_info,
                                   const p4::v1::Update &pi_update,
                                   const std::vector<Mutation> &mutations);

// Creates a P4Runtime WriteRequest from an AnnotatedWriteRequest.
p4::v1::WriteRequest RemoveAnnotations(const AnnotatedWriteRequest &request);

// Returns a more readable version of AnnotatedWriteRequest.
AnnotatedWriteRequest MakeReadable(AnnotatedWriteRequest request);

// Ensures that the `annotated_request` and `response` are compatible, then
// outputs each update in the `annotated_request` and its corresponding status
// response in `response` in an interleaved fashion to the artifact
// `artifact_name`. `identifying_prefix` distinguishes different calls to the
// function.
absl::Status OutputInterleavedRequestAndResponseToArtifact(
    thinkit::TestEnvironment &environment, absl::string_view artifact_name,
    absl::string_view identifying_prefix,
    const AnnotatedWriteRequest &annotated_request,
    const pdpi::IrWriteRpcStatus &response);

} // namespace p4_fuzzer

#endif // P4_FUZZER_ANNOTATION_UTIL_H_
