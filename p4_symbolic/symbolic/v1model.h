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

#ifndef P4_SYMBOLIC_SYMBOLIC_V1MODEL_H_
#define P4_SYMBOLIC_SYMBOLIC_V1MODEL_H_

#include <vector>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/context.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "z3++.h"

namespace p4_symbolic::symbolic::v1model {

// The bitwdith of the `standard_metadata.mcast_grp` field in V1Model.
static constexpr int kMcastGrpBitwidth = 16;

// Standard metadata header name.
constexpr absl::string_view kStandardMetadataHeaderName = "standard_metadata";

// 32-bit bit-vector field in standard metadata indicating whether there is a
// parser error. The error code is defined in core.p4 and can be extended by the
// P4 program. 0 means no error.
constexpr absl::string_view kParserErrorField =
    "standard_metadata.parser_error";

// V1model's `mark_to_drop` primitive sets the `egress_spec` field to
// `kDropPort` to indicate the packet should be dropped at the end of
// ingress/egress processing. See v1model.p4 for details.
z3::expr EgressSpecDroppedValue(z3::context &z3_context);

// Initializes the ingress headers to appropriate values.
// Here we initialize all standard metadata fields to zero for the ingress
// packet. Local (user) metadata fields are intentionally left uninitialized
// to align with the standard.
absl::Status InitializeIngressHeaders(const ir::P4Program &program,
                                      SymbolicPerPacketState &ingress_headers,
                                      z3::context &z3_context);

// Symbolically evaluates the parser, ingress, and egress pipelines of the given
// P4 program with the given entries, assuming the program is written against V1
// model.
absl::Status EvaluateV1model(SolverState &state,
                             const std::vector<int> &physical_ports);

}  // namespace p4_symbolic::symbolic::v1model

#endif  // P4_SYMBOLIC_SYMBOLIC_V1MODEL_H_
