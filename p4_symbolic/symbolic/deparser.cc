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

#include "p4_symbolic/symbolic/deparser.h"

#include <optional>
#include <string>

#include "absl/status/statusor.h"
#include "google/protobuf/repeated_ptr_field.h"
#include "gutil/gutil/status.h"
#include "p4_infra/string_encodings/bit_string.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/context.h"
#include "p4_symbolic/symbolic/solver_state.h"
#include "p4_symbolic/z3_util.h"
#include "z3++.h"

namespace p4_symbolic {

namespace {

// Deparses the given symbolic `packet` into a byte string, using values
// according to the given `model`, with the given `header_order`.
absl::StatusOr<std::string> Deparse(
    const symbolic::SymbolicPerPacketState& packet, const z3::model& model,
    const ::google::protobuf::RepeatedPtrField<std::string>& header_order,
    const ::google::protobuf::Map<std::string, ir::HeaderType>& headers) {
  string_encodings::BitString result;

  // Serialize each header to the bit-string from the outermost one to the
  // innermost one.
  for (const std::string& header_name : header_order) {
    // The header specified in the header order must exist in the program.
    auto it = headers.find(header_name);
    if (it == headers.end()) {
      return gutil::NotFoundErrorBuilder()
             << "Header not found during deparsing: " << header_name;
    }

    // Obtain the valid field of the header. Skip serializing the header if it's
    // not valid.
    ASSIGN_OR_RETURN(z3::expr valid_expr,
                     packet.Get(header_name, symbolic::kValidPseudoField));
    ASSIGN_OR_RETURN(bool valid, EvalZ3Bool(valid_expr, model));
    if (!valid) continue;

    const ir::HeaderType& header_type = it->second;

    // Serialize each field within the header to the bit-string.
    for (const std::string& field_name : header_type.ordered_fields_list()) {
      ASSIGN_OR_RETURN(z3::expr field_expr,
                       packet.Get(header_name, field_name));
      if (!field_expr.is_bv()) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Header field '" << header_name << "." << field_name
               << "' is not a bit-vector: " << field_expr;
      }

      // Evaluate the concrete value of the field given the model.
      RETURN_IF_ERROR(
          EvalAndAppendZ3BitvectorToBitString(result, field_expr, model));
    }
  }

  return result.ToByteString();
}

}  // namespace

absl::StatusOr<std::string> DeparseIngressPacket(
    const symbolic::SolverState& state, const z3::model& model,
    std::optional<symbolic::SymbolicPerPacketState> headers) {
  // TODO: We are using the deparser header order to serialize
  // ingress packet for now. In the future, we may want to infer parser header
  // order and use that for ingress packets.
  const ir::Deparser& deparser = state.program.deparsers().begin()->second;
  if (headers.has_value())
    return Deparse(headers.value(), model, deparser.header_order(),
                   state.program.headers());
  else
    return Deparse(state.context.ingress_headers, model,
                   deparser.header_order(), state.program.headers());
}

absl::StatusOr<std::string> DeparseEgressPacket(
    const symbolic::SolverState& state, const z3::model& model) {
  const ir::Deparser& deparser = state.program.deparsers().begin()->second;
  return Deparse(state.context.egress_headers, model, deparser.header_order(),
                 state.program.headers());
}

}  // namespace p4_symbolic
