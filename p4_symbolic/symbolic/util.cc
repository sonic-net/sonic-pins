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

// Helpful utilities for managing symbolic and concrete headers and values.

#include "p4_symbolic/symbolic/util.h"

#include <string>

#include "absl/strings/str_format.h"
#include "p4_pdpi/utils/ir.h"
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/symbolic/packet.h"

namespace p4_symbolic {
namespace symbolic {
namespace util {

namespace {

bool Z3BooltoBool(Z3_lbool z3_bool) {
  switch (z3_bool) {
    case Z3_L_TRUE:
      return true;
    default:
      return false;
  }
}

}  // namespace

absl::StatusOr<std::unordered_map<std::string, z3::expr>> FreeSymbolicHeaders(
    const google::protobuf::Map<std::string, ir::HeaderType> &headers) {
  // Loop over every header instance in the p4 program.
  // Find its type, and loop over every field in it, creating a symbolic free
  // variable for every field in every header instance.
  std::unordered_map<std::string, z3::expr> symbolic_headers;
  for (const auto &[header_name, header_type] : headers) {
    // Special validity field.
    std::string valid_field_name = absl::StrFormat("%s.$valid$", header_name);
    z3::expr valid_expression =
        Z3Context().bool_const(valid_field_name.c_str());
    symbolic_headers.insert({valid_field_name, valid_expression});

    // Regular fields defined in the p4 program or v1model.
    for (const auto &[field_name, field] : header_type.fields()) {
      if (field.signed_()) {
        return absl::UnimplementedError(
            "Negative header fields are not supported");
      }

      std::string field_full_name =
          absl::StrFormat("%s.%s", header_name, field_name);
      z3::expr field_expression =
          Z3Context().bv_const(field_full_name.c_str(), field.bitwidth());
      symbolic_headers.insert({field_full_name, field_expression});
    }
  }

  // Finally, we have a special field marking if the packet represented by
  // these headers was dropped.
  symbolic_headers.insert({"$dropped$", Z3Context().bool_val(false)});
  return symbolic_headers;
}

SymbolicTableMatch DefaultTableMatch() {
  return {
      Z3Context().bool_val(false),  // No match yet!
      Z3Context().int_val(-1)       // No match index.
  };
}

absl::StatusOr<ConcreteContext> ExtractFromModel(
    SymbolicContext context, z3::model model,
    const values::P4RuntimeTranslator &translator) {
  // Extract ports.
  std::string ingress_port = model.eval(context.ingress_port, true).to_string();
  std::string egress_port = model.eval(context.egress_port, true).to_string();

  // Extract an input packet and its predicted output.
  ConcretePacket ingress_packet =
      packet::ExtractConcretePacket(context.ingress_packet, model);
  ConcretePacket egress_packet =
      packet::ExtractConcretePacket(context.egress_packet, model);

  // Extract the ingress and egress headers.
  ConcretePerPacketState ingress_headers;
  for (const auto &[name, expr] : context.ingress_headers) {
    ASSIGN_OR_RETURN(ingress_headers[name],
                     values::TranslateValueToP4RT(
                         name, model.eval(expr, true).to_string(), translator));
  }
  ConcretePerPacketState egress_headers;
  for (const auto &[name, expr] : context.egress_headers) {
    ASSIGN_OR_RETURN(egress_headers[name],
                     values::TranslateValueToP4RT(
                         name, model.eval(expr, true).to_string(), translator));
  }

  // Extract the trace (matches on every table).
  bool dropped =
      Z3BooltoBool(model.eval(context.trace.dropped, true).bool_value());
  std::unordered_map<std::string, ConcreteTableMatch> matches;
  for (const auto &[table, match] : context.trace.matched_entries) {
    matches[table] = {
        Z3BooltoBool(model.eval(match.matched, true).bool_value()),
        model.eval(match.entry_index, true).get_numeral_int()};
  }
  ConcreteTrace trace = {matches, dropped};

  return ConcreteContext{ingress_port,  egress_port,     ingress_packet,
                         egress_packet, ingress_headers, egress_headers,
                         trace};
}

absl::StatusOr<SymbolicTrace> MergeTracesOnCondition(
    const z3::expr &condition, const SymbolicTrace &true_trace,
    const SymbolicTrace &false_trace) {
  ASSIGN_OR_RETURN(
      z3::expr merged_dropped,
      operators::Ite(condition, true_trace.dropped, false_trace.dropped));

  // The merged trace is initially empty.
  SymbolicTrace merged = {{}, merged_dropped};

  // Merge all tables matches in true_trace (including ones in both traces).
  for (const auto &[name, true_match] : true_trace.matched_entries) {
    // Find match in other trace (or use default).
    SymbolicTableMatch false_match = DefaultTableMatch();
    if (false_trace.matched_entries.count(name) > 0) {
      false_match = false_trace.matched_entries.at(name);
    }

    // Merge this match.
    ASSIGN_OR_RETURN(
        z3::expr matched,
        operators::Ite(condition, true_match.matched, false_match.matched));
    ASSIGN_OR_RETURN(z3::expr index,
                     operators::Ite(condition, true_match.entry_index,
                                    false_match.entry_index));
    merged.matched_entries.insert({name, {matched, index}});
  }

  // Merge all tables matches in false_trace only.
  for (const auto &[name, false_match] : false_trace.matched_entries) {
    SymbolicTableMatch true_match = DefaultTableMatch();
    if (true_trace.matched_entries.count(name) > 0) {
      continue;  // Already covered.
    }

    // Merge this match.
    ASSIGN_OR_RETURN(
        z3::expr matched,
        operators::Ite(condition, true_match.matched, false_match.matched));
    ASSIGN_OR_RETURN(z3::expr index,
                     operators::Ite(condition, true_match.entry_index,
                                    false_match.entry_index));
    merged.matched_entries.insert({name, {matched, index}});
  }

  return merged;
}

}  // namespace util
}  // namespace symbolic
}  // namespace p4_symbolic
