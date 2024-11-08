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

#include "absl/status/status.h"
#include "absl/strings/str_format.h"
#include "absl/strings/substitute.h"
#include "p4_pdpi/utils/ir.h"
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/z3_util.h"

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

absl::StatusOr<absl::btree_map<std::string, z3::expr>> FreeSymbolicHeaders(
    const google::protobuf::Map<std::string, ir::HeaderType> &headers) {
  // Loop over every header instance in the p4 program.
  // Find its type, and loop over every field in it, creating a symbolic free
  // variable for every field in every header instance.
  absl::btree_map<std::string, z3::expr> symbolic_headers;
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

  // Initialize pseudo header fields.
  symbolic_headers.insert({
      std::string(kGotClonedPseudoField),
      Z3Context().bool_val(false),
  });
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
  ASSIGN_OR_RETURN(bool dropped, EvalZ3Bool(context.trace.dropped, model));
  ASSIGN_OR_RETURN(bool got_cloned,
                   EvalZ3Bool(context.trace.got_cloned, model));
  absl::btree_map<std::string, ConcreteTableMatch> matched_entries;
  for (const auto &[table, match] : context.trace.matched_entries) {
    ASSIGN_OR_RETURN(bool matched, EvalZ3Bool(match.matched, model));
    ASSIGN_OR_RETURN(int entry_index, EvalZ3Int(match.entry_index, model));
    matched_entries[table] = ConcreteTableMatch{
        .matched = matched,
        .entry_index = entry_index,
    };
  }

  return ConcreteContext{
      .ingress_port = ingress_port,
      .egress_port = egress_port,
      .ingress_headers = ingress_headers,
      .egress_headers = egress_headers,
      .trace =
          ConcreteTrace{
              .matched_entries = matched_entries,
              .dropped = dropped,
              .got_cloned = got_cloned,
          },
  };
}

absl::StatusOr<SymbolicTableMatches> MergeMatchesOnCondition(
    const z3::expr &condition, const SymbolicTableMatches &true_matches,
    const SymbolicTableMatches &false_matches) {
  SymbolicTableMatches merged;

  // Add all tables matches in true_trace.
  for (const auto &[name, true_match] : true_matches) {
    // The table should not be applied in the other branch.
    if (false_matches.contains(name)) {
      return absl::InternalError(
          absl::Substitute("Table '$0' was symbolically executed both in true "
                           "and false branches, this is not expected",
                           name));
    }

    // Get the default match for the false branch.
    const SymbolicTableMatch false_match = DefaultTableMatch();

    // Merge this match.
    ASSIGN_OR_RETURN(
        z3::expr matched,
        operators::Ite(condition, true_match.matched, false_match.matched));
    ASSIGN_OR_RETURN(z3::expr entry_index,
                     operators::Ite(condition, true_match.entry_index,
                                    false_match.entry_index));
    merged.insert({name, SymbolicTableMatch{
                             .matched = matched,
                             .entry_index = entry_index,
                         }});
  }

  // Add all tables matches in false_matches.
  for (const auto &[name, false_match] : false_matches) {
    // The table should not be applied in the other branch.
    if (true_matches.contains(name)) {
      return absl::InternalError(
          absl::Substitute("Table '$0' was symbolically executed both in true "
                           "and false branches, this is not expected",
                           name));
    }

    // Get the default match for the true branch.
    const SymbolicTableMatch true_match = DefaultTableMatch();

    // Merge this match.
    ASSIGN_OR_RETURN(
        z3::expr matched,
        operators::Ite(condition, true_match.matched, false_match.matched));
    ASSIGN_OR_RETURN(z3::expr entry_index,
                     operators::Ite(condition, true_match.entry_index,
                                    false_match.entry_index));
    merged.insert({name, SymbolicTableMatch{
                             .matched = matched,
                             .entry_index = entry_index,
                         }});
  }

  return merged;
}

absl::StatusOr<SymbolicTableMatches> MergeDisjointTableMatches(
    const SymbolicTableMatches &lhs, const SymbolicTableMatches &rhs) {
  SymbolicTableMatches merged = lhs;
  for (const auto &[table_name, match] : rhs) {
    auto [_, inserted] = merged.insert({table_name, match});
    if (!inserted) {
      return absl::InvalidArgumentError(absl::Substitute(
          "Expected disjoint keys. Table '$0' encountered in both maps",
          table_name));
    }
  }
  return merged;
}

}  // namespace util
}  // namespace symbolic
}  // namespace p4_symbolic
