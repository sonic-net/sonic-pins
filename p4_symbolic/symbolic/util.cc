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
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "glog/logging.h"
#include "p4_pdpi/internal/ordered_map.h"
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/z3_util.h"

namespace p4_symbolic {
namespace symbolic {
namespace util {

namespace {

// Extract the header field definition of a `field_ref` from the given P4
// `program`.
absl::StatusOr<ir::HeaderField> GetFieldDefinition(
    const ir::P4Program &program, absl::string_view field_ref) {
  // Split the field reference into header and field names.
  std::vector<std::string> split = absl::StrSplit(field_ref, '.');
  if (split.size() != 2) {
    return absl::InvalidArgumentError(
        absl::Substitute("Expected <header>.<field> got '$0'", field_ref));
  }
  const std::string &header_name = split[0];
  const std::string &field_name = split[1];

  // Extract the header definition from the program.
  if (!program.headers().contains(header_name)) {
    return absl::InvalidArgumentError(
        absl::Substitute("Unexpected header instance'$0'", header_name));
  }
  const p4_symbolic::ir::HeaderType &header_def =
      program.headers().at(header_name);

  // Extract the field definition from the header definition.
  if (!header_def.fields().contains(field_name)) {
    return absl::InvalidArgumentError(absl::Substitute(
        "Unexpected field'$0' in header '$1'", field_name, header_name));
  }
  return header_def.fields().at(field_name);
}

}  // namespace

absl::StatusOr<absl::btree_map<std::string, z3::expr>> FreeSymbolicHeaders(
    const google::protobuf::Map<std::string, ir::HeaderType> &headers) {
  // Loop over every header instance in the p4 program.
  // Find its type, and loop over every field in it, creating a symbolic free
  // variable for every field in every header instance.
  absl::btree_map<std::string, z3::expr> symbolic_headers;
  for (const auto &[header_name, header_type] : Ordered(headers)) {
    // Pseudo fields used in P4-Symbolic indicating the state of the header.
    for (const auto &pseudo_field_name :
         {kValidPseudoField, kExtractedPseudoField}) {
      std::string field_name =
          absl::StrFormat("%s.%s", header_name, pseudo_field_name);
      // TODO: Set these fields to false while removing SAI parser
      // code.
      z3::expr free_expr = Z3Context().bool_const(field_name.c_str());
      symbolic_headers.insert({field_name, free_expr});
    }

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
    const SymbolicContext &context, z3::model model,
    const values::P4RuntimeTranslator &translator) {
  // Extract ports.
  std::string ingress_port = model.eval(context.ingress_port, true).to_string();
  std::string egress_port = model.eval(context.egress_port, true).to_string();

  // Extract the ingress, parsed, and egress headers.
  ConcretePerPacketState ingress_headers;
  for (const auto &[name, expr] : context.ingress_headers) {
    ASSIGN_OR_RETURN(ingress_headers[name],
                     values::TranslateValueToP4RT(
                         name, model.eval(expr, true).to_string(), translator));
  }
  ConcretePerPacketState parsed_headers;
  for (const auto &[name, expr] : context.parsed_headers) {
    ASSIGN_OR_RETURN(parsed_headers[name],
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
      .parsed_headers = parsed_headers,
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

  // Merge all tables matches in true_trace (including ones in both traces).
  for (const auto &[name, true_match] : true_matches) {
    // Find match in other trace (or use default).
    const SymbolicTableMatch false_match = false_matches.contains(name)
                                               ? false_matches.at(name)
                                               : DefaultTableMatch();

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

  // Merge all tables matches in false_matches only.
  for (const auto &[name, false_match] : false_matches) {
    if (true_matches.contains(name)) {
      // Already covered.
      LOG(WARNING) << "Table '" << name << "' is evaluated more than once.";
      continue;
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

absl::StatusOr<int> GetFieldBitwidth(absl::string_view field_name,
                                     const ir::P4Program &program) {
  if (absl::EndsWith(field_name, symbolic::kValidPseudoField) ||
      absl::EndsWith(field_name, symbolic::kExtractedPseudoField)) {
    return 1;
  } else {
    ASSIGN_OR_RETURN(const ir::HeaderField field_definition,
                     GetFieldDefinition(program, field_name));
    return field_definition.bitwidth();
  }
}

std::string GetHeaderValidityFieldName(absl::string_view header_name) {
  return absl::StrCat(header_name, ".", kValidPseudoField);
}

}  // namespace util
}  // namespace symbolic
}  // namespace p4_symbolic
