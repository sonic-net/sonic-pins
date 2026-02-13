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
#include <utility>

#include "absl/container/btree_map.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "gutil/status.h"
#include "gutil/ordered_map.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/context.h"
#include "p4_symbolic/symbolic/deparser.h"
#include "p4_symbolic/symbolic/operators.h"
#include "p4_symbolic/symbolic/solver_state.h"
#include "p4_symbolic/symbolic/symbolic_table_entry.h"
#include "p4_symbolic/z3_util.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {
namespace util {

using ::gutil::AsOrderedView;

namespace {

// Extracts the header field definition based on the given `header_name` and
// `field_name` from the given P4 `program`.
absl::StatusOr<ir::HeaderField> GetFieldDefinition(
    const ir::P4Program &program, absl::string_view header_name,
    absl::string_view field_name) {
  // Extract the header definition from the program.
  auto header_it = program.headers().find(header_name);
  if (header_it == program.headers().end()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Unexpected header instance '" << header_name << "'";
  }
  const ir::HeaderType &header = header_it->second;

  // Extract the field definition from the header definition.
  auto field_it = header.fields().find(field_name);
  if (field_it == header.fields().end()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Unexpected field '" << field_name << "' in header '"
           << header_name << "'";
  }
  return field_it->second;
}

}  // namespace

absl::StatusOr<absl::btree_map<std::string, z3::expr>> FreeSymbolicHeaders(
    z3::context &z3_context,
    const google::protobuf::Map<std::string, ir::HeaderType> &headers) {
  // Loop over every header instance in the p4 program.
  // Find its type, and loop over every field in it, creating a symbolic free
  // variable for every field in every header instance.
  absl::btree_map<std::string, z3::expr> symbolic_headers;
  for (const auto &[header_name, header_type] : AsOrderedView(headers)) {
    // Pseudo fields (`$valid$`, `$extracted$`) in P4-Symbolic indicate the
    // state of the header. Here we initialize the pseudo fields of each header
    // to symbolic variables.
    for (const auto &pseudo_field_name :
         {kValidPseudoField, kExtractedPseudoField}) {
      std::string field_name =
          absl::StrFormat("%s.%s", header_name, pseudo_field_name);
      z3::expr free_variable = z3_context.bool_const(field_name.c_str());
      symbolic_headers.insert({field_name, free_variable});
    }

    // Regular fields defined in the p4 program or v1model.
    for (const auto &[field_name, field] : 
		    AsOrderedView(header_type.fields())) {
      if (field.signed_()) {
        return absl::UnimplementedError(
            "Negative header fields are not supported");
      }

      std::string field_full_name =
          absl::StrFormat("%s.%s", header_name, field_name);
      z3::expr field_expression =
          z3_context.bv_const(field_full_name.c_str(), field.bitwidth());
      symbolic_headers.insert({field_full_name, field_expression});
    }
  }

  // Initialize packet-wide pseudo fields to false.
  symbolic_headers.insert({
      std::string(kGotClonedPseudoField),
      z3_context.bool_val(false),
  });
  symbolic_headers.insert({
      std::string(kGotRecirculatedPseudoField),
      z3_context.bool_val(false),
  });

  return symbolic_headers;
}

SymbolicTableMatch DefaultTableMatch(z3::context &z3_context) {
  return {
      z3_context.bool_val(false),  // No match yet!
      z3_context.int_val(-1)       // No match index.
  };
}

// Translates the table and action names back to the aliases.
// This should be called when synthesizing concrete entries used on other
// target platforms. PDPI maps are keyed by the alias names. This function
// makes the table entry compatible with PDPI formats.
// TODO: Consider removing this function if we switch to using
// aliases as table/action names in P4-Symbolic.
void ConvertFullyQualifiedNamesToAliases(ir::ConcreteTableEntry &entry,
                                         const ir::P4Program &program) {
  if (!entry.pdpi_ir_entity().has_table_entry()) return;
  pdpi::IrTableEntry &pdpi_ir_entry =
      *entry.mutable_pdpi_ir_entity()->mutable_table_entry();

  // Check if the table specified by the table name exists.
  auto it = program.tables().find(pdpi_ir_entry.table_name());
  // If the table cannot be found with the table name, it may have been
  // converted to the alias already.
  if (it == program.tables().end()) return;
  const ir::Table &table = it->second;

  // Set table name that is compatible with PDPI.
  pdpi_ir_entry.set_table_name(table.table_definition().preamble().alias());

  // Set action name that is compatible with PDPI.
  auto convert_action_name = [&program](
                                 pdpi::IrActionInvocation &action_invocation) {
    const std::string &action_name = action_invocation.name();
    auto it = program.actions().find(action_name);
    // If the action cannot be found with the action name, it may have been
    // converted to the alias already.
    if (it == program.actions().end()) return;
    const ir::Action &action = it->second;
    action_invocation.set_name(action.action_definition().preamble().alias());
  };

  if (pdpi_ir_entry.has_action()) {
    convert_action_name(*pdpi_ir_entry.mutable_action());
  } else if (pdpi_ir_entry.has_action_set()) {
    for (pdpi::IrActionSetInvocation &action :
         *pdpi_ir_entry.mutable_action_set()->mutable_actions()) {
      convert_action_name(*action.mutable_action());
    }
  }
}

absl::StatusOr<ConcreteContext> ExtractFromModel(const z3::model &model,
                                                 const SolverState &state) {
  // Extract ports.
  std::string ingress_port =
      model.eval(state.context.ingress_port, true).to_string();
  std::string egress_port =
      model.eval(state.context.egress_port, true).to_string();

  // Extract the ingress, parsed, and egress headers.
  ConcretePerPacketState ingress_headers;
  for (const auto &[name, expr] : state.context.ingress_headers) {
    ASSIGN_OR_RETURN(auto translated_value,
                     values::TranslateZ3ValueStringToP4RT(
                         model.eval(expr, true).to_string(), name,
                         /*type_name=*/std::nullopt, state.translator));
    ingress_headers[name] = std::move(translated_value.first);
  }
  ConcretePerPacketState parsed_headers;
  for (const auto &[name, expr] : state.context.parsed_headers) {
    ASSIGN_OR_RETURN(auto translated_value,
                     values::TranslateZ3ValueStringToP4RT(
                         model.eval(expr, true).to_string(), name,
                         /*type_name=*/std::nullopt, state.translator));
    parsed_headers[name] = std::move(translated_value.first);
  }
  ConcretePerPacketState egress_headers;
  for (const auto &[name, expr] : state.context.egress_headers) {
    ASSIGN_OR_RETURN(auto translated_value,
                     values::TranslateZ3ValueStringToP4RT(
                         model.eval(expr, true).to_string(), name,
                         /*type_name=*/std::nullopt, state.translator));
    egress_headers[name] = std::move(translated_value.first);
  }

  ASSIGN_OR_RETURN(std::string serialized_ingress_headers,
                   DeparseIngressPacket(state, model));
  ASSIGN_OR_RETURN(std::string serialized_egress_headers,
                   DeparseEgressPacket(state, model));

  // Extract the table entries.
  absl::btree_map<std::string, std::vector<ir::ConcreteTableEntry>>
      concrete_entries;
  for (const auto &[table_name, entries_per_table] :
       state.context.table_entries) {
    for (const ir::TableEntry &entry : entries_per_table) {
      ir::ConcreteTableEntry &concrete_entry =
          concrete_entries[table_name].emplace_back();
      switch (entry.entry_case()) {
        case ir::TableEntry::kConcreteEntry: {
          concrete_entry = entry.concrete_entry();
          break;
        }
        case ir::TableEntry::kSymbolicEntry: {
          ASSIGN_OR_RETURN(concrete_entry,
                           ExtractConcreteEntryFromModel(
                               entry.symbolic_entry(), model, state.program,
                               state.translator, *state.context.z3_context));
          break;
        }
        case ir::TableEntry::ENTRY_NOT_SET: {
          return gutil::InvalidArgumentErrorBuilder()
                 << "invalid entry in table '" << table_name
                 << "': " << absl::StrCat(entry);
        }
      }
      ConvertFullyQualifiedNamesToAliases(concrete_entry, state.program);
    }
  }

  // Extract the trace (matches on every table).
  ASSIGN_OR_RETURN(bool dropped,
                   EvalZ3Bool(state.context.trace.dropped, model));
  ASSIGN_OR_RETURN(bool got_cloned,
                   EvalZ3Bool(state.context.trace.got_cloned, model));
  absl::btree_map<std::string, ConcreteTableMatch> matched_entries;
  for (const auto &[table, match] : state.context.trace.matched_entries) {
    ASSIGN_OR_RETURN(bool matched, EvalZ3Bool(match.matched, model));
    ASSIGN_OR_RETURN(int entry_index, EvalZ3Int(match.entry_index, model));
    matched_entries[table] = ConcreteTableMatch{
        .matched = matched,
        .entry_index = entry_index,
    };
  }

  return ConcreteContext{
      .ingress_port = std::move(ingress_port),
      .egress_port = std::move(egress_port),
      .ingress_headers = std::move(ingress_headers),
      .parsed_headers = std::move(parsed_headers),
      .egress_headers = std::move(egress_headers),
      .serialized_ingress_headers = std::move(serialized_ingress_headers),
      .serialized_egress_headers = std::move(serialized_egress_headers),
      .table_entries = std::move(concrete_entries),
      .trace =
          ConcreteTrace{
              .matched_entries = std::move(matched_entries),
              .dropped = dropped,
              .got_cloned = got_cloned,
          },
  };
}

absl::StatusOr<SymbolicTableMatches> MergeMatchesOnCondition(
    const z3::expr &condition, const SymbolicTableMatches &true_matches,
    const SymbolicTableMatches &false_matches, z3::context &z3_context) {
  SymbolicTableMatches merged;

  // Merge all tables matches in true_trace (including ones in both traces).
  for (const auto &[name, true_match] : true_matches) {
    // Find match in other trace (or use default).
    const SymbolicTableMatch false_match = false_matches.contains(name)
                                               ? false_matches.at(name)
                                               : DefaultTableMatch(z3_context);

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
    const SymbolicTableMatch true_match = DefaultTableMatch(z3_context);

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

absl::StatusOr<int> GetFieldBitwidth(absl::string_view qualified_field_name,
                                     const ir::P4Program &program) {
  // Split the fully qualified field name into header and field names.
  std::vector<std::string> split = absl::StrSplit(qualified_field_name, '.');
  if (split.size() != 2) {
    return absl::InvalidArgumentError(absl::Substitute(
        "Expected <header>.<field> got '$0'", qualified_field_name));
  }
  return GetFieldBitwidth(/*header_name=*/split[0], /*field_name=*/split[1],
                          program);
}

absl::StatusOr<int> GetFieldBitwidth(absl::string_view header_name,
                                     absl::string_view field_name,
                                     const ir::P4Program &program) {
  if (field_name == symbolic::kValidPseudoField ||
      field_name == symbolic::kExtractedPseudoField) {
    return 1;
  } else {
    ASSIGN_OR_RETURN(const ir::HeaderField field_definition,
                     GetFieldDefinition(program, header_name, field_name));
    return field_definition.bitwidth();
  }
}

std::string GetHeaderValidityFieldName(absl::string_view header_name) {
  return absl::StrCat(header_name, ".", kValidPseudoField);
}

absl::StatusOr<std::string> GetFieldNameFromMatch(absl::string_view match_name,
                                                  const ir::Table &table) {
  const auto &match_name_to_field =
      table.table_implementation().match_name_to_field();
  auto it = match_name_to_field.find(match_name);
  if (it == match_name_to_field.end()) {
    return gutil::NotFoundErrorBuilder()
           << "Match '" << match_name
           << "' not found in the implementation of table '"
           << table.table_definition().preamble().name() << "'";
  }
  const ir::FieldValue &matched_field = it->second;
  return absl::StrFormat("%s.%s", matched_field.header_name(),
                         matched_field.field_name());
}

absl::StatusOr<pdpi::IrMatchFieldDefinition> GetMatchDefinition(
    absl::string_view match_name, const ir::Table &table) {
  const auto &match_fields_by_name =
      table.table_definition().match_fields_by_name();
  auto it = match_fields_by_name.find(match_name);
  if (it == match_fields_by_name.end()) {
    return gutil::NotFoundErrorBuilder()
           << "Match '" << match_name
           << "' not found in the definition of table '"
           << table.table_definition().preamble().name() << "'";
  }
  return it->second;
}

absl::StatusOr<const ir::Table *> GetIrTable(const ir::P4Program &program,
                                             absl::string_view table_name) {
  auto it = program.tables().find(table_name);
  if (it == program.tables().end()) {
    return gutil::NotFoundErrorBuilder()
           << "Table '" << table_name << "' not found";
  }
  return &it->second;
}

}  // namespace util
}  // namespace symbolic
}  // namespace p4_symbolic
