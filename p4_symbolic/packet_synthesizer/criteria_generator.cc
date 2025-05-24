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

#include <string>
#include <vector>

#include "absl/container/btree_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/packet_synthesizer/coverage_goal.pb.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesis_criteria.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesis_criteria.pb.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/symbolic/table.h"
#include "p4_symbolic/symbolic/util.h"

namespace p4_symbolic::packet_synthesizer {
namespace {

// Checks if the given `target` string matches the given string matching
// `pattern`. A string s matches pattern p iff s == p or p == "*" (we can expand
// this in the future if needed).
bool MatchesPattern(absl::string_view target, absl::string_view pattern) {
  return pattern == "*" || target == pattern;
}

// Checks if the given `target` string matches at least one of the given
// `patterns`.
bool MatchesPatterns(absl::string_view target, const Patterns& patterns) {
  for (const auto& pattern : patterns.patterns()) {
    if (MatchesPattern(target, pattern)) return true;
  }
  return false;
}

// Generates a list of packet synthesis criteria for the given entry coverage
// `goal`, consistent with the semantics defined in
// coverage_goal.proto:EntryCoverageGoal.
absl::StatusOr<std::vector<PacketSynthesisCriteria>>
GenerateSynthesisCriteriaFor(const EntryCoverageGoal& goal,
                             const symbolic::SolverState& solver_state) {
  // Determine selected tables, sort by name.
  absl::btree_set<std::string> target_tables;
  for (const auto& [table_name, table] : solver_state.program.tables()) {
    // Exclude BMv2's internal tables.
    if (table.table_definition().preamble().id() == 0) {
      continue;
    }

    // TODO: Check if each pattern matches at least one table (and
    // other possible pitfalls).
    if (MatchesPatterns(table_name, goal.tables()) &&
        !MatchesPatterns(table_name, goal.table_exclusions())) {
      target_tables.insert(table_name);
    }
  }

  std::vector<PacketSynthesisCriteria> criteria_list;
  for (const auto& table_name : target_tables) {
    PacketSynthesisCriteria criteria;
    criteria.mutable_table_reachability_criteria()->set_table_name(table_name);
    criteria.mutable_table_entry_reachability_criteria()->set_table_name(
        table_name);

    // Add one synthesis criteria with table entry reachability constraint per
    // each table entry.
    bool table_is_empty = true;
    auto it = solver_state.context.table_entries.find(table_name);
    if (it != solver_state.context.table_entries.end()) {
      const std::vector<ir::TableEntry>& entries = it->second;
      if (!entries.empty()) table_is_empty = false;
      for (int i = 0; i < entries.size(); i++) {
        criteria.mutable_table_entry_reachability_criteria()->set_match_index(
            i);
        criteria_list.push_back(criteria);
        criteria_list.back()
            .mutable_metadata()
            ->mutable_covered_entity_debug_strings()
            ->Add(gutil::PrintTextProto(entries[i]));
      }
    }

    // If configured, add one synthesis criteria covering the table's default
    // action.
    if (goal.cover_default_actions()) {
      // If configured, exclude empty tables.
      if (goal.exclude_empty_tables() && table_is_empty) continue;

      criteria.mutable_table_entry_reachability_criteria()->set_match_index(
          symbolic::table::kDefaultActionEntryIndex);
      criteria_list.push_back(criteria);
    }
  }

  return criteria_list;
}

// Generates a list of packet synthesis criteria for the given packet fate
// coverage `goal`, consistent with the semantics defined in
// coverage_goal.proto:PacketFateCoverageGoal.
absl::StatusOr<std::vector<PacketSynthesisCriteria>>
GenerateSynthesisCriteriaFor(const PacketFateCoverageGoal& goal,
                             const symbolic::SolverState& solver_state) {
  std::vector<PacketSynthesisCriteria> criteria_list;

  // Add one synthesis criteria with packet output constraints per each selected
  // fate.
  for (const auto fate : goal.fates()) {
    PacketSynthesisCriteria criteria;
    switch (fate) {
      case PacketFateCoverageGoal::PacketFate::
          PacketFateCoverageGoal_PacketFate_UNSPECIFIED:
        // Add no constraint.
        break;
      case PacketFateCoverageGoal::PacketFate::
          PacketFateCoverageGoal_PacketFate_DROP:
        criteria.mutable_output_criteria()->set_drop_expected(true);
        break;
      case PacketFateCoverageGoal::PacketFate::
          PacketFateCoverageGoal_PacketFate_NOT_DROP:
        criteria.mutable_output_criteria()->set_drop_expected(false);
        break;
      default:
        return absl::UnimplementedError(
            absl::StrCat("Unsupported packet fate: ", fate));
    }
    criteria_list.push_back(criteria);
  }

  return criteria_list;
}

HeaderCriteria::FieldCriterion MakeHeaderValidityCriterion(
    absl::string_view header_name, bool valid) {
  HeaderCriteria::FieldCriterion field_criterion;
  field_criterion.mutable_field_match()->set_name(
      symbolic::util::GetHeaderValidityFieldName(header_name));
  field_criterion.mutable_field_match()->mutable_exact()->set_hex_str(
      valid ? "0x1" : "0x0");
  return field_criterion;
}

// Generates a list of packet synthesis criteria for the given input packet
// header coverage `goal`, consistent with the semantics defined in
// coverage_goal.proto:HeaderCoverageGoal.
absl::StatusOr<std::vector<PacketSynthesisCriteria>>
GenerateSynthesisCriteriaFor(const HeaderCoverageGoal& goal,
                             const symbolic::SolverState& solver_state) {
  // Determine selected headers, sort by name.
  absl::btree_set<std::string> target_headers;
  absl::btree_set<std::string> headers_to_prevent_unless_explicitly_covered;
  for (const auto& [header_name, _] : solver_state.program.headers()) {
    // Exclude metadata headers.
    if (absl::StartsWith(header_name, "standard_metadata") ||
        // The user defined metadata in BMv2 are all part of a header named
        // `scalars`.
        absl::StartsWith(header_name, "scalars")) {
      continue;
    }

    if (MatchesPatterns(header_name, goal.headers()) &&
        !MatchesPatterns(header_name, goal.header_exclusions())) {
      target_headers.insert(header_name);
    }

    if (MatchesPatterns(header_name,
                        goal.headers_to_prevent_unless_explicitly_covered())) {
      headers_to_prevent_unless_explicitly_covered.insert(header_name);
    }
  }

  if (goal.include_wildcard_header()) {
    // Empty table name means no particular header is targeted (see below).
    target_headers.insert("");
  }

  std::vector<PacketSynthesisCriteria> criteria_list;

  for (const auto& header_name : target_headers) {
    // Add constraints to make the targeted header valid.
    PacketSynthesisCriteria criteria;
    if (!header_name.empty()) {
      *criteria.mutable_input_packet_header_criteria()->add_field_criteria() =
          MakeHeaderValidityCriterion(header_name, /*valid=*/true);
    }

    // Add constraints to make headers in
    // `headers_to_prevent_unless_explicitly_covered` (except the currently
    // targeted header itself) invalid.
    for (const auto& prevented_header_name :
         headers_to_prevent_unless_explicitly_covered) {
      if (prevented_header_name != header_name) {
        *criteria.mutable_input_packet_header_criteria()->add_field_criteria() =
            MakeHeaderValidityCriterion(prevented_header_name, /*valid=*/false);
      }
    }

    criteria_list.push_back(criteria);
  }

  return criteria_list;
}

// Generates a list of packet synthesis criteria for the custom criteria
// coverage `goal`, consistent with the semantics defined in
// coverage_goal.proto:CustomCriteriaCoverageGoal.
absl::StatusOr<std::vector<PacketSynthesisCriteria>>
GenerateSynthesisCriteriaFor(const CustomCriteriaCoverageGoal& goal,
                             const symbolic::SolverState& solver_state) {
  return std::vector<PacketSynthesisCriteria>(goal.criteria_list().begin(),
                                              goal.criteria_list().end());
}

// Generates a list of packet synthesis criteria for a given (composite)
// coverage `goal`, consistent with the semantics defined in
// coverage_goal.proto:CoverageGoal.
absl::StatusOr<std::vector<PacketSynthesisCriteria>>
GenerateSynthesisCriteriaFor(const CartesianProductCoverageGoal& goal,
                             const symbolic::SolverState& solver_state) {
  // Use a wildcard synthesis criteria for any missing goal.
  PacketSynthesisCriteria wildcard;
  std::vector<PacketSynthesisCriteria> entry_criteria = {wildcard};
  std::vector<PacketSynthesisCriteria> fate_criteria = {wildcard};
  std::vector<PacketSynthesisCriteria> header_criteria = {wildcard};
  std::vector<PacketSynthesisCriteria> custom_criteria = {wildcard};

  // Generate criteria for individual goals.
  if (goal.has_entry_coverage()) {
    ASSIGN_OR_RETURN(entry_criteria, GenerateSynthesisCriteriaFor(
                                         goal.entry_coverage(), solver_state));
  }

  if (goal.has_packet_fate_coverage()) {
    ASSIGN_OR_RETURN(fate_criteria,
                     GenerateSynthesisCriteriaFor(goal.packet_fate_coverage(),
                                                  solver_state));
  }

  if (goal.has_header_coverage()) {
    ASSIGN_OR_RETURN(
        header_criteria,
        GenerateSynthesisCriteriaFor(goal.header_coverage(), solver_state));
  }

  if (goal.has_custom_criteria_coverage()) {
    ASSIGN_OR_RETURN(custom_criteria,
                     GenerateSynthesisCriteriaFor(
                         goal.custom_criteria_coverage(), solver_state));
  }

  // Combine criteria across goals.
  ASSIGN_OR_RETURN(
      auto fate_entry_criteria,
      MakeCartesianProductConjunction(fate_criteria, entry_criteria));
  ASSIGN_OR_RETURN(
      auto header_fate_entry_criteria,
      MakeCartesianProductConjunction(header_criteria, fate_entry_criteria));
  return MakeCartesianProductConjunction(header_fate_entry_criteria,
                                         custom_criteria);
}

// Generates a list of packet synthesis criteria for a given coverage `goal`.
absl::StatusOr<std::vector<PacketSynthesisCriteria>>
GenerateSynthesisCriteriaFor(const CoverageGoal& goal,
                             const symbolic::SolverState& solver_state) {
  switch (goal.coverage_goal_case()) {
    case CoverageGoal::kEntryCoverage:
      return GenerateSynthesisCriteriaFor(goal.entry_coverage(), solver_state);
    case CoverageGoal::kPacketFateCoverage:
      return GenerateSynthesisCriteriaFor(goal.packet_fate_coverage(),
                                          solver_state);
    case CoverageGoal::kHeaderCoverage:
      return GenerateSynthesisCriteriaFor(goal.header_coverage(), solver_state);
    case CoverageGoal::kCartesianProductCoverage:
      return GenerateSynthesisCriteriaFor(goal.cartesian_product_coverage(),
                                          solver_state);
    case CoverageGoal::kCustomCriteriaCoverage:
      return GenerateSynthesisCriteriaFor(goal.custom_criteria_coverage(),
                                          solver_state);
    default:
      return absl::UnimplementedError(absl::StrCat(
          "Unsupported coverage goal: ", goal.coverage_goal_case()));
  }
}

}  // namespace

// Generates a list of packet synthesis criteria for the given list of
// (composite) coverage `goals`, consistent with the semantics defined in
// coverage_goal.proto:CoverageGoals.
absl::StatusOr<std::vector<PacketSynthesisCriteria>>
GenerateSynthesisCriteriaFor(const CoverageGoals& goals,
                             const symbolic::SolverState& solver_state) {
  std::vector<PacketSynthesisCriteria> criteria_list;
  for (const auto& goal : goals.coverage_goals()) {
    ASSIGN_OR_RETURN(auto criteria_for_goal,
                     GenerateSynthesisCriteriaFor(goal, solver_state));
    criteria_list.insert(criteria_list.end(), criteria_for_goal.begin(),
                         criteria_for_goal.end());
  }

  return criteria_list;
}

}  // namespace p4_symbolic::packet_synthesizer
