// Copyright 2025 Google LLC
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

#include "p4_infra/p4_pdpi/sequencing_util.h"

#include <cstdint>
#include <iterator>
#include <string>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/types/span.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/status.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"

namespace pdpi {
namespace {

// Returns the match field value for `field_match` as string if `field_match`'s
// field_match_type is exact or optional. Returns InvalidArgument for other
// field_match_type.
absl::StatusOr<std::string> GetExactOrOptionalMatchFieldValue(
    const ::p4::v1::FieldMatch& field_match) {
  switch (field_match.field_match_type_case()) {
    case ::p4::v1::FieldMatch::kExact:
      return field_match.exact().value();
    case ::p4::v1::FieldMatch::kOptional:
      return field_match.optional().value();
    default:
      return absl::InvalidArgumentError(
          absl::StrCat("cannot extract value from field match type: ",
                       field_match.field_match_type_case()));
  }
}

// Returns a vector of ReferredTableEntries that `table_entry`'s match fields
// refer to.
absl::StatusOr<std::vector<ReferredTableEntry>>
EntriesReferredToByTableEntryMatchFields(
    const IrP4Info& info, const ::p4::v1::TableEntry& table_entry) {
  ASSIGN_OR_RETURN(
      const IrTableDefinition* ir_table_definition,
      gutil::FindPtrOrStatus(info.tables_by_id(), table_entry.table_id()));
  absl::flat_hash_map<uint32_t, ReferredTableEntry> referred_table_entries;

  // Iterate through match fields of `table_entry` and incrementally build
  // ReferredTableEntries that `table_entry` can refer to.
  // At the end of the iteration, each value in the k/v pair represents a table
  // and its match fields that `table_entry` refers to.
  for (const p4::v1::FieldMatch& field_match : table_entry.match()) {
    ASSIGN_OR_RETURN(
        const auto* match_field_definition,
        gutil::FindPtrOrStatus(ir_table_definition->match_fields_by_id(),
                               field_match.field_id()));
    // Ignore other match field type since only Exact or Optional are used to
    // refer to entries.
    if (!field_match.has_exact() && !field_match.has_optional()) continue;
    ASSIGN_OR_RETURN(std::string value,
                     GetExactOrOptionalMatchFieldValue(field_match));
    for (const auto& ir_reference : match_field_definition->references()) {
      referred_table_entries[ir_reference.table_id()].table_id =
          ir_reference.table_id();
      referred_table_entries[ir_reference.table_id()].referred_fields.insert(
          ReferredField{
              .match_field_id = ir_reference.match_field_id(),
              .value = value,
          });
    }
  }

  // Extract accumulated table entries into a vector to return.
  std::vector<ReferredTableEntry> referred_table_entries_vector;
  for (auto& [unused, referred_table_entry] : referred_table_entries) {
    referred_table_entries_vector.push_back(std::move(referred_table_entry));
  }
  return referred_table_entries_vector;
}

// Returns a vector of ReferredTableEntry that `action_params` refers to.
absl::StatusOr<std::vector<ReferredTableEntry>> EntriesReferredToByActionParams(
    const IrP4Info& info, const IrActionDefinition& ir_action_definition,
    absl::Span<const p4::v1::Action_Param* const> action_params) {
  absl::flat_hash_map<uint32_t, ReferredTableEntry> referred_table_entries;
  for (const p4::v1::Action_Param* const param : action_params) {
    ASSIGN_OR_RETURN(
        const auto* param_definition,
        gutil::FindPtrOrStatus(ir_action_definition.params_by_id(),
                               param->param_id()),
        _ << "Failed to extract action definition when creating entries "
             "referred by action: Action param with ID "
          << param->param_id() << " does not exist.");
    for (const auto& ir_reference : param_definition->references()) {
      referred_table_entries[ir_reference.table_id()].table_id =
          ir_reference.table_id();
      referred_table_entries[ir_reference.table_id()].referred_fields.insert(
          ReferredField{
              .match_field_id = ir_reference.match_field_id(),
              .value = param->value(),
          });
    }
  }

  // Extract accumulated table entries into a vector to return.
  std::vector<ReferredTableEntry> referred_table_entries_vector;
  for (auto& [unused, referred_table_entry] : referred_table_entries) {
    referred_table_entries_vector.push_back(std::move(referred_table_entry));
  }
  return referred_table_entries_vector;
}

// Returns a vector of `ReferredTableEntry`s that `action` refers to based on
// its action parameters' values and `info` reference fields for the given
// action.
absl::StatusOr<std::vector<ReferredTableEntry>> EntriesReferredToByAction(
    const IrP4Info& info, const ::p4::v1::TableAction& action) {
  switch (action.type_case()) {
    case p4::v1::TableAction::kAction: {
      ASSIGN_OR_RETURN(
          const IrActionDefinition* ir_action_definition,
          gutil::FindPtrOrStatus(info.actions_by_id(),
                                 action.action().action_id()),
          _ << "Failed to extract action definition when creating entries "
               "referred by action: Action with ID "
            << action.action().action_id() << " does not exist in IrP4Info.");
      return EntriesReferredToByActionParams(info, *ir_action_definition,
                                             action.action().params());
    }
    case p4::v1::TableAction::kActionProfileActionSet: {
      std::vector<ReferredTableEntry> referred_table_entries_vector;
      for (const auto& action :
           action.action_profile_action_set().action_profile_actions()) {
        ASSIGN_OR_RETURN(
            const IrActionDefinition* ir_action_definition,
            gutil::FindPtrOrStatus(info.actions_by_id(),
                                   action.action().action_id()),
            _ << "Failed to extract action definition when creating entries "
                 "referred by action: Action with ID "
              << action.action().action_id() << " does not exist in IrP4Info.");

        ASSIGN_OR_RETURN(
            std::vector<ReferredTableEntry> referred_entries_by_action,
            EntriesReferredToByActionParams(info, *ir_action_definition,
                                            action.action().params()));
        for (auto& referred_table_entry : referred_entries_by_action) {
          referred_table_entries_vector.push_back(
              std::move(referred_table_entry));
        }
      }
      return referred_table_entries_vector;
    }
    default:
      return absl::UnimplementedError(absl::StrCat(
          "Sequencing can only handle action and action profile set, but got:",
          action.type_case()));
  }
}

}  // namespace

absl::flat_hash_map<ReferenceRelationKey, ReferenceRelation>
CreateReferenceRelations(const IrP4Info& ir_p4info) {
  absl::flat_hash_map<ReferenceRelationKey, ReferenceRelation>
      reference_relations;
  for (const IrMatchFieldReference& ir_reference : ir_p4info.references()) {
    ReferenceRelationKey key{
        .referred_table_id = ir_reference.table_id(),
    };
    ReferenceRelation& reference_relation = reference_relations[key];
    reference_relation.match_field_ids.insert(ir_reference.match_field_id());
  }
  return reference_relations;
}

absl::StatusOr<std::vector<ReferredTableEntry>> EntriesReferredToByTableEntry(
    const IrP4Info& ir_p4info, const ::p4::v1::TableEntry& table_entry) {
  ASSIGN_OR_RETURN(
      std::vector<ReferredTableEntry> referred_table_entries_by_match_fields,
      EntriesReferredToByTableEntryMatchFields(ir_p4info, table_entry));
  ASSIGN_OR_RETURN(
      std::vector<ReferredTableEntry> referred_table_entries_by_actions,
      EntriesReferredToByAction(ir_p4info, table_entry.action()));
  referred_table_entries_by_match_fields.insert(
      referred_table_entries_by_match_fields.end(),
      std::make_move_iterator(referred_table_entries_by_actions.begin()),
      std::make_move_iterator(referred_table_entries_by_actions.end()));
  return referred_table_entries_by_match_fields;
}

absl::StatusOr<ReferredTableEntry> CreateReferrableTableEntry(
    const IrP4Info& ir_p4info,
    const absl::flat_hash_map<ReferenceRelationKey, ReferenceRelation>&
        reference_relations,
    const p4::v1::TableEntry& table_entry) {
  // If `table_entry` can't be referred to by any table, returns an error.
  ReferenceRelationKey reference_relation_key{
      .referred_table_id = table_entry.table_id(),
  };
  ASSIGN_OR_RETURN(
      const ReferenceRelation* reference_relation,
      gutil::FindPtrOrStatus(reference_relations, reference_relation_key),
      _ << " while trying to look up ReferenceRelation with key "
        << absl::StrCat(reference_relation_key));

  ReferredTableEntry referrable_table_entry = {
      .table_id = table_entry.table_id(),
  };
  // Incrementally builds referrable_table_entry by iterating through each match
  // field of `table_entry` and adding referred-to entry to
  // referrable_table_entry.
  for (const p4::v1::FieldMatch& field_match : table_entry.match()) {
    if (reference_relation->match_field_ids.contains(field_match.field_id())) {
      ASSIGN_OR_RETURN(std::string value,
                       GetExactOrOptionalMatchFieldValue(field_match));
      referrable_table_entry.referred_fields.insert(ReferredField{
          .match_field_id = field_match.field_id(),
          .value = value,
      });
    }
  }
  return referrable_table_entry;
}

}  // namespace pdpi
