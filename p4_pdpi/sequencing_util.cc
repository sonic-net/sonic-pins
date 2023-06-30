#include "p4_pdpi/sequencing_util.h"

#include <iterator>
#include <string>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"

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
    const ::p4::v1::TableEntry& table_entry, const IrP4Info& info) {
  ASSIGN_OR_RETURN(
      const IrTableDefinition* ir_table_definition,
      gutil::FindPtrOrStatus(info.tables_by_id(), table_entry.table_id()));
  absl::flat_hash_map<std::string, ReferredTableEntry> referred_table_entries;

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
      referred_table_entries[ir_reference.table()].table = ir_reference.table();
      referred_table_entries[ir_reference.table()].referred_fields.insert(
          {ir_reference.match_field(), value});
    }
  }

  // Extract accumulated table entries into a vector to return.
  std::vector<ReferredTableEntry> referred_table_entries_vector;
  for (auto& [table_name, referred_table_entry] : referred_table_entries) {
    referred_table_entries_vector.push_back(std::move(referred_table_entry));
  }
  return referred_table_entries_vector;
}

// Returns a vector of ReferredTableEntry that `action_params` refers to.
absl::StatusOr<std::vector<ReferredTableEntry>> EntriesReferredToByActionParams(
    absl::Span<const p4::v1::Action_Param* const> action_params,
    const IrActionDefinition& ir_action_definition, const IrP4Info& info) {
  absl::flat_hash_map<std::string, ReferredTableEntry> referred_table_entries;
  for (const p4::v1::Action_Param* const param : action_params) {
    ASSIGN_OR_RETURN(
        const auto* param_definition,
        gutil::FindPtrOrStatus(ir_action_definition.params_by_id(),
                               param->param_id()),
        _ << "Failed to extract action definition when creating entries "
             "referred by action: Action param with ID "
          << param->param_id() << " does not exist.");
    for (const auto& ir_reference : param_definition->references()) {
      referred_table_entries[ir_reference.table()].table = ir_reference.table();
      referred_table_entries[ir_reference.table()].referred_fields.insert(
          {ir_reference.match_field(), param->value()});
    }
  }

  // Extract accumulated table entries into a vector to return.
  std::vector<ReferredTableEntry> referred_table_entries_vector;
  for (auto& [table_name, referred_table_entry] : referred_table_entries) {
    referred_table_entries_vector.push_back(std::move(referred_table_entry));
  }
  return referred_table_entries_vector;
}

// Returns a vector of `ReferredTableEntry`s that `action` refers to based on
// its action parameters' values and `info` reference fields for the given
// action.
absl::StatusOr<std::vector<ReferredTableEntry>> EntriesReferredToByAction(
    const ::p4::v1::TableAction& action, const IrP4Info& info) {
  switch (action.type_case()) {
    case p4::v1::TableAction::kAction: {
      ASSIGN_OR_RETURN(
          const IrActionDefinition* ir_action_definition,
          gutil::FindPtrOrStatus(info.actions_by_id(),
                                 action.action().action_id()),
          _ << "Failed to extract action definition when creating entries "
               "referred by action: Action with ID "
            << action.action().action_id() << " does not exist in IrP4Info.");
      return EntriesReferredToByActionParams(action.action().params(),
                                             *ir_action_definition, info);
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
            EntriesReferredToByActionParams(action.action().params(),
                                            *ir_action_definition, info));
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
    ReferenceRelationKey key{.referred_table_name = ir_reference.table()};
    ReferenceRelation& reference_relation = reference_relations[key];
    reference_relation.match_field_names.insert(ir_reference.match_field());
  }
  return reference_relations;
}

absl::StatusOr<std::vector<ReferredTableEntry>> EntriesReferredToByTableEntry(
    const ::p4::v1::TableEntry& table_entry, const IrP4Info& ir_p4info) {
  ASSIGN_OR_RETURN(
      std::vector<ReferredTableEntry> referred_table_entries_by_match_fields,
      EntriesReferredToByTableEntryMatchFields(table_entry, ir_p4info));
  ASSIGN_OR_RETURN(
      std::vector<ReferredTableEntry> referred_table_entries_by_actions,
      EntriesReferredToByAction(table_entry.action(), ir_p4info));
  referred_table_entries_by_match_fields.insert(
      referred_table_entries_by_match_fields.end(),
      std::make_move_iterator(referred_table_entries_by_actions.begin()),
      std::make_move_iterator(referred_table_entries_by_actions.end()));
  return referred_table_entries_by_match_fields;
}

}  // namespace pdpi
