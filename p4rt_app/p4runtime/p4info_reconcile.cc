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

#include "p4rt_app/p4runtime/p4info_reconcile.h"

#include <string>
#include <utility>
#include <vector>

#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/status.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/utils/annotation_parser.h"
#include "p4rt_app/p4runtime/resource_utilization.h"
#include "p4rt_app/sonic/app_db_acl_def_table_manager.h"
#include "p4rt_app/sonic/hashing.h"
#include "p4rt_app/sonic/swss_utils.h"
#include "p4rt_app/utils/table_utility.h"

namespace p4rt_app {
namespace {

template <typename T>
struct SetDifference {
  std::vector<T> deleted;
  std::vector<T> added;
  std::vector<T> intersection;
};

template <typename T>
SetDifference<T> CalculateSetDifference(const absl::btree_set<T>& from,
                                        const absl::btree_set<T>& to) {
  SetDifference<T> difference;
  auto from_iter = from.begin();
  auto to_iter = to.begin();
  while (from_iter != from.end() && to_iter != to.end()) {
    if (*from_iter == *to_iter) {
      difference.intersection.push_back(*from_iter);
      ++from_iter;
      ++to_iter;
    } else if (*from_iter < *to_iter) {
      difference.deleted.push_back(*from_iter);
      ++from_iter;
    } else {  // *from_iter > *to_iter
      difference.added.push_back(*to_iter);
      ++to_iter;
    }
  }
  while (from_iter != from.end()) {
    difference.deleted.push_back(*from_iter);
    ++from_iter;
  }
  while (to_iter != to.end()) {
    difference.added.push_back(*to_iter);
    ++to_iter;
  }
  return difference;
}

absl::Status CalculateHashingDifference(const pdpi::IrP4Info& from,
                                        const pdpi::IrP4Info& to,
                                        P4InfoReconcileTransition& transition) {
  auto from_hash_packet_fields = sonic::ExtractHashPacketFieldConfigs(from);
  if (!from_hash_packet_fields.ok()) {
    return gutil::InternalErrorBuilder()
           << "Failed to calculate hash packets fields from existing P4Info: "
           << from_hash_packet_fields.status().message();
  }
  auto from_hash_parameters = sonic::ExtractHashParamConfigs(from);
  if (!from_hash_parameters.ok()) {
    return gutil::InternalErrorBuilder()
           << "Failed to calculate hash parameter fields from existing P4Info: "
           << from_hash_parameters.status().message();
  }

  ASSIGN_OR_RETURN(auto to_hash_packet_fields,
                   sonic::ExtractHashPacketFieldConfigs(to),
                   _.SetPrepend() << "Failed to calculate hash packet fields "
                                  << "from new forwarding pipeline config. ");
  ASSIGN_OR_RETURN(auto to_hash_parameters, sonic::ExtractHashParamConfigs(to),
                   _.SetPrepend() << "failed to calculate hash parameters from "
                                  << "new forwarding pipeline config. ");

  // calculate packet field config diffs.
  SetDifference packet_field_diff =
      CalculateSetDifference(*from_hash_packet_fields, to_hash_packet_fields);
  absl::btree_set<std::string> to_packet_field_keys;
  for (const sonic::HashPacketFieldConfig& config : to_hash_packet_fields) {
    to_packet_field_keys.insert(to_packet_field_keys.end(), config.key);
  }
  for (const sonic::HashPacketFieldConfig& config : packet_field_diff.deleted) {
    // Skip delete of keys that we will replace.
    if (!to_packet_field_keys.contains(config.key)) {
      transition.hashing_packet_field_configs_to_delete.push_back(config.key);
    }
  }
  for (const sonic::HashPacketFieldConfig& config : packet_field_diff.added) {
    transition.hashing_packet_field_configs_to_set.push_back(config.key);
  }

  // Calculate whether the switch table is different.
  transition.update_switch_table =
      !transition.hashing_packet_field_configs_to_delete.empty() ||
      !transition.hashing_packet_field_configs_to_set.empty() ||
      *from_hash_parameters != to_hash_parameters;

  return absl::OkStatus();
}

absl::StatusOr<absl::btree_set<std::string>> GetAclTableNames(
    const pdpi::IrP4Info& p4info) {
  absl::btree_set<std::string> acl_table_names;
  for (const auto& [name, table] : p4info.tables_by_name()) {
    ASSIGN_OR_RETURN(table::Type table_type, GetTableType(table),
                     _.SetPrepend()
                         << "Failed to determine table type of table '" << name
                         << "': ");
    if (table_type == table::Type::kAcl) acl_table_names.insert(name);
  }
  return acl_table_names;
}

absl::StatusOr<bool> IsValidModification(
    const pdpi::IrTableDefinition& from_table,
    const pdpi::IrTableDefinition& to_table) {
  auto from_db_table = sonic::AppDbAclTableDefinition(from_table);
  if (!from_db_table.ok()) {
    return gutil::InternalErrorBuilder()
           << "Failed to generate AppDB representation of ACL table from "
           << "existing P4Info: " << from_db_table.status().message();
  }
  ASSIGN_OR_RETURN(auto to_db_table, sonic::AppDbAclTableDefinition(to_table),
                   _.SetPrepend()
                       << "Failed to generate AppDB format for ACL table "
                       << to_table.preamble().alias());

  // We don't bother with the return status code here because the ACL table
  // definition always has a stage.
  ASSIGN_OR_RETURN(std::string from_stage,
                   sonic::kfvFieldLookup(*from_db_table, "stage"));
  ASSIGN_OR_RETURN(std::string to_stage,
                   sonic::kfvFieldLookup(to_db_table, "stage"));

  if (from_stage != to_stage) {
    return gutil::FailedPreconditionErrorBuilder()
           << "ACL tables may not change stage. Cannot transition table '"
           << to_table.preamble().alias() << "' from stage '" << from_stage
           << "' to '" << to_stage << "'";
  }

  return !sonic::kfvEq(*from_db_table, to_db_table);
}

absl::Status CalculateAclDifference(const pdpi::IrP4Info& from,
                                    const pdpi::IrP4Info& to,
                                    P4InfoReconcileTransition& transition) {
  ASSIGN_OR_RETURN(absl::btree_set<std::string> from_acl_table_names,
                   GetAclTableNames(from));
  ASSIGN_OR_RETURN(absl::btree_set<std::string> to_acl_table_names,
                   GetAclTableNames(to));

  SetDifference<std::string> acl_table_diff =
      CalculateSetDifference(from_acl_table_names, to_acl_table_names);

  transition.acl_tables_to_add = std::move(acl_table_diff.added);
  transition.acl_tables_to_delete = std::move(acl_table_diff.deleted);

  for (const std::string& table_name : acl_table_diff.intersection) {
    pdpi::IrTableDefinition from_table = from.tables_by_name().at(table_name);
    pdpi::IrTableDefinition to_table = to.tables_by_name().at(table_name);
    ASSIGN_OR_RETURN(bool modified, IsValidModification(from_table, to_table));
    if (modified) {
      if (pdpi::GetAnnotationBody("nonessential_for_upgrade",
                                  to_table.preamble().annotations())
              .ok()) {
        transition.nonessential_acl_tables_to_modify.push_back(table_name);
      } else {
        transition.essential_acl_tables_to_modify.push_back(table_name);
      }
    }
  }
  return absl::OkStatus();
}

}  // namespace

absl::StatusOr<P4InfoReconcileTransition> CalculateTransition(
    const pdpi::IrP4Info& from, const pdpi::IrP4Info& to) {
  P4InfoReconcileTransition transition;
  RETURN_IF_ERROR(CalculateHashingDifference(from, to, transition));
  RETURN_IF_ERROR(CalculateAclDifference(from, to, transition));
  return transition;
}

absl::StatusOr<absl::flat_hash_map<std::string, ActionProfileResourceCapacity>>
GetUpdatedResourceCapacities(
    const pdpi::IrP4Info& ir_p4info,
    const absl::flat_hash_map<std::string, ActionProfileResourceCapacity>&
        original) {
  absl::flat_hash_map<std::string, ActionProfileResourceCapacity> capacity_map;
  for (const auto& [action_profile_name, action_profile_def] :
       ir_p4info.action_profiles_by_name()) {
    ActionProfileResourceCapacity capacity =
        GetActionProfileResourceCapacity(action_profile_def);
    const ActionProfileResourceCapacity* original_capacity =
        gutil::FindOrNull(original, action_profile_name);
    capacity.current_utilization = original_capacity == nullptr
                                       ? 0
                                       : original_capacity->current_utilization;
    if (capacity.current_utilization > capacity.max_weight_for_all_groups) {
      return gutil::FailedPreconditionErrorBuilder()
             << "The new ForwardingPipelineConfig capacity for action profile '"
             << action_profile_name << "' ("
             << capacity.max_weight_for_all_groups
             << ") is less than the current usage ("
             << capacity.current_utilization << ")";
    }
    // TODO: Check against the current usage.
    if (capacity.current_utilization > 0 &&
        capacity.max_group_size < original_capacity->max_group_size) {
      return gutil::FailedPreconditionErrorBuilder()
             << "The new ForwardingPipelineConfig max group size for action "
             << "profile '" << action_profile_name << "' ("
             << capacity.max_group_size
             << ") is smaller than the original size ("
             << original_capacity->max_group_size
             << "). Shrinking the max group size is currently unsupported.";
    }

    capacity_map.insert_or_assign(action_profile_name, std::move(capacity));
  }
  return capacity_map;
}

}  // namespace p4rt_app
