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
#include "p4rt_app/p4runtime/resource_utilization.h"

#include <algorithm>
#include <cstdint>
#include <optional>
#include <string>
#include <utility>

#include "absl/container/flat_hash_map.h"
#include "absl/log/log.h"
#include "absl/status/statusor.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/entity_keys.h"
#include "p4_pdpi/ir.pb.h"
#include "p4rt_app/p4runtime/entity_update.h"

namespace p4rt_app {
namespace {

absl::StatusOr<std::string> GetActionProfileName(
    const pdpi::IrP4Info& ir_p4info, uint32_t action_profile_id) {
  const pdpi::IrActionProfileDefinition* action_profile_def =
      gutil::FindOrNull(ir_p4info.action_profiles_by_id(), action_profile_id);
  if (action_profile_def == nullptr) {
    return gutil::NotFoundErrorBuilder()
           << "Could not find action profile definition for ID: "
           << action_profile_id;
  }
  return action_profile_def->action_profile().preamble().alias();
}

}  // namespace

absl::StatusOr<TableResources> GetResourceUsageForIrTableEntry(
    const pdpi::IrP4Info& ir_p4info, const pdpi::IrTableEntry& table_entry) {
  TableResources resources{
      .name = table_entry.table_name(),
  };

  const pdpi::IrTableDefinition* table_def =
      gutil::FindOrNull(ir_p4info.tables_by_name(), table_entry.table_name());
  if (table_def == nullptr) {
    return gutil::NotFoundErrorBuilder()
           << "Could not find table definition for: "
           << table_entry.table_name();
  }

  // If the table does not have an action profile then we do not need to include
  // those resources in the result. So we're done.
  if (!table_def->has_action_profile_id()) {
    return resources;
  }

  // Otherwise, compute the resources used.
  ASSIGN_OR_RETURN(
      std::string action_profile_name,
      GetActionProfileName(ir_p4info, table_def->action_profile_id()));
  int32_t actions = 0;
  int64_t total_weight = 0;
  int32_t max_weight = 0;
  for (const pdpi::IrActionSetInvocation& action :
       table_entry.action_set().actions()) {
    ++actions;
    total_weight += action.weight();
    max_weight = std::max(max_weight, action.weight());
  }
  resources.action_profile = ActionProfileResources{
      .name = action_profile_name,
      .number_of_actions = actions,
      .total_weight = total_weight,
      .max_weight = max_weight,
  };

  return resources;
}

absl::StatusOr<TableResources> GetResourceUsageForPiTableEntry(
    const pdpi::IrP4Info& ir_p4info, const p4::v1::TableEntry& table_entry) {
  const pdpi::IrTableDefinition* table_def =
      gutil::FindOrNull(ir_p4info.tables_by_id(), table_entry.table_id());
  if (table_def == nullptr) {
    return gutil::NotFoundErrorBuilder()
           << "Could not find table definition for ID: "
           << table_entry.table_id();
  }
  TableResources resources{
      .name = table_def->preamble().alias(),
  };

  // If the table does not have an action profile then we do need to include
  // those resources in the result. So we're done.
  if (!table_def->has_action_profile_id()) {
    return resources;
  }

  // Otherwise, compute the resources used.
  ASSIGN_OR_RETURN(
      std::string action_profile_name,
      GetActionProfileName(ir_p4info, table_def->action_profile_id()));
  int32_t actions = 0;
  int64_t total_weight = 0;
  int32_t max_weight = 0;
  for (const p4::v1::ActionProfileAction& action :
       table_entry.action()
           .action_profile_action_set()
           .action_profile_actions()) {
    ++actions;
    total_weight += action.weight();
    max_weight = std::max(max_weight, action.weight());
  }
  resources.action_profile = ActionProfileResources{
      .name = action_profile_name,
      .number_of_actions = actions,
      .total_weight = total_weight,
      .max_weight = max_weight,
  };

  return resources;
}

ActionProfileResourceCapacity GetActionProfileResourceCapacity(
    const pdpi::IrActionProfileDefinition& action_profile_def) {
  return ActionProfileResourceCapacity{
      .action_profile = action_profile_def.action_profile(),
      .current_total_weight = 0,
      .current_total_members = 0,
  };
}

absl::StatusOr<TableResources> VerifyCapacityAndGetTableResourceChange(
    const pdpi::IrP4Info& ir_p4info, const EntityUpdate& update,
    const absl::flat_hash_map<pdpi::EntityKey, p4::v1::Entity>& entity_cache,
    const absl::flat_hash_map<std::string, ActionProfileResourceCapacity>&
        capacity_by_action_profile_name,
    absl::flat_hash_map<std::string, int64_t>& current_batch_resources) {
  TableResources resources;
  // This function currently only applies to table entries.
  if (update.entry.entity_case() != pdpi::IrEntity::kTableEntry) {
    return resources;
  }
  std::optional<TableResources> new_resources;
  std::optional<TableResources> old_resources;

  // For an insert or modify we will need the table resources for the new table
  // entry.
  if (update.update_type == p4::v1::Update::INSERT ||
      update.update_type == p4::v1::Update::MODIFY) {
    absl::StatusOr<TableResources> table_resources =
        GetResourceUsageForIrTableEntry(ir_p4info, update.entry.table_entry());
    if (!table_resources.ok()) {
      LOG(WARNING) << "Could not get table entry's resources: "
                   << table_resources.status();
      return gutil::InvalidArgumentErrorBuilder()
             << "[P4RT App] Could not get table resources.";
    }

    new_resources = *std::move(table_resources);
  }

  // For a modify or delete we will need the table resources for the old table
  // entry.
  if (update.update_type == p4::v1::Update::MODIFY ||
      update.update_type == p4::v1::Update::DELETE) {
    const auto* cache_entry =
        gutil::FindOrNull(entity_cache, update.entity_key);
    if (cache_entry == nullptr) {
      return gutil::NotFoundErrorBuilder() << "[P4RT App] Could not find cache "
                                              "entry for resource accounting.";
    }
    absl::StatusOr<TableResources> cache_resources =
        GetResourceUsageForPiTableEntry(ir_p4info,
                                        (*cache_entry).table_entry());
    if (!cache_resources.ok()) {
      LOG(WARNING) << "Could not get cached entry's resources: "
                   << cache_resources.status();
      return gutil::NotFoundErrorBuilder()
             << "[P4RT App] Could not get resources for cached table entry.";
    }
    old_resources = *std::move(cache_resources);
  }

  // We add any new resources that will be needed, and subtract any old
  // resources that will get removed. For INSERT and DELETE only the new or old
  // resource is used, but for MODIFY both will be used. If we are adding new
  // resources we also have to take into consideration if the request has too
  // many actions or too much weight.
  int32_t actions_in_new_request = 0;
  int32_t weight_in_new_request = 0;
  if (new_resources.has_value() && new_resources->action_profile.has_value()) {
    resources.name = new_resources->name;
    resources.action_profile = new_resources->action_profile;
    actions_in_new_request = new_resources->action_profile->number_of_actions;
    weight_in_new_request = new_resources->action_profile->total_weight;
  }
  if (old_resources.has_value() && old_resources->action_profile.has_value()) {
    resources.name = old_resources->name;
    if (!resources.action_profile.has_value()) {
      resources.action_profile = ActionProfileResources{
          .name = old_resources->action_profile->name,
      };
    }
    resources.action_profile->number_of_actions -=
        old_resources->action_profile->number_of_actions;
    resources.action_profile->total_weight -=
        old_resources->action_profile->total_weight;
  }

  // If the request will affect the action profile resources then verify we will
  // not exceed the reserved amount.
  if (resources.action_profile.has_value()) {
    const std::string& profile_name = resources.action_profile->name;

    const auto* current_capacity =
        gutil::FindOrNull(capacity_by_action_profile_name, profile_name);
    if (current_capacity == nullptr) {
      LOG(WARNING) << "Could not find the current ActionProfile capacity for '"
                   << profile_name << "'";
      return gutil::NotFoundErrorBuilder()
             << "[P4RT App] Could not get the current capacity data for '"
             << profile_name << "'";
    }

    // Branch on whether the action profile uses SumOfMembers or SumOfWeights
    // size semantics.
    if (UsesSumOfMembers(*current_capacity)) {
      // With the SumOfMembers semantics:
      // 1. The number of members in the request can't exceed the
      //    `max_group_size`.
      // 2. The weight of any one member in the request can't exceed the
      //    `max_weight_per_member`.
      // 3. The total number of members across all groups can't exceed the
      //    `size`.

      // Check that the number of members doesn't exceed the `max_group_size`
      // (unless it's zero in which case any size is allowed).
      if (auto max_members_per_group = GetMaxMembersPerGroup(*current_capacity);
          max_members_per_group.has_value() && *max_members_per_group != 0 &&
          actions_in_new_request > *max_members_per_group) {
        return gutil::InvalidArgumentErrorBuilder()
               << "[P4RT App] too many actions. The max allowed is "
               << *max_members_per_group << ", but got "
               << actions_in_new_request;
      }

      // Check that no action has too high weight (unless it's zero in which
      // case any weight is allowed).
      if (auto max_weight_per_member = GetMaxWeightPerMember(*current_capacity);
          max_weight_per_member.has_value() && *max_weight_per_member != 0 &&
          resources.action_profile->max_weight > *max_weight_per_member) {
        return gutil::InvalidArgumentErrorBuilder()
               << "[P4RT App] Action had too high weight. The max allowed is "
               << *max_weight_per_member << ", but got "
               << resources.action_profile->max_weight;
      }

      // Ensure that there are enough members available for this update.
      int64_t projected_utilization =
          current_capacity->current_total_members +
          current_batch_resources[profile_name] +
          resources.action_profile->number_of_actions;
      if (auto max_total_members = GetMaxMembersForAllGroups(*current_capacity);
          max_total_members.has_value() && *max_total_members != 0 &&
          projected_utilization > *max_total_members) {
        return gutil::ResourceExhaustedErrorBuilder()
               << "[P4RT App] not enough resources to fit in '" << profile_name
               << "' using SumOfMembers semantics. Projected utilization was '"
               << projected_utilization << "' but we can only fit '"
               << *max_total_members << "'.";
      }
    } else if (UsesSumOfWeights(*current_capacity)) {
      // With the SumOfWeights semantics:
      // 1. The weight in the request can't exceed the `max_group_size`.
      // 2. The total weight across all groups can't exceed the `size`.

      // Check that the weight doesn't exceed the `max_group_size` (unless it's
      // zero in which case any size is allowed).
      if (auto max_weight_per_group = GetMaxWeightPerGroup(*current_capacity);
          max_weight_per_group.has_value() && *max_weight_per_group != 0 &&
          weight_in_new_request > *max_weight_per_group) {
        return gutil::InvalidArgumentErrorBuilder()
               << "[P4RT App] too much weight in actions. The max allowed is "
               << *max_weight_per_group << ", but got "
               << weight_in_new_request;
      }

      // Ensure that there is enough weight available for this update.
      int64_t projected_utilization = current_capacity->current_total_weight +
                                      current_batch_resources[profile_name] +
                                      resources.action_profile->total_weight;
      if (auto max_total_weight = GetMaxWeightForAllGroups(*current_capacity);
          max_total_weight.has_value() && *max_total_weight != 0 &&
          projected_utilization > *max_total_weight) {
        return gutil::ResourceExhaustedErrorBuilder()
               << "[P4RT App] not enough resources to fit in '" << profile_name
               << "' using SumOfWeights semantics. Projected utilization was '"
               << projected_utilization << "' but we can only fit '"
               << *max_total_weight << "'.";
      }
    } else {
      return gutil::InvalidArgumentErrorBuilder()
             << "[P4RT App] Expected an action profile using either "
                "SumOfMembers or SumOfWeights semantics, but got one that uses "
                "neither: "
             << current_capacity->action_profile.DebugString();
    }
  }

  return resources;
}

}  // namespace p4rt_app
