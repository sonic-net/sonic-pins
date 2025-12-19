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

#include <cstdint>
#include <optional>
#include <string>
#include <utility>

#include "absl/container/flat_hash_map.h"
#include "absl/log/log.h"
#include "absl/status/statusor.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/entity_keys.h"
#include "p4_pdpi/ir.pb.h"
#include "p4rt_app/sonic/app_db_manager.h"

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

absl::StatusOr<sonic::TableResources> GetResourceUsageForIrTableEntry(
    const pdpi::IrP4Info& ir_p4info, const pdpi::IrTableEntry& table_entry) {
  sonic::TableResources resources{
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
  for (const pdpi::IrActionSetInvocation& action :
       table_entry.action_set().actions()) {
    ++actions;
    total_weight += action.weight();
  }
  resources.action_profile = sonic::ActionProfileResources{
      .name = action_profile_name,
      .number_of_actions = actions,
      .total_weight = total_weight,
  };

  return resources;
}

absl::StatusOr<sonic::TableResources> GetResourceUsageForPiTableEntry(
    const pdpi::IrP4Info& ir_p4info, const p4::v1::TableEntry& table_entry) {
  const pdpi::IrTableDefinition* table_def =
      gutil::FindOrNull(ir_p4info.tables_by_id(), table_entry.table_id());
  if (table_def == nullptr) {
    return gutil::NotFoundErrorBuilder()
           << "Could not find table definition for ID: "
           << table_entry.table_id();
  }
  sonic::TableResources resources{
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
  for (const p4::v1::ActionProfileAction& action :
       table_entry.action()
           .action_profile_action_set()
           .action_profile_actions()) {
    ++actions;
    total_weight += action.weight();
  }
  resources.action_profile = sonic::ActionProfileResources{
      .name = action_profile_name,
      .number_of_actions = actions,
      .total_weight = total_weight,
  };

  return resources;
}

ActionProfileResourceCapacity GetActionProfileResourceCapacity(
    const pdpi::IrActionProfileDefinition& action_profile_def) {
  return ActionProfileResourceCapacity{
      .max_group_size = action_profile_def.action_profile().max_group_size(),

      // TODO: replace with max_member_weight.
      // We use the profile size as a workaround for the max weight for
      // all groups in a selector today.
      .max_weight_for_all_groups = action_profile_def.action_profile().size(),
  };
}

absl::StatusOr<sonic::TableResources> VerifyCapacityAndGetTableResourceChange(
    const pdpi::IrP4Info& ir_p4info, const sonic::AppDbEntry& app_db_entry,
    const absl::flat_hash_map<pdpi::EntityKey, p4::v1::Entity>& entity_cache,
    const absl::flat_hash_map<std::string, ActionProfileResourceCapacity>&
        capacity_by_action_profile_name,
    absl::flat_hash_map<std::string, int64_t>& current_batch_resources) {
  sonic::TableResources resources;
  // This function currently only applies to table entries.
  if (app_db_entry.entry.entity_case() != pdpi::IrEntity::kTableEntry) {
    return resources;
  }
  std::optional<sonic::TableResources> new_resources;
  std::optional<sonic::TableResources> old_resources;

  // For an insert or modify we will need the table resources for the new table
  // entry.
  if (app_db_entry.update_type == p4::v1::Update::INSERT ||
      app_db_entry.update_type == p4::v1::Update::MODIFY) {
    absl::StatusOr<sonic::TableResources> table_resources =
        GetResourceUsageForIrTableEntry(ir_p4info,
                                        app_db_entry.entry.table_entry());
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
  if (app_db_entry.update_type == p4::v1::Update::MODIFY ||
      app_db_entry.update_type == p4::v1::Update::DELETE) {
    const auto* cache_entry =
        gutil::FindOrNull(entity_cache, app_db_entry.entity_key);
    if (cache_entry == nullptr) {
      return gutil::NotFoundErrorBuilder() << "[P4RT App] Could not find cache "
                                              "entry for resource accounting.";
    }
    absl::StatusOr<sonic::TableResources> cache_resources =
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
  // many actions.
  int32_t actions_in_new_request = 0;
  if (new_resources.has_value() && new_resources->action_profile.has_value()) {
    resources.name = new_resources->name;
    resources.action_profile = new_resources->action_profile;
    actions_in_new_request = new_resources->action_profile->number_of_actions;
  }
  if (old_resources.has_value() && old_resources->action_profile.has_value()) {
    resources.name = old_resources->name;
    if (!resources.action_profile.has_value()) {
      resources.action_profile = sonic::ActionProfileResources{
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
      LOG(WARNING) << "Could not find the current ActionProfile capcity for '"
                   << profile_name << "'";
      return gutil::NotFoundErrorBuilder()
             << "[P4RT App] Could not get the current capacity data for '"
             << profile_name << "'";
    }

    if (actions_in_new_request > current_capacity->max_group_size) {
      return gutil::ResourceExhaustedErrorBuilder()
             << "[P4RT App] too many actions. The max allowed is "
             << current_capacity->max_group_size << ", but got "
             << actions_in_new_request;
    }

    int64_t projected_utilization =
        current_capacity->current_utilization +
        current_batch_resources[resources.action_profile->name] +
        resources.action_profile->total_weight;
    if (projected_utilization > current_capacity->max_weight_for_all_groups) {
      return gutil::ResourceExhaustedErrorBuilder()
             << "[P4RT App] not enough resources to fit in '" << profile_name
             << "'.";
    }
  }

  return resources;
}

}  // namespace p4rt_app
