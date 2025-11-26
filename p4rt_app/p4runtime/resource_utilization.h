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
#ifndef PINS_P4RT_APP_P4RUNTIME_RESOURCE_UTILIZATION_H_
#define PINS_P4RT_APP_P4RUNTIME_RESOURCE_UTILIZATION_H_

#include <cstdint>
#include <optional>
#include <string>

#include "absl/container/flat_hash_map.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_format.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/entity_keys.h"
#include "p4_pdpi/ir.pb.h"
#include "p4rt_app/p4runtime/entity_update.h"

namespace p4rt_app {

// Given an IR table entry this method will return the number of resources used
// by that entry. A NOT_FOUND error can be returned if either the table
// definition cannot be found, or if an action profile definition is used and
// cannot be found.
absl::StatusOr<TableResources> GetResourceUsageForIrTableEntry(
    const pdpi::IrP4Info& ir_p4info, const pdpi::IrTableEntry& table_entry);

// Given an PI table entry this method will return the number of resources used
// by that entry. A NOT_FOUND error can be returned if either the table
// definition cannot be found, or if an action profile definition is used and
// cannot be found.
absl::StatusOr<TableResources> GetResourceUsageForPiTableEntry(
    const pdpi::IrP4Info& ir_p4info, const p4::v1::TableEntry& table_entry);

// Action profiles in P4 allow us to group multiple actions together, and for
// any given packet only one action is applied. The applied action is chosen
// by a selector (e.g. hash). These selectors can place hard limits on the
// profile that need to be enforced.
struct ActionProfileResourceCapacity {
  // Records the `max_group_size`, the `selector_size_semantics` and the related
  // max `size`.
  p4::config::v1::ActionProfile action_profile;

  int64_t current_total_weight = 0;
  int64_t current_total_members = 0;

  template <typename Sink>
  friend void AbslStringify(Sink& sink,
                            const ActionProfileResourceCapacity& capacity) {
    absl::Format(
        &sink, R"({
  max_group_size = %d,
  max_weight_for_all_groups = %s,
  max_members_for_all_groups = %s,
  max_weight_per_member = %s,
  current_total_weight = %d,
  current_total_members = %d,
})",
        capacity.action_profile.max_group_size(),
        !capacity.action_profile.has_sum_of_members()
            ? std::to_string(capacity.action_profile.size())
            : "N/A",
        capacity.action_profile.has_sum_of_members()
            ? std::to_string(capacity.action_profile.size())
            : "N/A",
        capacity.action_profile.has_sum_of_members()
            ? std::to_string(
                  capacity.action_profile.sum_of_members().max_member_weight())
            : "N/A",
        capacity.current_total_weight, capacity.current_total_members);
  }
};

// Parses an IrActionProfileDefinition for resource capacity information.
ActionProfileResourceCapacity GetActionProfileResourceCapacity(
    const pdpi::IrActionProfileDefinition &action_profile_def);

// Computes the number of resources used by a given table entry. For inserts the
// resource usage will depend on the entry being inserted (i.e. always
// positive). For deletes the resource usage will depend on the entry being
// removed from the table cache (i.e. always negative). For modifies the
// resource usage will be the difference between the new and old entry (i.e. may
// use more or fewer resources).
//
// When determining if a request has enough space we need to take into
// consideration all the requests that came before it in the batch (i.e.
// batch_resource_utilization).
//
// Note that this method assumes SumOfWeights today and does not consider
// SumOfActions selectors.
absl::StatusOr<TableResources> VerifyCapacityAndGetTableResourceChange(
    const pdpi::IrP4Info& ir_p4info, const EntityUpdate& update,
    const absl::flat_hash_map<pdpi::EntityKey, p4::v1::Entity>& entity_cache,
    const absl::flat_hash_map<std::string, ActionProfileResourceCapacity>&
        capacity_by_action_profile_name,
    absl::flat_hash_map<std::string, int64_t>& current_batch_resources);

// -- Getters ------------------------------------------------------------------
// TODO: These should be moved into a class based version of
// ActionProfileResourceCapacity (if they're still necessary at that point).
inline bool UsesSumOfMembers(const ActionProfileResourceCapacity& capacity) {
  return capacity.action_profile.has_sum_of_members();
}

inline bool UsesSumOfWeights(const ActionProfileResourceCapacity& capacity) {
  // If an action profile doesn't use SumOfMembers, it uses SumOfWeights.
  return !UsesSumOfMembers(capacity);
}

inline std::optional<int64_t> GetMaxWeightForAllGroups(
    const ActionProfileResourceCapacity& capacity) {
  if (UsesSumOfWeights(capacity)) {
    return capacity.action_profile.size();
  }
  return std::nullopt;
};

inline std::optional<int32_t> GetMaxWeightPerGroup(
    const ActionProfileResourceCapacity& capacity) {
  if (UsesSumOfWeights(capacity)) {
    return capacity.action_profile.max_group_size();
  }
  return std::nullopt;
};

inline std::optional<int64_t> GetMaxMembersForAllGroups(
    const ActionProfileResourceCapacity& capacity) {
  if (UsesSumOfMembers(capacity)) {
    return capacity.action_profile.size();
  }
  return std::nullopt;
};

inline std::optional<int32_t> GetMaxMembersPerGroup(
    const ActionProfileResourceCapacity& capacity) {
  if (UsesSumOfMembers(capacity)) {
    return capacity.action_profile.max_group_size();
  }
  return std::nullopt;
};

inline std::optional<int32_t> GetMaxWeightPerMember(
    const ActionProfileResourceCapacity& capacity) {
  if (UsesSumOfMembers(capacity)) {
    return capacity.action_profile.sum_of_members().max_member_weight();
  }
  return std::nullopt;
};

}  // namespace p4rt_app

#endif // PINS_P4RT_APP_P4RUNTIME_RESOURCE_UTILIZATION_H_
