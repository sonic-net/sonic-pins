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
#include <string>

#include "absl/container/flat_hash_map.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_format.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/entity_keys.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4rt_app/sonic/app_db_manager.h"

namespace p4rt_app {

// Given an IR table entry this method will return the number of resources used
// by that entry. A NOT_FOUND error can be returned if either the table
// definition cannot be found, or if an action profile definition is used and
// cannot be found.
absl::StatusOr<sonic::TableResources>
GetResourceUsageForIrTableEntry(const pdpi::IrP4Info &ir_p4info,
                                const pdpi::IrTableEntry &table_entry);

// Given an PI table entry this method will return the number of resources used
// by that entry. A NOT_FOUND error can be returned if either the table
// definition cannot be found, or if an action profile definition is used and
// cannot be found.
absl::StatusOr<sonic::TableResources>
GetResourceUsageForPiTableEntry(const pdpi::IrP4Info &ir_p4info,
                                const p4::v1::TableEntry &table_entry);

// Action profiles in P4 allow us to group multiple actions together, and for
// any given packet only one action is applied. The applied action is chosen
// by a selector (e.g. hash). These selectors can place hard limits on the
// profile that need to be enforced.
struct ActionProfileResourceCapacity {
  int32_t max_group_size = 0;
  int64_t max_weight_for_all_groups = 0;

  // Utilization can be based SumOfActions or SumOfWeights in the P4Info. Today
  // we always assume SumOfWeights.
  int64_t current_utilization = 0;

  template <typename Sink>
  friend void AbslStringify(Sink& sink,
                            const ActionProfileResourceCapacity& capacity) {
    absl::Format(&sink, R"({
  max_group_size = %d,
  max_weight_for_all_groups = %d,
  current_utilization = %d,
})",
                 capacity.max_group_size, capacity.max_weight_for_all_groups,
                 capacity.current_utilization);
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
absl::StatusOr<sonic::TableResources> VerifyCapacityAndGetTableResourceChange(
    const pdpi::IrP4Info &ir_p4info, const sonic::AppDbEntry &app_db_entry,
    const absl::flat_hash_map<pdpi::EntityKey, p4::v1::Entity> &entity_cache,
    const absl::flat_hash_map<std::string, ActionProfileResourceCapacity>
        &capacity_by_action_profile_name,
    absl::flat_hash_map<std::string, int64_t> &current_batch_resources);

} // namespace p4rt_app

#endif // PINS_P4RT_APP_P4RUNTIME_RESOURCE_UTILIZATION_H_
