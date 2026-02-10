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
#ifndef PINS_P4RT_APP_P4RUNTIME_UPDATE_H_
#define PINS_P4RT_APP_P4RUNTIME_UPDATE_H_

#include <cstdint>
#include <optional>
#include <string>

#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/entity_keys.h"
#include "p4_pdpi/ir.pb.h"
#include "p4rt_app/sonic/app_db_manager.h"

namespace p4rt_app {

// This file defines data structures for managing individual update requests
// from P4.

// Action profiles are used to model things like WCMP where we can have multiple
// actions with different weights. Resource accounting can be measured either
// against the total number of actions, or the sum total of all the action
// weights.
struct ActionProfileResources {
  std::string name;
  int32_t number_of_actions = 0;
  int64_t total_weight = 0;
};

// Each table resource usually only counts as 1 (i.e. one table entry), but
// depending on the table they may include an action profile (e.g. WCMP).
struct TableResources {
  std::string name;
  std::optional<ActionProfileResources> action_profile;
};

// This struct holds all the information needed to process a P4 update in P4RT.
struct EntityUpdate {
  // The IR translation of the PI request.
  pdpi::IrEntity entry;

  // Specifies if this request is an INSERT MODIFY or DELETE.
  p4::v1::Update::Type update_type;

  // Normalized PI entities. Note this will be semantically the same as the
  // original request, but does not have to be syntactically the same.
  p4::v1::Entity pi_entity;

  // A unique hash of the entries match fields. Used to identify duplicates and
  // any caching of entries.
  pdpi::EntityKey entity_key;

  // The net utilization change for table entries with group actions. If the
  // update_type is an insert then this value will simply be the resources for
  // the entry. If the update_type is a modify then this value is the difference
  // between the new and old entries. If the update_type is a delete then this
  // value is the resources of the old entry.
  // Note: This is only relevant at the moment for tables with action profiles.
  TableResources resource_utilization_change;

  // The AppDb format of for this update.
  sonic::AppDbUpdate app_db_update;

  // A pointer to the response in the IrWriteResponse for this update.
  pdpi::IrUpdateStatus* status;
};

}  // namespace p4rt_app

#endif  // PINS_P4RT_APP_P4RUNTIME_UPDATE_H_
