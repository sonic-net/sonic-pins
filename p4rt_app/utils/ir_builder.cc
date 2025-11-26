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

#include "p4rt_app/utils/ir_builder.h"

#include <utility>

#include "p4_pdpi/ir.pb.h"

namespace p4rt_app {

IrP4InfoBuilder& IrP4InfoBuilder::table(pdpi::IrTableDefinition ir_table) {
  if (ir_table.preamble().id() == 0) {
    ir_table.mutable_preamble()->set_id(++table_id_);
  }
  int table_id = ir_table.preamble().id();

  if (auto action_profile = action_profile_associations_.find(table_id);
      action_profile != action_profile_associations_.end()) {
    ir_table.set_action_profile_id(action_profile->second);
    // One shot is the only type of action profile used in PiNS.
    ir_table.set_uses_oneshot(true);
    action_profile_associations_.erase(action_profile);
  }

  (*p4info_.mutable_tables_by_id())[ir_table.preamble().id()] = ir_table;
  (*p4info_.mutable_tables_by_name())[ir_table.preamble().alias()] =
      std::move(ir_table);
  return *this;
}

IrP4InfoBuilder& IrP4InfoBuilder::action_profile(
    pdpi::IrActionProfileDefinition ir_action_profile) {
  auto& preamble =
      *ir_action_profile.mutable_action_profile()->mutable_preamble();
  if (preamble.id() == 0) {
    preamble.set_id(++action_profile_id_);
  }

  for (int table_id : ir_action_profile.action_profile().table_ids()) {
    if (p4info_.tables_by_id().contains(table_id)) {
      auto& table_by_id = p4info_.mutable_tables_by_id()->at(table_id);
      table_by_id.set_action_profile_id(preamble.id());
      // One shot is the only type of action profile used in PiNS.
      table_by_id.set_uses_oneshot(true);
      p4info_.mutable_tables_by_name()
          ->at(table_by_id.preamble().alias())
          .set_action_profile_id(preamble.id());
      p4info_.mutable_tables_by_name()
          ->at(table_by_id.preamble().alias())
          .set_uses_oneshot(true);
    } else {
      action_profile_associations_.insert({table_id, preamble.id()});
    }
  }

  (*p4info_.mutable_action_profiles_by_id())[preamble.id()] = ir_action_profile;
  (*p4info_.mutable_action_profiles_by_name())[preamble.name()] =
      std::move(ir_action_profile);

  return *this;
}

}  // namespace p4rt_app

