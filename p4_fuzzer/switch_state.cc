// Copyright 2021 Google LLC
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
#include "p4_fuzzer/switch_state.h"

#include <algorithm>
#include <iterator>
#include <set>
#include <string>

#include "absl/algorithm/container.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "glog/logging.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/internal/ordered_map.h"
#include "p4_pdpi/ir.pb.h"

namespace p4_fuzzer {

using ::gutil::FindOrDie;
using ::p4::v1::TableEntry;
using ::p4::v1::Update;
using ::pdpi::IrP4Info;

SwitchState::SwitchState(IrP4Info ir_p4info) : ir_p4info_(ir_p4info) {
  for (auto& [table_id, table] : ir_p4info_.tables_by_id()) {
    tables_[table_id] = TableEntries();
  }
}

bool SwitchState::AllTablesEmpty() const {
  for (auto table_id : AllTableIds()) {
    if (!IsTableEmpty(table_id)) {
      return false;
    }
  }

  return true;
}

bool SwitchState::IsTableFull(const uint32_t table_id) const {
  return !CanAccommodateInserts(table_id, 1);
}

int64_t SwitchState::GetNumTableEntries(const uint32_t table_id) const {
  return FindOrDie(tables_, table_id).size();
}

int64_t SwitchState::GetNumTableEntries() const {
  int result = 0;
  for (const auto& [key, table] : tables_) {
    result += table.size();
  }
  return result;
}

const std::vector<uint32_t> SwitchState::AllTableIds() const {
  std::vector<uint32_t> table_ids;

  for (auto& [key, table] : ir_p4info_.tables_by_id()) {
    table_ids.push_back(key);
  }

  return table_ids;
}

bool SwitchState::CanAccommodateInserts(const uint32_t table_id,
                                        const int n) const {
  return (FindOrDie(ir_p4info_.tables_by_id(), table_id).size() -
          GetNumTableEntries(table_id)) >= n;
}

bool SwitchState::IsTableEmpty(const uint32_t table_id) const {
  return FindOrDie(tables_, table_id).empty();
}

std::vector<TableEntry> SwitchState::GetTableEntries(
    const uint32_t table_id) const {
  std::vector<TableEntry> result;

  for (const auto& [key, entry] : FindOrDie(tables_, table_id)) {
    result.push_back(entry);
  }

  return result;
}

absl::optional<TableEntry> SwitchState::GetTableEntry(TableEntry entry) const {
  auto table = FindOrDie(tables_, entry.table_id());

  if (auto table_iter = table.find(TableEntryKey(entry));
      table_iter != table.end()) {
    auto [table_key, table_entry] = *table_iter;
    return table_entry;
  }

  return absl::nullopt;
}

absl::Status SwitchState::ApplyUpdate(const Update& update) {
  const int table_id = update.entity().table_entry().table_id();

  auto& table = FindOrDie(tables_, table_id);

  TableEntry table_entry = update.entity().table_entry();

  switch (update.type()) {
    case Update::INSERT: {
      auto [iter, not_present] =
          table.insert(/*value=*/{TableEntryKey(table_entry), table_entry});

      if (!not_present) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Cannot install the same table entry multiple times. Update: "
               << update.DebugString();
      }
      break;
    }

    case Update::DELETE: {
      if (tables_[table_id].erase(TableEntryKey(table_entry)) != 1) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Cannot erase non-existent table entries. Update: "
               << update.DebugString();
      }
      break;
    }

    case Update::MODIFY: {
      auto [iter, not_present] =
          table.insert(/*value=*/{TableEntryKey(table_entry), table_entry});

      if (not_present) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Cannot modify a non-existing update. Update: "
               << update.DebugString();
      }
      break;
    }

    default:
      LOG(FATAL) << "Update of unsupported type: " << update.DebugString();
  }
  return absl::OkStatus();
}

std::string SwitchState::SwitchStateSummary() const {
  if (tables_.empty()) return std::string("EmptyState()");
  std::string res = "";
  // Ordered is used to get a deterministic order for the summary.
  for (const auto& [table_id, table] : Ordered(tables_)) {
    const pdpi::IrTableDefinition& table_def =
        FindOrDie(ir_p4info_.tables_by_id(), table_id);
    const std::string& table_name = table_def.preamble().alias();
    int max_size = table_def.size();
    int current_size = table.size();

    absl::StrAppendFormat(&res, "\n % 12d% 12d    %s", current_size, max_size,
                          table_name);

    // Mark tables where we have exceeded their resource limits.
    if (current_size > max_size) {
      absl::StrAppend(&res, "*");
    }

    // If the table is a WCMP table, then we also print its total weight and
    // max group weight. Only WCMP tables using one-shot programming are
    // supported.
    if (table_def.implementation_id_case() ==
        pdpi::IrTableDefinition::kActionProfileId) {
      int max_weight = 0;
      int total_weight = 0;
      int total_actions = 0;
      for (auto& [_, table_entry] : table) {
        int this_entry_weight = 0;
        for (const p4::v1::ActionProfileAction& action :
             table_entry.action()
                 .action_profile_action_set()
                 .action_profile_actions()) {
          this_entry_weight += action.weight();
        }
        max_weight = std::max(max_weight, this_entry_weight);
        total_weight += this_entry_weight;
        total_actions += table_entry.action()
                             .action_profile_action_set()
                             .action_profile_actions_size();
      }

      const p4::config::v1::ActionProfile& action_profile =
          FindOrDie(ir_p4info_.action_profiles_by_id(),
                    table_def.action_profile_id())
              .action_profile();

      absl::StrAppendFormat(&res, "\n % 12d% 12d    %s.total_weight",
                            total_weight, action_profile.size(), table_name);
      // Mark if we have exceeded the total weight.
      if (total_weight > action_profile.size()) {
        absl::StrAppend(&res, "*");
      }

      absl::StrAppendFormat(&res, "\n % 12d% 12s    %s.total_actions",
                            total_actions, "N/A", table_name);

      absl::StrAppendFormat(&res, "\n % 12d% 12d    %s.max_weight", max_weight,
                            action_profile.max_group_size(), table_name);
      // Mark if we have exceeded the max weight for a given group.
      if (max_weight > action_profile.max_group_size()) {
        absl::StrAppend(&res, "*");
      }
    }
  }
  return absl::StrFormat(
      "State(\n % 12s% 12s    table_name\n % 12d% 12s    total number of "
      "flows%s\n * marks tables where max size > current size.\n)",
      "current size", "max size", GetNumTableEntries(), "N/A", res);
}


}  // namespace p4_fuzzer
