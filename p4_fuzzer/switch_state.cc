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

#include "absl/algorithm/container.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "glog/logging.h"
#include "gutil/collections.h"
#include "gutil/status.h"

namespace p4_fuzzer {

using ::absl::StrAppend;
using ::absl::StrCat;
using ::absl::StrFormat;
using ::gutil::FindOrDie;
using ::p4::v1::TableEntry;
using ::p4::v1::Update;
using ::pdpi::IrP4Info;

namespace {

std::string GetTableName(const IrP4Info& info, const uint32_t table_id) {
  return FindOrDie(info.tables_by_id(), table_id).preamble().alias();
}

}  // namespace

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
  int total = 0;
  for (const auto& [table_id, table] : tables_) {
    total += table.size();

    StrAppend(&res, "\n  ", absl::StrFormat("% 10d", table.size()), " ",
              GetTableName(ir_p4info_, table_id));
  }

  return StrCat("State(", "\n  ", StrFormat("% 10d", total),
                " total number of flows", res, "\n", ")");
}

}  // namespace p4_fuzzer
