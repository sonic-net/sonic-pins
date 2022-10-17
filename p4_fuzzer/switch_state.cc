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
#include <cstdint>
#include <functional>
#include <iterator>
#include <optional>
#include <set>
#include <string>
#include <vector>

#include "absl/algorithm/container.h"
#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "glog/logging.h"
#include "google/protobuf/util/message_differencer.h"
#include "gutil/collections.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/internal/ordered_map.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"

namespace p4_fuzzer {

using ::gutil::FindOrDie;
using ::gutil::PrintTextProto;
using ::p4::v1::TableEntry;
using ::p4::v1::Update;
using ::pdpi::IrP4Info;
using ::pdpi::IrTableEntry;

/*absl::StatusOr<TableEntry> CanonicalizeTableEntry(const IrP4Info& info,
                                                  const TableEntry& entry,
                                                  bool key_only) {
  ASSIGN_OR_RETURN(IrTableEntry ir_entry,
                   pdpi::PiTableEntryToIr(info, entry, key_only),
                   _ << "Could not canonicalize: PiToIr Error\n"
                     << entry.DebugString());
  ASSIGN_OR_RETURN(TableEntry canonical_entry,
                   IrTableEntryToPi(info, ir_entry, key_only),
                   _ << "Could not canonicalize: IrToPi Error\n"
                     << entry.DebugString());
  return canonical_entry;
}*/

absl::StatusOr<TableEntry> CanonicalizeTableEntry(const IrP4Info& info,
                                                  const TableEntry& entry,
                                                  bool key_only) {
  auto pdpi_options = pdpi::TranslationOptions{
      .key_only = key_only,
  };
  ASSIGN_OR_RETURN(IrTableEntry ir_entry,
                   pdpi::PiTableEntryToIr(info, entry, pdpi_options),
                   _ << "Could not canonicalize: PiToIr Error\n"
                     << entry.DebugString());
  ASSIGN_OR_RETURN(TableEntry canonical_entry,
                   IrTableEntryToPi(info, ir_entry, pdpi_options),
                   _ << "Could not canonicalize: IrToPi Error\n"
                     << entry.DebugString());
  return canonical_entry;
}

SwitchState::SwitchState(IrP4Info ir_p4info)
    : ir_p4info_(std::move(ir_p4info)) {
  for (auto& [table_id, table] : ir_p4info_.tables_by_id()) {
    tables_[table_id] = TableEntries();
    canonical_tables_[table_id] = CanonicalTableEntries();
  }
}

void SwitchState::ClearTableEntries() {
  *this = SwitchState(std::move(ir_p4info_));
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
  // absl::c_sort(table_ids);

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

std::vector<TableEntry> SwitchState::GetCanonicalTableEntries(
    const uint32_t table_id) const {
  std::vector<TableEntry> result;

  for (const auto& [key, entry] : FindOrDie(canonical_tables_, table_id)) {
    result.push_back(entry);
  }

  return result;
}

std::optional<TableEntry> SwitchState::GetTableEntry(
    const TableEntry& entry) const {
  const TableEntries& table = FindOrDie(tables_, entry.table_id());

  if (auto table_iter = table.find(pdpi::TableEntryKey(entry));
      table_iter != table.end()) {
    auto [table_key, table_entry] = *table_iter;
    return table_entry;
  }

  return absl::nullopt;
}

std::optional<TableEntry> SwitchState::GetCanonicalTableEntry(
    const TableEntry& entry) const {
  const CanonicalTableEntries& table =
      FindOrDie(canonical_tables_, entry.table_id());

  if (auto table_iter = table.find(pdpi::TableEntryKey(entry));
      table_iter != table.end()) {
    auto [table_key, table_entry] = *table_iter;
    return table_entry;
  }

  return absl::nullopt;
}

absl::Status SwitchState::ApplyUpdate(const Update& update) {
  const int table_id = update.entity().table_entry().table_id();

  auto& table = FindOrDie(tables_, table_id);
  auto& canonical_table = FindOrDie(canonical_tables_, table_id);

  const TableEntry& table_entry = update.entity().table_entry();
  // TODO: PDPI IR Update translation currently does not properly
  // ignore non-key fields on DELETE updates. Therefore, information to ignore
  // non-key fields is explitcitly passed for canonicalization.
  ASSIGN_OR_RETURN(
      const TableEntry& canonical_table_entry,
      CanonicalizeTableEntry(ir_p4info_, table_entry,
                             /*key_only=*/update.type() == Update::DELETE));

  switch (update.type()) {
    case Update::INSERT: {
      auto [iter, not_present] =
          table.insert(/*value=*/{pdpi::TableEntryKey(table_entry), table_entry});

      auto [canonical_iter, canonical_not_present] =
          canonical_table.insert(/*value=*/{
              pdpi::TableEntryKey(canonical_table_entry), canonical_table_entry});

      if (not_present != canonical_not_present) {
        return gutil::InternalErrorBuilder()
               << "Standard Table and Canonical Table out of sync. Entry "
               << (not_present ? "not present" : "present")
               << " in Standard Table but "
               << (canonical_not_present ? "not present" : "present")
               << " in Canonical Table.\n"
               << "Offending Entry Update\n"
               << update.DebugString();
      }

      if (!not_present) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Cannot install the same table entry multiple times. Update: "
               << update.DebugString();
      }

      break;
    }

    case Update::DELETE: {
      int entries_erased = tables_[table_id].erase(pdpi::TableEntryKey(table_entry));
      int canonical_entries_erased = canonical_tables_[table_id].erase(
          pdpi::TableEntryKey(canonical_table_entry));

      if (entries_erased != canonical_entries_erased) {
        return gutil::InternalErrorBuilder()
               << "Standard Table and Canonical Table out of sync. Entry "
               << (entries_erased == 0 ? "not present" : "present")
               << " in Standard Table but "
               << (canonical_entries_erased == 0 ? "not present" : "present")
               << " in Canonical Table.\n"
               << "Offending Update\n"
               << update.DebugString();
      }

      if (entries_erased != 1) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Cannot erase non-existent table entries. Update: "
               << update.DebugString();
      }

      break;
    }

    case Update::MODIFY: {
      auto [iter, not_present] = table.insert_or_assign(
          /*k=*/pdpi::TableEntryKey(table_entry), /*obj=*/table_entry);

      auto [canonical_iter, canonical_not_present] =
          canonical_table.insert_or_assign(/*k=*/
                                           pdpi::TableEntryKey(canonical_table_entry),
                                           /*obj=*/canonical_table_entry);

      if (not_present != canonical_not_present) {
        return gutil::InternalErrorBuilder()
               << "Standard Table and Canonical Table out of sync. Entry "
               << (not_present ? "not present" : "present")
               << " in Standard Table but "
               << (canonical_not_present ? "not present" : "present")
               << " in Canonical Table.\n"
               << "Offending Update\n"
               << update.DebugString();
      }

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

absl::Status SwitchState::SetTableEntries(
    absl::Span<const p4::v1::TableEntry> table_entries) {
  ClearTableEntries();

  for (const p4::v1::TableEntry& entry : table_entries) {
    auto table = tables_.find(entry.table_id());
    auto canonical_table = canonical_tables_.find(entry.table_id());
    if (table == tables_.end()) {
      return gutil::InvalidArgumentErrorBuilder()
             << "table entry with unknown table ID '" << entry.table_id()
             << "'";
    }
    if (canonical_table == canonical_tables_.end()) {
      return gutil::InvalidArgumentErrorBuilder()
             << "canonical table entry with unknown table ID '"
             << entry.table_id() << "'";
    }
    ASSIGN_OR_RETURN(TableEntry canonical_entry,
                     CanonicalizeTableEntry(ir_p4info_, entry, false));
    table->second.insert({pdpi::TableEntryKey(entry), entry});
    canonical_table->second.insert(
        {pdpi::TableEntryKey(canonical_entry), canonical_entry});
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

absl::btree_set<std::string> SwitchState::GetIdsForMatchField(
    const pdpi::IrMatchFieldReference& field) const {
  absl::btree_set<std::string> result;
  const auto& table_definition =
      FindOrDie(ir_p4info_.tables_by_name(), field.table());
  const auto& match_definition =
      FindOrDie(table_definition.match_fields_by_name(), field.match_field());
  // Loop over all table entries in this table and collect IDs.
  for (const auto& [key, entry] :
       FindOrDie(tables_, table_definition.preamble().id())) {
    // Find the correct match field.
    for (const auto& match : entry.match()) {
      if (match.field_id() == match_definition.match_field().id()) {
        result.insert(match.exact().value());
        break;
      }
    }
  }
  return result;
}

absl::Status SwitchState::CheckConsistency() const {
  if (tables_.size() != canonical_tables_.size()) {
    return absl::InternalError(
        absl::StrFormat("Size of `tables_` and `canonical_tables_` is "
                        "different. `tables_`: '%d'  `canonical_tables_`: '%d'",
                        tables_.size(), canonical_tables_.size()));
  }

  // Ensure that every `table_id` in `tables_` is also present in
  // `canonical_tables_` and that the corresponding tables are the same size.
  for (const auto& [table_id, table] : tables_) {
    if (!canonical_tables_.contains(table_id)) {
      return absl::InternalError(absl::StrFormat(
          "`canonical_tables_` is missing table with id '%d'", table_id));
    }

    const CanonicalTableEntries& canonical_table =
        canonical_tables_.at(table_id);

    if (canonical_table.size() != table.size()) {
      return absl::InternalError(absl::StrFormat(
          "Number of standard entries differs from number of canonical entries "
          "in table with id %d. Standard Entries: %d  Canonical Entries: %d",
          table_id, table.size(), canonical_tables_.at(table_id).size()));
    }

    // Ensure that every `table_entry` in a standard table has a corresponding
    // `canonical_table_entry` in a canonical table.
    for (const auto& [table_key, table_entry] : table) {
      ASSIGN_OR_RETURN(TableEntry canonical_table_entry,
                       CanonicalizeTableEntry(ir_p4info_, table_entry, false));

      std::optional<TableEntry> fetched_entry =
          GetCanonicalTableEntry(canonical_table_entry);
      if (!fetched_entry.has_value()) {
        return absl::InternalError(absl::StrFormat(
            "Table entry %s is missing corresponding canonical table entry",
            table_entry.DebugString()));
      }

      google::protobuf::util::MessageDifferencer differ;
      differ.TreatAsSet(TableEntry::descriptor()->FindFieldByName("match"));
      if (!gutil::ProtoEqual(canonical_table_entry, *fetched_entry, differ)) {
        return absl::InternalError(absl::StrFormat(
            "Stored canonical entry differs from expected canonical entry\n "
            "Stored Entry: %s Expected Entry: %s",
            fetched_entry->DebugString(), canonical_table_entry.DebugString()));
      }
    }
  }
  return absl::OkStatus();
}

absl::Status SwitchState::AssertEntriesAreEqualToState(
    const std::vector<p4::v1::TableEntry>& switch_entries,
    std::optional<std::function<bool(const IrTableEntry&, const IrTableEntry&)>>
        TreatAsEqualDueToKnownBug) const {
  std::string status_message = "";

  // Condition that requires a search for unique entries in switchstate.
  bool entry_unique_to_switch = false;

  if (switch_entries.size() != GetNumTableEntries()) {
    absl::StrAppendFormat(&status_message,
                          "Number of entries on switch does not match number "
                          "of entries in Fuzzer\n"
                          "Entries on switch: %d\n"
                          "Entries in Fuzzer: %d\n",
                          switch_entries.size(), GetNumTableEntries());
  }

  // Message differencer for PI Table Entries.
  google::protobuf::util::MessageDifferencer differ;
  differ.TreatAsSet(
      p4::v1::TableEntry::GetDescriptor()->FindFieldByName("match"));
  differ.TreatAsSet(p4::v1::Action::GetDescriptor()->FindFieldByName("params"));
  differ.TreatAsSet(
      p4::v1::ActionProfileActionSet::GetDescriptor()->FindFieldByName(
          "action_profile_actions"));

  // Message differencer for IR Table Entries.
  google::protobuf::util::MessageDifferencer ir_differ;
  ir_differ.TreatAsSet(
      IrTableEntry::GetDescriptor()->FindFieldByName("matches"));
  ir_differ.TreatAsSet(
      pdpi::IrActionInvocation::GetDescriptor()->FindFieldByName("params"));
  ir_differ.TreatAsSet(
      pdpi::IrActionSet::GetDescriptor()->FindFieldByName("actions"));

  std::optional<p4::v1::TableEntry> fuzzer_entry;
  for (const auto& switch_entry : switch_entries) {
    fuzzer_entry = GetCanonicalTableEntry(switch_entry);

    // Is there an entry on the switch that does not exist in the Fuzzer?
    if (!fuzzer_entry.has_value()) {
      entry_unique_to_switch = true;
      ASSIGN_OR_RETURN(IrTableEntry ir_entry,
                       pdpi::PiTableEntryToIr(ir_p4info_, switch_entry));
      absl::StrAppend(
          &status_message,
          "The following entry exists on switch but not in Fuzzer:\n",
          PrintTextProto(ir_entry));
      continue;
    }

    std::string differences = "";
    differ.ReportDifferencesToString(&differences);
    std::string ir_differences = "";
    ir_differ.ReportDifferencesToString(&ir_differences);

    // Is there an entry with the same key on both the switch and in the Fuzzer,
    // but they differ in other ways?
    if (!differ.Compare(*fuzzer_entry, switch_entry)) {
      ASSIGN_OR_RETURN(IrTableEntry ir_switch_entry,
                       pdpi::PiTableEntryToIr(ir_p4info_, switch_entry));
      ASSIGN_OR_RETURN(IrTableEntry ir_fuzzer_entry,
                       pdpi::PiTableEntryToIr(ir_p4info_, *fuzzer_entry));

      if (ir_differ.Compare(ir_fuzzer_entry, ir_switch_entry)) {
        return absl::InternalError(absl::StrFormat(
            "PI 'entries' were not equal but IR 'entries' were\n"
            "IR Entry\n"
            "%s"
            "Differences in PI 'entries'\n"
            "%s\n"
            "Switch PI Entry\n"
            "%s"
            "Fuzzer PI Entry\n"
            "%s",
            PrintTextProto(ir_switch_entry), differences,
            PrintTextProto(switch_entry), PrintTextProto(*fuzzer_entry)));

        // If there is a difference, are known bugs being masked and is the
        // difference caused by a known bug?
      } else if (!TreatAsEqualDueToKnownBug.has_value() ||
                 !(*TreatAsEqualDueToKnownBug)(ir_fuzzer_entry,
                                               ir_switch_entry)) {
        absl::StrAppendFormat(
            &status_message,
            "Entry exists in both switch and Fuzzer, but is different:\n"
            "%s\n"
            "Entry on switch:\n"
            "%s"
            "Entry in Fuzzer:\n"
            "%s",
            ir_differences, PrintTextProto(ir_switch_entry),
            PrintTextProto(ir_fuzzer_entry));
      }
    }
  }

  // Are there entries in the Fuzzer that do not exist on the switch?
  if (switch_entries.size() != GetNumTableEntries() || entry_unique_to_switch) {
    absl::flat_hash_map<int, CanonicalTableEntries> fuzzer_state_copy =
        canonical_tables_;

    // Removes all entries from the `fuzzer_state_copy` that exist on the
    // switch.
    for (const auto& switch_entry : switch_entries) {
      if (GetCanonicalTableEntry(switch_entry).has_value()) {
        fuzzer_state_copy.at(switch_entry.table_id())
            .erase(pdpi::TableEntryKey(switch_entry));
      }
    }

    // All remaining entries exist only in the fuzzer.
    for (const auto& [table_id, table] : fuzzer_state_copy) {
      for (const auto& [key, fuzzer_entry] : table) {
        ASSIGN_OR_RETURN(IrTableEntry ir_entry,
                         pdpi::PiTableEntryToIr(ir_p4info_, fuzzer_entry));
        absl::StrAppend(
            &status_message,
            "The following entry exists in Fuzzer but not on switch:\n",
            PrintTextProto(ir_entry));
      }
    }
  }

  if (status_message.empty()) return absl::OkStatus();

  return absl::FailedPreconditionError(status_message);
}

}  // namespace p4_fuzzer
