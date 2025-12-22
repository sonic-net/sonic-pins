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
#include "p4_fuzzer/switch_state.h"

#include <algorithm>
#include <cstdint>
#include <functional>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/btree_map.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "absl/types/span.h"
#include "google/protobuf/util/message_differencer.h"
#include "gutil/collections.h"
#include "gutil/ordered_map.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/built_ins.h"
#include "p4_pdpi/entity_keys.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/translation_options.h"

// Remove death behavior from this file (i.e. remove
// statements that crash like FindOrDie).

namespace p4_fuzzer {
namespace {

using ::gutil::FindOrDie;
using ::gutil::FindPtrOrStatus;
using ::gutil::PrintTextProto;
using ::p4::v1::Entity;
using ::p4::v1::MulticastGroupEntry;
using ::p4::v1::TableEntry;
using ::p4::v1::Update;
using ::pdpi::IrEntity;
using ::pdpi::IrP4Info;
using ::pdpi::IrTableEntry;

// Resource utilization for ActionProfiles depends on how the profile is
// configured. Using SumOfMembers means we only count the number of actions in
// an action profile. Using SumOfWeights means we count the total weight for all
// actions combined.
struct ActionProfileResources {
  int actions = 0;
  int total_weight = 0;
};

ActionProfileResources GetAllActionProfileResourceForTable(
    const UnorderedTableEntries& table) {
  ActionProfileResources resources;
  for (auto& [table_key, table_entry] : table) {
    for (const p4::v1::ActionProfileAction& action :
         table_entry.action()
             .action_profile_action_set()
             .action_profile_actions()) {
      resources.total_weight += action.weight();
    }
    resources.actions += table_entry.action()
                             .action_profile_action_set()
                             .action_profile_actions_size();
  }
  return resources;
}

ActionProfileResources GetAllActionProfileResourceForTableEntry(
    const p4::v1::TableEntry& pi_table_entry) {
  ActionProfileResources resources;
  for (const p4::v1::ActionProfileAction& action :
       pi_table_entry.action()
           .action_profile_action_set()
           .action_profile_actions()) {
    ++resources.actions;
    resources.total_weight += action.weight();
  }
  return resources;
}

absl::StatusOr<std::string> ReasonActionProfileCanAccommodateTableEntry(
    const p4::config::v1::ActionProfile& action_profile,
    const UnorderedTableEntries& current_table,
    const p4::v1::Update& pi_update) {
  if (pi_update.type() == Update::DELETE) {
    return "The update is a DELETE which can always be accommodated.";
  }

  const p4::v1::TableEntry& pi_table_entry = pi_update.entity().table_entry();
  ActionProfileResources current_resources =
      GetAllActionProfileResourceForTable(current_table);
  ActionProfileResources needed_resources =
      GetAllActionProfileResourceForTableEntry(pi_table_entry);
  // MODIFYs are treated as a DELETE + INSERT which means resources are removed
  // before added. INSERTs do not remove resources.
  ActionProfileResources removed_resources;
  if (pi_update.type() == Update::MODIFY) {
    auto it = current_table.find(pdpi::TableEntryKey(pi_table_entry));
    if (it == current_table.end()) {
      return gutil::InvalidArgumentErrorBuilder()
             << " Cannot MODIFY an entry that does not exist. "
             << gutil::PrintTextProto(pi_update);
    }
    removed_resources = GetAllActionProfileResourceForTableEntry(it->second);
  }

  for (const p4::v1::ActionProfileAction& action :
       pi_table_entry.action()
           .action_profile_action_set()
           .action_profile_actions()) {
    // If action weight is 0 or less, or if it is greater than the
    // max_member_weight (if non-zero) for SumOfMembers semantics, the server
    // MUST return an InvalidArgumentError.
    if (action.weight() <= 0) {
      return absl::InvalidArgumentError(absl::StrFormat(
          "The new entry attempts to program a member with weight %d, which is "
          "never allowed.",
          action.weight()));
    } else if (action_profile.sum_of_members().max_member_weight() != 0 &&
               action.weight() >
                   action_profile.sum_of_members().max_member_weight()) {
      return absl::InvalidArgumentError(absl::StrFormat(
          "The action profile max_member_weight is %d and the new entry "
          "programs a member of weight %d.",
          action_profile.sum_of_members().max_member_weight(),
          action.weight()));
    }
  }

  if (action_profile.has_sum_of_members()) {
    // If the table entry has too many actions then the current table resources
    // do not matter. The server must return an InvalidArgumentError.
    if (needed_resources.actions > action_profile.max_group_size() &&
        action_profile.max_group_size() != 0) {
      return absl::InvalidArgumentError(absl::StrFormat(
          "The action profile max group size is %d and the new entry needs %d.",
          action_profile.max_group_size(), needed_resources.actions));
    }
    std::string result = absl::StrFormat(
        "The action profile uses SumOfMembers and currently has %d members "
        "with space for %d, and the new entry needs %d.",
        current_resources.actions, action_profile.size(),
        needed_resources.actions);
    if (pi_update.type() == Update::MODIFY) {
      absl::StrAppend(
          &result,
          " The update is a MODIFY and will replace an entry that had ",
          removed_resources.actions, " members.");
    }
    if (current_resources.actions + needed_resources.actions -
            removed_resources.actions <=
        action_profile.size()) {
      return result;
    }
    return absl::ResourceExhaustedError(result);
  } else {
    // If the table entry has too much weight then the current table resources
    // do not matter. The server must return an InvalidArgumentError.
    if (needed_resources.total_weight > action_profile.max_group_size() &&
        action_profile.max_group_size() != 0) {
      return absl::InvalidArgumentError(absl::StrFormat(
          "The action profile max group size is %d and the new entry needs %d.",
          action_profile.max_group_size(), needed_resources.total_weight));
    }
    // If the action profile does not use SumOfMembers semantics, then it must
    // use SumOfWeights since that is both the default and the only other
    // option.
    std::string result = absl::StrFormat(
        "The action profile uses SumOfWeights and has a current total weight "
        "of %d with space for %d, and the new entry needs %d.",
        current_resources.total_weight, action_profile.size(),
        needed_resources.total_weight);
    if (pi_update.type() == Update::MODIFY) {
      absl::StrAppend(&result,
                      " The update is a MODIFY and will replace an entry that "
                      "had weight ",
                      removed_resources.total_weight, ".");
    }
    if (current_resources.total_weight + needed_resources.total_weight -
            removed_resources.total_weight <=
        action_profile.size()) {
      return result;
    }
    return absl::ResourceExhaustedError(result);
  }
}

}  // namespace

// Returns the canonical form of `entity` according to the P4 Runtime Spec
// https://s3-us-west-2.amazonaws.com/p4runtime/ci/main/P4Runtime-Spec.html#sec-bytestrings.
// TODO: Canonical form is achieved by performing an IR roundtrip
// translation. This ties correctness to IR functionality. Local
// canonicalization would be preferred.
absl::StatusOr<Entity> CanonicalizeEntity(const IrP4Info& info,
                                          const Entity& entity, bool key_only) {
  auto pdpi_options = pdpi::TranslationOptions{
      .key_only = key_only,
  };
  // IR->PI translation includes canonicalization so a PI->IR->PI translation is
  // performed for canonicalization.
  ASSIGN_OR_RETURN(IrEntity ir_entity,
                   pdpi::PiEntityToIr(info, entity, pdpi_options),
                   _ << "Could not canonicalize: PiToIr Error\n"
                     << entity.DebugString());
  ASSIGN_OR_RETURN(Entity canonical_entity,
                   pdpi::IrEntityToPi(info, ir_entity, pdpi_options),
                   _ << "Could not canonicalize: IrToPi Error\n"
                     << entity.DebugString());
  return canonical_entity;
}

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
    ordered_tables_[table_id] = OrderedTableEntries();
    unordered_tables_[table_id] = UnorderedTableEntries();
    current_resource_statistics_[table_id] = ResourceStatistics();
    peak_resource_statistics_[table_id] = PeakResourceStatistics();
  }
  current_entries_ = 0;
  peak_entries_seen_ = 0;
  current_multicast_resource_statistics_ = ResourceStatistics();
  peak_multicast_resource_statistics_ = PeakResourceStatistics();
}

void SwitchState::ClearTableEntries() {
  for (auto& [table_id, table] : ir_p4info_.tables_by_id()) {
    ordered_tables_[table_id] = OrderedTableEntries();
    unordered_tables_[table_id] = UnorderedTableEntries();
    current_resource_statistics_[table_id] = ResourceStatistics();
  }
  ordered_multicast_entries_ = {};
  unordered_multicast_entries_ = {};
  current_entries_ = 0;
  current_multicast_resource_statistics_ = ResourceStatistics();
}

bool SwitchState::AllP4TablesEmpty() const {
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
  return FindOrDie(current_resource_statistics_, table_id).entries;
}

int64_t SwitchState::GetNumTableEntries() const { return current_entries_; }

// For this method to pass we only need 1 of the following checks to fail:
//   * table is full.
//   * action profile resources are exhausted. (only applies to action sets)
absl::Status SwitchState::ResourceExhaustedIsAllowed(
    const p4::v1::Update& pi_update) const {
  // DELETEs should never trigger resource exhaustion.
  if (pi_update.type() == Update::DELETE) {
    return gutil::FailedPreconditionErrorBuilder()
           << "DELETEs should never trigger resource exhaustion."
           << gutil::PrintTextProto(pi_update);
  }
  std::vector<std::string> results;
  results.reserve(2);

  if (pi_update.entity().has_table_entry()) {
    const TableEntry& pi_table_entry = pi_update.entity().table_entry();
    uint32_t table_id = pi_table_entry.table_id();
    ASSIGN_OR_RETURN(const pdpi::IrTableDefinition* table_def,
                     FindPtrOrStatus(ir_p4info_.tables_by_id(), table_id));
    ASSIGN_OR_RETURN(const UnorderedTableEntries* table,
                     FindPtrOrStatus(unordered_tables_, table_id));

    // If adding this entry would push the table size beyond what is defined
    // then ResourceExhausted is allowed.
    if (pi_update.type() == Update::INSERT &&
        table->size() + 1 > table_def->size()) {
      return absl::OkStatus();
    }

    std::string table_size_result =
        absl::StrFormat("The table is holding %d entries and has space for %d.",
                        table->size(), table_def->size());
    if (pi_update.type() == Update::MODIFY) {
      absl::StrAppend(
          &table_size_result,
          " The update is a MODIFY and replaces an existing entry.");
    }
    results.push_back(table_size_result);

    // If the table uses an action profile then we also need to verify that the
    // profile itself has enough space.
    if (table_def->implementation_id_case() ==
        pdpi::IrTableDefinition::kActionProfileId) {
      ASSIGN_OR_RETURN(
          const pdpi::IrActionProfileDefinition* action_profile_def,
          FindPtrOrStatus(ir_p4info_.action_profiles_by_id(),
                          table_def->action_profile_id()));
      const p4::config::v1::ActionProfile& action_profile =
          action_profile_def->action_profile();

      // Check if we have exhausted our action profile resources.
      absl::StatusOr<std::string> action_profile_has_space =
          ReasonActionProfileCanAccommodateTableEntry(action_profile, *table,
                                                      pi_update);

      if (!action_profile_has_space.ok()) {
        // If we've exhausted our action profile resources then
        // ResourceExhausted is allowed, but if we have a different error then
        // something else is wrong and needs to be reported.
        return (action_profile_has_space.status().code() ==
                absl::StatusCode::kResourceExhausted)
                   ? absl::OkStatus()
                   : action_profile_has_space.status();
      }
      results.push_back(*action_profile_has_space);
    }

    return absl::FailedPreconditionError(absl::StrFormat(
        "Table '%s' must accept the entry because: %s",
        table_def->preamble().alias(), absl::StrJoin(results, " ")));
  }

  if (pi_update.entity()
          .packet_replication_engine_entry()
          .has_multicast_group_entry()) {
    const MulticastGroupEntry& multicast_group_entry =
        pi_update.entity()
            .packet_replication_engine_entry()
            .multicast_group_entry();

    int removed_multicast_replicas = 0;
    int removed_multicast_entries = 0;
    if (pi_update.type() == Update::MODIFY) {
      std::optional<p4::v1::MulticastGroupEntry>
          existing_multicast_group_entry =
              GetMulticastGroupEntry(multicast_group_entry);
      if (!existing_multicast_group_entry.has_value()) {
        return gutil::InvalidArgumentErrorBuilder()
               << " Cannot MODIFY a multicast group entry that does not exist. "
               << gutil::PrintTextProto(pi_update);
      }
      removed_multicast_replicas =
          existing_multicast_group_entry->replicas_size();
      removed_multicast_entries = 1;
    }

    // Get the resource limits for multicast group entries from the P4info.
    const p4::config::v1::PlatformProperties& platform_properties =
        ir_p4info_.pkg_info().platform_properties();

    std::string result;
    if (current_multicast_resource_statistics_.total_members +
            multicast_group_entry.replicas_size() -
            removed_multicast_replicas <=
        platform_properties.multicast_group_table_total_replicas()) {
      result = absl::StrFormat(
          "The multicast group table has %d total replicas with a maximum "
          "limit of %d, the new entry needs %d, and %d replicas were removed.",
          current_multicast_resource_statistics_.total_members,
          platform_properties.multicast_group_table_total_replicas(),
          multicast_group_entry.replicas_size(), removed_multicast_replicas);
    } else {
      return absl::OkStatus();
    }

    if (current_multicast_resource_statistics_.entries + 1 -
            removed_multicast_entries <=
        platform_properties.multicast_group_table_size()) {
      result = absl::StrFormat(
          "The current multicast_group_table size is %d, and the max size "
          "allowed is %d.",
          current_multicast_resource_statistics_.entries,
          platform_properties.multicast_group_table_size());
    } else {
      return absl::OkStatus();
    }

    if (multicast_group_entry.replicas_size() <=
        platform_properties.multicast_group_table_max_replicas_per_entry()) {
      result = absl::StrFormat(
          "The current multicast_group_table_entry has %d replicas and the max "
          "allowed number of replicas per entry is %d.",
          multicast_group_entry.replicas_size(),
          platform_properties.multicast_group_table_max_replicas_per_entry());
    } else {
      return absl::OkStatus();
    }

    return absl::InvalidArgumentError(result);
  }

  return gutil::UnimplementedErrorBuilder()
         << "ResourceExhaustedIsAllowed does not support "
         << pi_update.entity().GetTypeName();
}

std::vector<uint32_t> SwitchState::AllTableIds() const {
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
  return FindOrDie(ordered_tables_, table_id).empty();
}

std::optional<Entity> SwitchState::GetEntity(const Entity& entity) const {
  std::optional<Entity> result = std::nullopt;
  if (entity.packet_replication_engine_entry().has_multicast_group_entry()) {
    std::optional<MulticastGroupEntry> multicast_group_entry =
        GetMulticastGroupEntry(
            entity.packet_replication_engine_entry().multicast_group_entry());
    if (multicast_group_entry.has_value()) {
      result = Entity();
      *result->mutable_packet_replication_engine_entry()
           ->mutable_multicast_group_entry() =
          *std::move(multicast_group_entry);
    }
  }

  if (entity.has_table_entry()) {
    std::optional<TableEntry> table_entry = GetTableEntry(entity.table_entry());
    if (table_entry.has_value()) {
      result = Entity();
      *result->mutable_table_entry() = *std::move(table_entry);
    }
  }

  return result;
}

std::optional<TableEntry> SwitchState::GetTableEntry(
    const TableEntry& entry) const {
  const UnorderedTableEntries& table =
      FindOrDie(unordered_tables_, entry.table_id());

  if (auto table_iter = table.find(pdpi::TableEntryKey(entry));
      table_iter != table.end()) {
    auto [table_key, table_entry] = *table_iter;
    return table_entry;
  }

  // If no entry found, canonicalize the entry and try again.
  absl::StatusOr<TableEntry> canonical_entry =
      CanonicalizeTableEntry(ir_p4info_, entry, /*key_only=*/true);
  if (!canonical_entry.ok()) return std::nullopt;

  if (auto table_iter = table.find(pdpi::TableEntryKey(*canonical_entry));
      table_iter != table.end()) {
    auto [table_key, table_entry] = *table_iter;
    return table_entry;
  }

  return std::nullopt;
}

std::optional<p4::v1::MulticastGroupEntry> SwitchState::GetMulticastGroupEntry(
    const MulticastGroupEntry& entry) const {
  if (auto table_iter =
          unordered_multicast_entries_.find(entry.multicast_group_id());
      table_iter != unordered_multicast_entries_.end()) {
    auto [table_key, table_entry] = *table_iter;
    return table_entry;
  }
  return std::nullopt;
}

absl::StatusOr<PeakResourceStatistics> SwitchState::GetPeakResourceStatistics(
    int table_id) const {
  if (!peak_resource_statistics_.contains(table_id)) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Table with id `" << table_id << "` does not exist.";
  }
  return peak_resource_statistics_.at(table_id);
}

absl::Status SwitchState::UpdateResourceStatistics(const TableEntry& entry,
                                                   p4::v1::Update::Type type) {
  int table_id = entry.table_id();
  const pdpi::IrTableDefinition& table_definition =
      FindOrDie(ir_p4info_.tables_by_id(), table_id);

  ResourceStatistics& current_resource_statistics =
      FindOrDie(current_resource_statistics_, table_id);
  PeakResourceStatistics& peak_resource_statistics =
      FindOrDie(peak_resource_statistics_, table_id);

  std::optional<ActionProfileResources> group_resources = std::nullopt;
  if (table_definition.uses_oneshot()) {
    group_resources = GetAllActionProfileResourceForTableEntry(entry);
  }

  switch (type) {
    case Update::INSERT: {
      current_entries_ += 1;
      current_resource_statistics.entries += 1;
      if (group_resources.has_value()) {
        current_resource_statistics.total_weight +=
            group_resources->total_weight;
        current_resource_statistics.total_members += group_resources->actions;
      }
      break;
    }
    case Update::DELETE: {
      // If entry uses action profiles, retrieve profile statistics from stored
      // entry.
      if (table_definition.uses_oneshot()) {
        auto& unordered_table = FindOrDie(unordered_tables_, table_id);
        auto it = unordered_table.find(pdpi::TableEntryKey(entry));
        if (it == unordered_table.end()) {
          return gutil::InvalidArgumentErrorBuilder()
                 << " Cannot update resource statistics for DELETE of "
                    "non-existent table entry. "
                 << entry.DebugString();
        }
        group_resources = GetAllActionProfileResourceForTableEntry(it->second);
      }

      current_entries_ -= 1;
      current_resource_statistics.entries -= 1;
      if (group_resources.has_value()) {
        current_resource_statistics.total_weight -=
            group_resources->total_weight;
        current_resource_statistics.total_members -= group_resources->actions;
      }
      break;
    }
    case Update::MODIFY: {
      auto& unordered_table = FindOrDie(unordered_tables_, table_id);
      auto it = unordered_table.find(pdpi::TableEntryKey(entry));
      if (it == unordered_table.end()) {
        return gutil::InvalidArgumentErrorBuilder()
               << " Cannot update resource statistics for MODIFY of "
                  "non-existent table entry. "
               << entry.DebugString();
      }
      RETURN_IF_ERROR(UpdateResourceStatistics(it->second, Update::DELETE));
      return UpdateResourceStatistics(entry, Update::INSERT);
    }
    default: {
      return gutil::InternalErrorBuilder()
             << "Update type must be specified when updating resource "
                "statistics."
             << Update_Type_Name(type);
    }
  }

  peak_entries_seen_ = std::max(peak_entries_seen_, current_entries_);
  peak_resource_statistics.entries = std::max(
      peak_resource_statistics.entries, current_resource_statistics.entries);
  if (group_resources.has_value()) {
    // Update weight semantics resources.
    peak_resource_statistics.total_weight =
        std::max(peak_resource_statistics.total_weight,
                 current_resource_statistics.total_weight);
    peak_resource_statistics.max_group_weight =
        std::max(peak_resource_statistics.max_group_weight,
                 group_resources->total_weight);

    // Update member semantics resources.
    peak_resource_statistics.total_members =
        std::max(peak_resource_statistics.total_members,
                 current_resource_statistics.total_members);
    peak_resource_statistics.max_members_per_group =
        std::max(peak_resource_statistics.max_members_per_group,
                 group_resources->actions);
  }
  return absl::OkStatus();
}

absl::Status SwitchState::UpdateMulticastResourceStatistics(
    const MulticastGroupEntry& entry, p4::v1::Update::Type type) {
  switch (type) {
    case Update::INSERT: {
      current_entries_ += 1;
      current_multicast_resource_statistics_.entries += 1;
      current_multicast_resource_statistics_.total_members +=
          entry.replicas().size();
      break;
    }
    case Update::DELETE: {
      auto it = unordered_multicast_entries_.find(entry.multicast_group_id());
      if (it == unordered_multicast_entries_.end()) {
        return gutil::InvalidArgumentErrorBuilder()
               << " Cannot update resource statistics for DELETE of "
                  "non-existent multicast group table entry. "
               << entry.DebugString();
      }
      current_entries_ -= 1;
      current_multicast_resource_statistics_.entries -= 1;
      current_multicast_resource_statistics_.total_members -=
          it->second.replicas().size();
      break;
    }
    case Update::MODIFY: {
      // Retrieve replica count from stored entry.
      auto it = unordered_multicast_entries_.find(entry.multicast_group_id());
      if (it == unordered_multicast_entries_.end()) {
        return gutil::InvalidArgumentErrorBuilder()
               << " Cannot update resource statistics for MODIFY of "
                  "non-existent multicast group table entry. "
               << entry.DebugString();
      }
      RETURN_IF_ERROR(
          UpdateMulticastResourceStatistics(it->second, Update::DELETE));
      return UpdateMulticastResourceStatistics(entry, Update::INSERT);
    }
    default: {
      return gutil::InternalErrorBuilder()
             << "Update type must be specified when updating resource "
                "statistics."
             << Update_Type_Name(type);
    }
  }

  peak_entries_seen_ = std::max(peak_entries_seen_, current_entries_);
  peak_multicast_resource_statistics_.entries =
      std::max(peak_multicast_resource_statistics_.entries,
               current_multicast_resource_statistics_.entries);

  // Update member semantics resources.
  peak_multicast_resource_statistics_.total_members =
      std::max(peak_multicast_resource_statistics_.total_members,
               current_multicast_resource_statistics_.total_members);
  peak_multicast_resource_statistics_.max_members_per_group =
      std::max(peak_multicast_resource_statistics_.max_members_per_group,
               entry.replicas().size());

  return absl::OkStatus();
}

absl::Status SwitchState::ApplyMulticastUpdate(const Update& update) {
  ASSIGN_OR_RETURN(
      Entity canonical_entity,
      CanonicalizeEntity(ir_p4info_, update.entity(),
                         /*key_only=*/update.type() == Update::DELETE));
  const p4::v1::MulticastGroupEntry& multicast_group_entry =
      canonical_entity.packet_replication_engine_entry()
          .multicast_group_entry();
  int multicast_group_id = multicast_group_entry.multicast_group_id();

  RETURN_IF_ERROR(
      UpdateMulticastResourceStatistics(multicast_group_entry, update.type()));
  switch (update.type()) {
    case Update::INSERT: {
      auto [ordered_iter, ordered_not_present] =
          ordered_multicast_entries_.insert(
              /*value=*/{multicast_group_id, multicast_group_entry});

      auto [unordered_iter, unordered_not_present] =
          unordered_multicast_entries_.insert(
              /*value=*/{multicast_group_id, multicast_group_entry});

      if (ordered_not_present != unordered_not_present) {
        return gutil::InternalErrorBuilder()
               << "Ordered Table and Unordered Table out of sync. Entry "
               << (ordered_not_present ? "not present" : "present")
               << " in Ordered Table but "
               << (unordered_not_present ? "not present" : "present")
               << " in Unordered Table.\n"
               << "Offending Entry Update\n"
               << update.DebugString();
      }

      if (!ordered_not_present) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Cannot install the same table entry multiple times. Update: "
               << update.DebugString();
      }

      break;
    }
    case Update::DELETE: {
      int ordered_entries_erased =
          ordered_multicast_entries_.erase(multicast_group_id);
      int unordered_entries_erased =
          unordered_multicast_entries_.erase(multicast_group_id);

      if (ordered_entries_erased != unordered_entries_erased) {
        return gutil::InternalErrorBuilder()
               << "Ordered Table and Unordered Table out of sync. Entry "
               << (ordered_entries_erased == 0 ? "not present" : "present")
               << " in Ordered Table but "
               << (unordered_entries_erased == 0 ? "not present" : "present")
               << " in Unordered Table.\n"
               << "Offending Update\n"
               << update.DebugString();
      }

      if (ordered_entries_erased != 1) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Cannot erase non-existent table entries. Update: "
               << update.DebugString();
      }

      break;
    }

    case Update::MODIFY: {
      auto [ordered_iter, ordered_not_present] =
          ordered_multicast_entries_.insert_or_assign(
              /*k=*/multicast_group_id,
              /*obj=*/multicast_group_entry);

      auto [unordered_iter, unordered_not_present] =
          unordered_multicast_entries_
              .insert_or_assign(/*k=*/
                                multicast_group_id,
                                /*obj=*/multicast_group_entry);

      if (ordered_not_present != unordered_not_present) {
        return gutil::InternalErrorBuilder()
               << "Ordered Table and Unordered Table out of sync. Entry "
               << (ordered_not_present ? "not present" : "present")
               << " in Ordered Table but "
               << (unordered_not_present ? "not present" : "present")
               << " in Unordered Table.\n"
               << "Offending Update\n"
               << update.DebugString();
      }

      if (ordered_not_present) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Cannot modify a non-existing update. Update: "
               << update.DebugString();
      }

      break;
    }

    default:
      LOG(FATAL) << "Update of unsupported type: "  // Crash OK
                 << update.DebugString();
  }
  return absl::OkStatus();
}

absl::Status SwitchState::ApplyUpdate(const Update& update) {
  if (update.entity()
          .packet_replication_engine_entry()
          .has_multicast_group_entry()) {
    return ApplyMulticastUpdate(update);
  }

  const int table_id = update.entity().table_entry().table_id();

  auto& ordered_table = FindOrDie(ordered_tables_, table_id);
  auto& unordered_table = FindOrDie(unordered_tables_, table_id);

  const TableEntry& table_entry = update.entity().table_entry();
  // TODO: PDPI IR Update translation currently does not properly
  // ignore non-key fields on DELETE updates. Therefore, information to ignore
  // non-key fields is explicitly passed for canonicalization.
  ASSIGN_OR_RETURN(
      const TableEntry& canonical_table_entry,
      CanonicalizeTableEntry(ir_p4info_, table_entry,
                             /*key_only=*/update.type() == Update::DELETE));

  RETURN_IF_ERROR(
      UpdateResourceStatistics(canonical_table_entry, update.type()));
  switch (update.type()) {
    case Update::INSERT: {
      auto [ordered_iter, ordered_not_present] = ordered_table.insert(
          /*value=*/{pdpi::TableEntryKey(canonical_table_entry),
                     canonical_table_entry});

      auto [unordered_iter,
            unordered_not_present] = unordered_table.insert(/*value=*/{
          pdpi::TableEntryKey(canonical_table_entry), canonical_table_entry});

      if (ordered_not_present != unordered_not_present) {
        return gutil::InternalErrorBuilder()
               << "Ordered Table and Unordered Table out of sync. Entry "
               << (ordered_not_present ? "not present" : "present")
               << " in Ordered Table but "
               << (unordered_not_present ? "not present" : "present")
               << " in Unordered Table.\n"
               << "Offending Entry Update\n"
               << update.DebugString();
      }

      if (!ordered_not_present) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Cannot install the same table entry multiple times. Update: "
               << update.DebugString();
      }

      break;
    }

    case Update::DELETE: {
      int ordered_entries_erased = ordered_tables_[table_id].erase(
          pdpi::TableEntryKey(canonical_table_entry));
      int unordered_entries_erased = unordered_tables_[table_id].erase(
          pdpi::TableEntryKey(canonical_table_entry));

      if (ordered_entries_erased != unordered_entries_erased) {
        return gutil::InternalErrorBuilder()
               << "Ordered Table and Unordered Table out of sync. Entry "
               << (ordered_entries_erased == 0 ? "not present" : "present")
               << " in Ordered Table but "
               << (unordered_entries_erased == 0 ? "not present" : "present")
               << " in Unordered Table.\n"
               << "Offending Update\n"
               << update.DebugString();
      }

      if (ordered_entries_erased != 1) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Cannot erase non-existent table entries. Update: "
               << update.DebugString();
      }

      break;
    }

    case Update::MODIFY: {
      auto [ordered_iter, ordered_not_present] = ordered_table.insert_or_assign(
          /*k=*/pdpi::TableEntryKey(canonical_table_entry),
          /*obj=*/canonical_table_entry);

      auto [unordered_iter, unordered_not_present] =
          unordered_table.insert_or_assign(/*k=*/
                                           pdpi::TableEntryKey(
                                               canonical_table_entry),
                                           /*obj=*/canonical_table_entry);

      if (ordered_not_present != unordered_not_present) {
        return gutil::InternalErrorBuilder()
               << "Ordered Table and Unordered Table out of sync. Entry "
               << (ordered_not_present ? "not present" : "present")
               << " in Ordered Table but "
               << (unordered_not_present ? "not present" : "present")
               << " in Unordered Table.\n"
               << "Offending Update\n"
               << update.DebugString();
      }

      if (ordered_not_present) {
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

absl::Status SwitchState::SetEntities(
    absl::Span<const p4::v1::Entity> entities) {
  ClearTableEntries();

  p4::v1::Update update;
  update.set_type(p4::v1::Update::INSERT);
  for (const Entity& entity : entities) {
    *update.mutable_entity() = entity;
    RETURN_IF_ERROR(ApplyUpdate(update));
  }

  return absl::OkStatus();
}

std::string SwitchState::SwitchStateSummary() const {
  if (ordered_tables_.empty()) return std::string("EmptyState()");
  std::string res = "";
  // Ordered is used to get a deterministic order for the summary.
  for (const auto& [table_id, table] : gutil::AsOrderedView(ordered_tables_)) {
    const pdpi::IrTableDefinition& table_definition =
        FindOrDie(ir_p4info_.tables_by_id(), table_id);
    const std::string& table_name = table_definition.preamble().alias();
    const ResourceStatistics& resource_statistics =
        FindOrDie(current_resource_statistics_, table_id);
    const PeakResourceStatistics& peak_resource_statistics =
        FindOrDie(peak_resource_statistics_, table_id);

    int guaranteed_size = table_definition.size();

    absl::StrAppendFormat(
        &res, "\n % 12d% 16d% 18d    %s", resource_statistics.entries,
        peak_resource_statistics.entries, guaranteed_size, table_name);

    // Mark tables where we have exceeded their resource limits.
    if (peak_resource_statistics.entries >= guaranteed_size) {
      absl::StrAppend(&res, "*");
    }

    // If the table is a WCMP table, then we also print its total weight,
    // max weight per group, total members, and max members per group. Only WCMP
    // tables using one-shot programming are supported.
    if (table_definition.implementation_id_case() ==
        pdpi::IrTableDefinition::kActionProfileId) {
      const p4::config::v1::ActionProfile& action_profile =
          FindOrDie(ir_p4info_.action_profiles_by_id(),
                    table_definition.action_profile_id())
              .action_profile();

      bool uses_weight_semantics = !action_profile.has_sum_of_members();
      absl::StrAppendFormat(&res, "\n % 12d% 16d% 18d    %s.total_weight",
                            resource_statistics.total_weight,
                            peak_resource_statistics.total_weight,
                            uses_weight_semantics ? action_profile.size() : 0,
                            table_name);
      // Mark if we have exceeded the total weight and use weight semantics.
      if (uses_weight_semantics &&
          peak_resource_statistics.total_weight >= action_profile.size()) {
        absl::StrAppend(&res, "*");
      }
      absl::StrAppendFormat(
          &res, "\n % 12s% 16d% 18d    %s.max_group_weight", "N/A",
          peak_resource_statistics.max_group_weight,
          uses_weight_semantics ? action_profile.max_group_size() : 0,
          table_name);
      // Mark if we have exceeded the max weight for a group and use weight
      // semantics.
      if (uses_weight_semantics && peak_resource_statistics.max_group_weight >=
                                       action_profile.max_group_size()) {
        absl::StrAppend(&res, "*");
      }

      bool uses_member_semantics = action_profile.has_sum_of_members();
      absl::StrAppendFormat(&res, "\n % 12d% 16d% 18d    %s.total_members",
                            resource_statistics.total_members,
                            peak_resource_statistics.total_members,
                            uses_member_semantics ? action_profile.size() : 0,
                            table_name);
      // Mark if we have exceeded the total members and use member semantics.
      if (uses_member_semantics &&
          peak_resource_statistics.total_members >= action_profile.size()) {
        absl::StrAppend(&res, "*");
      }
      absl::StrAppendFormat(
          &res, "\n % 12s% 16d% 18d    %s.max_members_per_group", "N/A",
          peak_resource_statistics.max_members_per_group,
          uses_member_semantics ? action_profile.max_group_size() : 0,
          table_name);
      // Mark if we have exceeded the max members for a group and use member
      // semantics.
      if (uses_member_semantics &&
          peak_resource_statistics.max_members_per_group >=
              action_profile.max_group_size()) {
        absl::StrAppend(&res, "*");
      }
    }
  }

  // Multicast Group Table Summary.
  absl::StrAppendFormat(
      &res, "\n % 12d% 16d% 18d    %s",
      current_multicast_resource_statistics_.entries,
      peak_multicast_resource_statistics_.entries,
      ir_p4info_.pkg_info().platform_properties().multicast_group_table_size(),
      pdpi::GetMulticastGroupTableName());
  // Mark statistic if we have exceeded resource limits.
  if (peak_multicast_resource_statistics_.entries >=
      ir_p4info_.pkg_info()
          .platform_properties()
          .multicast_group_table_size()) {
    absl::StrAppend(&res, "*");
  }
  absl::StrAppendFormat(&res, "\n % 12d% 16d% 18d    %s.total_replicas",
                        current_multicast_resource_statistics_.total_members,
                        peak_multicast_resource_statistics_.total_members,
                        ir_p4info_.pkg_info()
                            .platform_properties()
                            .multicast_group_table_total_replicas(),
                        pdpi::GetMulticastGroupTableName());
  // Mark statistic if we have exceeded resource limits.
  if (peak_multicast_resource_statistics_.total_members >=
      ir_p4info_.pkg_info()
          .platform_properties()
          .multicast_group_table_total_replicas()) {
    absl::StrAppend(&res, "*");
  }
  absl::StrAppendFormat(
      &res, "\n % 12s% 16d% 18d    %s.max_replicas_per_group", "N/A",
      peak_multicast_resource_statistics_.max_members_per_group,
      ir_p4info_.pkg_info()
          .platform_properties()
          .multicast_group_table_max_replicas_per_entry(),
      pdpi::GetMulticastGroupTableName());
  // Mark statistic if we have exceeded resource limits.
  if (peak_multicast_resource_statistics_.max_members_per_group >=
      ir_p4info_.pkg_info()
          .platform_properties()
          .multicast_group_table_max_replicas_per_entry()) {
    absl::StrAppend(&res, "*");
  }

  return absl::StrFormat(
      "State(\n % 12s% 16s% 18s    table_name\n % 12d% 16d% 18s    total "
      "number of table entries%s\n * marks tables where max size >= "
      "guaranteed size.\n)",
      "current size", "max size seen", "guaranteed size", GetNumTableEntries(),
      peak_entries_seen_, "N/A", res);
}

absl::Status SwitchState::CheckConsistency() const {
  if (ordered_tables_.size() != unordered_tables_.size()) {
    return absl::InternalError(absl::StrFormat(
        "Size of `ordered_tables_` and `unordered_tables_` is "
        "different. `ordered_tables_`: '%d'  `unordered_tables_`: '%d'",
        ordered_tables_.size(), unordered_tables_.size()));
  }

  // Ensure that every `table_id` in `ordered_tables_` is also present in
  // `unordered_tables_` and that the corresponding tables are the same size.
  for (const auto& [table_id, ordered_table] : ordered_tables_) {
    if (!unordered_tables_.contains(table_id)) {
      return absl::InternalError(absl::StrFormat(
          "`unordered_tables_` is missing table with id '%d'", table_id));
    }

    const UnorderedTableEntries& unordered_table =
        unordered_tables_.at(table_id);

    if (unordered_table.size() != ordered_table.size()) {
      return absl::InternalError(absl::StrFormat(
          "Number of ordered entries differs from number of unordered entries "
          "in table with id %d. Ordered Entries: %d  Unordered Entries: %d",
          table_id, ordered_table.size(),
          unordered_tables_.at(table_id).size()));
    }

    // Ensure that every `table_entry` in an ordered table has a corresponding
    // `table_entry` in the unordered table.
    for (const auto& [table_key, ordered_table_entry] : ordered_table) {
      std::optional<TableEntry> unordered_table_entry =
          GetTableEntry(ordered_table_entry);
      if (!unordered_table_entry.has_value()) {
        return absl::InternalError(
            absl::StrFormat("Ordered table entry %s is missing corresponding "
                            "unordered table entry",
                            ordered_table_entry.DebugString()));
      }

      google::protobuf::util::MessageDifferencer differ;
      differ.TreatAsSet(TableEntry::descriptor()->FindFieldByName("match"));
      if (!gutil::ProtoEqual(ordered_table_entry, *unordered_table_entry,
                             differ)) {
        return absl::InternalError(
            absl::StrFormat("Ordered entry differs from unordered entry\n "
                            "Ordered entry: %s Unordered Entry: %s",
                            ordered_table_entry.DebugString(),
                            unordered_table_entry->DebugString()));
      }
    }
  }

  if (unordered_multicast_entries_.size() !=
      ordered_multicast_entries_.size()) {
    return absl::InternalError(absl::StrFormat(
        "Number of ordered multicast group entries differs from number of "
        "unordered multicast group entries. Ordered Entries: %d  Unordered "
        "Entries: %d",
        ordered_multicast_entries_.size(),
        unordered_multicast_entries_.size()));
  }

  // Ensure that every `table_entry` in an ordered table has a corresponding
  // `table_entry` in the unordered table.
  for (const auto& [multicast_group_id, ordered_entry] :
       ordered_multicast_entries_) {
    std::optional<p4::v1::MulticastGroupEntry> unordered_entry =
        GetMulticastGroupEntry(ordered_entry);
    if (unordered_entry == std::nullopt) {
      return absl::InternalError(absl::StrFormat(
          "Ordered multicast group entry %s is missing corresponding "
          "unordered multicast group entry",
          ordered_entry.DebugString()));
    }

    google::protobuf::util::MessageDifferencer differ;
    if (!gutil::ProtoEqual(ordered_entry, *unordered_entry, differ)) {
      return absl::InternalError(absl::StrFormat(
          "Ordered entry differs from unordered entry\n "
          "Ordered entry: %s Unordered Entry: %s",
          ordered_entry.DebugString(), unordered_entry->DebugString()));
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

  // use entities throughout API.
  if (switch_entries.size() !=
      GetNumTableEntries() - current_multicast_resource_statistics_.entries) {
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

  for (const auto& switch_entry : switch_entries) {
    ASSIGN_OR_RETURN(
        TableEntry canonical_switch_entry,
        CanonicalizeTableEntry(ir_p4info_, switch_entry, /*key_only=*/false));

    std::optional<p4::v1::TableEntry> fuzzer_entry =
        GetTableEntry(canonical_switch_entry);

    // Is there an entry on the switch that does not exist in the Fuzzer?
    if (!fuzzer_entry.has_value()) {
      entry_unique_to_switch = true;
      ASSIGN_OR_RETURN(
          IrTableEntry ir_entry,
          pdpi::PiTableEntryToIr(ir_p4info_, canonical_switch_entry));
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
    if (!differ.Compare(*fuzzer_entry, canonical_switch_entry)) {
      ASSIGN_OR_RETURN(
          IrTableEntry ir_switch_entry,
          pdpi::PiTableEntryToIr(ir_p4info_, canonical_switch_entry));
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
            PrintTextProto(canonical_switch_entry),
            PrintTextProto(*fuzzer_entry)));

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
    absl::flat_hash_map<int, UnorderedTableEntries> fuzzer_state_copy =
        unordered_tables_;

    // Removes all entries from the `fuzzer_state_copy` that exist on the
    // switch.
    for (const auto& switch_entry : switch_entries) {
      if (GetTableEntry(switch_entry).has_value()) {
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
