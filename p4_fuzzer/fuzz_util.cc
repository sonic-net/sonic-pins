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
#include "p4_fuzzer/fuzz_util.h"

#include <algorithm>
#include <cstdint>
#include <functional>
#include <iterator>
#include <limits>
#include <vector>

#include "absl/algorithm/container.h"
#include "absl/base/casts.h"
#include "absl/base/internal/endian.h"
#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_set.h"
#include "absl/random/discrete_distribution.h"
#include "absl/random/distributions.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/types/span.h"
#include "google/protobuf/repeated_field.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/config/v1/p4types.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_fuzzer/annotation_util.h"
#include "p4_fuzzer/fuzzer_config.h"
#include "p4_fuzzer/mutation.h"
#include "p4_pdpi/internal/ordered_map.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/netaddr/ipv6_address.h"
#include "p4_pdpi/utils/ir.h"
#include "p4_pdpi/entity_keys.h"

namespace p4_fuzzer {

using ::absl::gntohll;

using ::absl::Uniform;
using ::pdpi::TableEntryKey;
using ::p4::v1::Action;
using ::p4::v1::FieldMatch;
using ::p4::v1::TableEntry;
using ::p4::v1::Update;
using ::pdpi::IrTableDefinition;

constexpr int kBitsInByte = 8;

// The probability that another entry is added to an update. 0.98 has been
// empirically determined to lead to big enough updates so that the test runs
// fast, but also sometimes generates small updates, which increases coverage.
constexpr float kAddUpdateProbability = 0.98;
// The probability of using a wildcard for a ternary or lpm match field.
constexpr float kFieldMatchWildcardProbability = 0.05;

constexpr char kP4PortTypeName[] = "port_id_t";
constexpr char kP4QosQueueTypeName[] = "qos_queue_t";
constexpr char kP4NeighborTypeName[] = "neighbor_id_t";

bool IsPort(
    const p4::config::v1::P4NamedType& type_name,
    const google::protobuf::RepeatedPtrField<pdpi::IrMatchFieldReference>&
        references) {
  return type_name.name() == kP4PortTypeName;
}

bool IsQosQueue(
    const p4::config::v1::P4NamedType& type_name,
    const google::protobuf::RepeatedPtrField<pdpi::IrMatchFieldReference>&
        references) {
  return type_name.name() == kP4QosQueueTypeName;
}

bool IsNeighbor(
    const p4::config::v1::P4NamedType& type_name,
    const google::protobuf::RepeatedPtrField<pdpi::IrMatchFieldReference>&
        references) {
  return type_name.name() == kP4NeighborTypeName;
}

bool IsReferring(
    const p4::config::v1::P4NamedType& type_name,
    const google::protobuf::RepeatedPtrField<pdpi::IrMatchFieldReference>&
        references) {
  return !references.empty();
}

bool IsDisabledForFuzzing(const FuzzerConfig& config, absl::string_view name) {
  return config.disabled_fully_qualified_names.contains(name);
}

namespace {

// An item and its associated weight when using a discrete distribution.
template <typename T>
struct WeightedItem {
  T item;
  int64_t weight;
};

template <typename T>
const T& DiscreteFromSpan(absl::BitGen* gen,
                          absl::Span<const WeightedItem<T>> span) {
  CHECK(!span.empty());  // Crash OK
  std::vector<int> weights;
  weights.reserve(span.size());
  for (const auto& item : span) weights.push_back(item.weight);
  int index =
      absl::discrete_distribution<>(weights.begin(), weights.end())(*gen);
  return span[index].item;
}

// Implicit conversion to Span does not seem to work correctly for templated
// code.
template <typename T>
const T& DiscreteFromSpan(absl::BitGen* gen,
                          const std::vector<WeightedItem<T>>& vec) {
  return DiscreteFromSpan(gen, absl::MakeConstSpan(vec));
}

std::string FuzzPort(absl::BitGen* gen, const FuzzerConfig& config) {
  return UniformFromSpan(gen, config.ports);
}

inline int DivideRoundedUp(const unsigned int n, const unsigned int d) {
  if (n == 0 || d == 0) {
    return 0;
  }

  return (n - 1) / d + 1;
}

absl::StatusOr<p4::v1::ActionProfileAction> FuzzActionProfileAction(
    absl::BitGen* gen, const FuzzerConfig& config,
    const SwitchState& switch_state,
    const pdpi::IrTableDefinition& ir_table_info, int max_weight) {
  p4::v1::ActionProfileAction action;

  ASSIGN_OR_RETURN(
      *action.mutable_action(),
      FuzzAction(gen, config, switch_state,
                 UniformFromSpan(gen, AllValidActions(config, ir_table_info))
                     .action()));

  action.set_weight(Uniform<int32_t>(*gen, 1, max_weight));
  action.set_watch_port(FuzzPort(gen, config));

  return action;
}

// Checks whether an unmutated update is unacceptable with respect to the fuzzer
// config, current switch state, and the set of updates already in this batch.
// Currently, an unmutated update may be unacceptable by:
// - Inserting entries into a full table, which is configured such that the
//   fuzzer should not exceed its resource guarantees.
// - An update with the same key already exists in the request.
// - Inserting an existing entry.
bool IsAccidentallyInvalidUpdate(
    const FuzzerConfig& config, const SwitchState& switch_state,
    const AnnotatedWriteRequest& request,
    const absl::flat_hash_set<pdpi::TableEntryKey>& entry_keys_in_request,
    const AnnotatedUpdate& candidate_update) {
  // Mutated updates are never accidentally invalid (they should always be
  // invalid) so return early if update contains any mutations.
  if (!candidate_update.mutations().empty()) return false;

  // Table entries are the only entity types used. Even if this is the case,
  // existence of a table entry should always be checked before accessing.
  if (candidate_update.pi().entity().has_table_entry()) {
    const TableEntry& candidate_entry =
        candidate_update.pi().entity().table_entry();
    // Checks for duplicates in current write request.
    if (entry_keys_in_request.contains(pdpi::TableEntryKey(candidate_entry))) {
      return true;
    }
    // Checks that an insert does not insert an existing entry.
    if (candidate_update.pi().type() == p4::v1::Update_Type_INSERT &&
        switch_state.GetTableEntry(candidate_entry).has_value()) {
      return true;
    }
  }

  const std::string& table_name =
      candidate_update.ir().entity().table_entry().table_name();
  // See if the update should be discarded because it is trying to insert into a
  // table that has a strict resource limit and cannot accommodate more inserts
  // than is already in the write request.
  if (candidate_update.ir().type() == p4::v1::Update_Type_INSERT &&
      config.tables_for_which_to_not_exceed_resource_guarantees.contains(
          table_name)) {
    // We determine how many entries we are trying to insert in the relevant
    // table including the candidate update.
    int num_inserts = 1;
    for (const auto& update : request.updates()) {
      if (update.ir().entity().table_entry().table_name() == table_name &&
          update.ir().type() == p4::v1::Update_Type_INSERT) {
        num_inserts++;
      }
      // Because batches are handled non-deterministically, we want to be
      // conservative and not take any deletes into account.
    }
    // If the table cannot accommodate sufficiently many inserts, then the
    // candidate update is 'bad'.
    return !switch_state.CanAccommodateInserts(
        candidate_update.pi().entity().table_entry().table_id(), num_inserts);
  }

  return false;
}

// Returns all valid table ids.
std::vector<uint32_t> AllValidTableIdsForP4rtRole(const FuzzerConfig& config) {
  std::vector<uint32_t> table_ids;

  for (const IrTableDefinition& table : AllValidTablesForP4RtRole(config)) {
    table_ids.push_back(table.preamble().id());
  }

  return table_ids;
}

// Returns the table ids of tables that use one shot action selector
// programming.
std::vector<uint32_t> GetOneShotTableIds(const FuzzerConfig& config) {
  std::vector<uint32_t> table_ids;

  for (const IrTableDefinition& table : AllValidTablesForP4RtRole(config)) {
    if (table.uses_oneshot()) {
      table_ids.push_back(table.preamble().id());
    }
  }

  return table_ids;
}

// Returns the table ids of tables that contain at least one exact match field.
std::vector<uint32_t> GetMandatoryMatchTableIds(const FuzzerConfig& config) {
  std::vector<uint32_t> table_ids;

  for (const IrTableDefinition& table : AllValidTablesForP4RtRole(config)) {
    for (auto& [match_id, match] : Ordered(table.match_fields_by_id())) {
      if (match.match_field().match_type() ==
          p4::config::v1::MatchField::EXACT) {
        table_ids.push_back(table.preamble().id());
        break;
      }
    }
  }

  return table_ids;
}

// Returns the table ids of tables that don't have role config.role.
std::vector<uint32_t> GetDifferentRoleTableIds(const FuzzerConfig& config) {
  std::vector<uint32_t> table_ids;

  for (auto& [key, table] : Ordered(config.info.tables_by_id())) {
    if (table.role() == config.role) continue;
    table_ids.push_back(key);
  }
  return table_ids;
}

// Returns the table ids of all tables that have at least one match field or
// action argument that satisfies the given predicate.
std::vector<uint32_t> GetTableIdsWithValuePredicate(
    const FuzzerConfig& config, P4ValuePredicate predicate) {
  std::vector<uint32_t> table_ids;

  for (const IrTableDefinition& table : AllValidTablesForP4RtRole(config)) {
    bool include = false;
    for (const auto& [match_id, match] : table.match_fields_by_id()) {
      if (predicate(match.match_field().type_name(), match.references())) {
        include = true;
        break;
      }
    }
    for (const auto& action : table.entry_actions()) {
      for (const auto& [param_id, param] : action.action().params_by_id()) {
        if (predicate(param.param().type_name(), param.references())) {
          include = true;
          break;
        }
      }
    }
    if (include) table_ids.push_back(table.preamble().id());
  }

  return table_ids;
}

// Randomly generates an update type.
Update::Type FuzzUpdateType(absl::BitGen* gen, const SwitchState& state) {
  if (state.AllTablesEmpty()) {
    // Insert if there are no entries to delete.
    return Update::INSERT;
  } else {
    // The probability of inserting a entry is larger than the probability of
    // removing one, which means that eventually the switch fills up. 0.7 is a
    // nice number because it causes the switch to fill up quickly, but there is
    // still a good chance to get a couple of deletes in a row.
    if (absl::Bernoulli(*gen, 0.7)) {
      return Update::INSERT;
    } else {
      // Equally split the rest between modify and delete.
      if (absl::Bernoulli(*gen, 0.5)) {
        return Update::MODIFY;
      }
      return Update::DELETE;
    }
  }
}

// Randomly changes the table_entry, without affecting the key fields.
void FuzzNonKeyFields(absl::BitGen* gen, const FuzzerConfig& config,
                      const SwitchState& switch_state,
                      TableEntry* table_entry) {
  // With some probability, don't modify the element at all.
  if (absl::Bernoulli(*gen, 0.2)) return;

  if (absl::Bernoulli(*gen, 0.25)) {
    if (absl::Bernoulli(*gen, 0.5)) {
      // TODO: can't remove action at the moment, because
      // IsWellformedUpdate
      // will think the update is no longer well-formed.
    } else {
      if (auto table_definition = gutil::FindOrStatus(
              config.info.tables_by_id(), table_entry->table_id());
          table_definition.ok()) {
        // Try up to 3 times to create a new action.
        for (int i = 0; i < 3; ++i) {
          if (auto action =
                  FuzzAction(gen, config, switch_state, *table_definition);
              action.ok()) {
            *table_entry->mutable_action() = *action;
            break;
          }
        }
      }
    }
  }

  // Remove or modify metadata.
  if (absl::Bernoulli(*gen, 0.25)) {
    if (absl::Bernoulli(*gen, 0.5)) {
      table_entry->clear_metadata();
    } else {
      // TODO: Currently, we only want to use metadata that looks
      // similar to our expectation. Eventually, we should fuzz just a random ID
      // with e.g. `FuzzRandomId(gen)`.
      table_entry->set_metadata(
          absl::StrCat("orion_cookie: ", FuzzUint64(gen, /*bits=*/64)));
    }
  }
  // TODO: also fuzz meters
}

// Generates `WeightedItems` for all valid table_ids where weight is equal to
// table_size.
std::vector<WeightedItem<uint32_t>> GenerateAllValidWeightedTableIds(
    const FuzzerConfig& config) {
  std::vector<WeightedItem<uint32_t>> weighted_table_ids;
  for (const IrTableDefinition& table : AllValidTablesForP4RtRole(config)) {
    weighted_table_ids.push_back(WeightedItem<uint32_t>{
        .item = table.preamble().id(),
        .weight = table.size(),
    });
  }
  return weighted_table_ids;
}

std::vector<WeightedItem<uint32_t>> GenerateNonEmptyWeightedTableIds(
    const FuzzerConfig& config, const SwitchState& switch_state) {
  std::vector<WeightedItem<uint32_t>> non_empty_weighted_table_ids;
  for (const auto& weighted_table_id :
       GenerateAllValidWeightedTableIds(config)) {
    if (switch_state.IsTableEmpty(weighted_table_id.item)) continue;
    non_empty_weighted_table_ids.push_back(weighted_table_id);
  }
  return non_empty_weighted_table_ids;
}

// Randomly generates an INSERT, MODIFY or DELETE update. The update may be
// mutated (see go/p4-fuzzer-design for mutation types).
AnnotatedUpdate FuzzUpdate(absl::BitGen* gen, const FuzzerConfig& config,
                           const SwitchState& switch_state) {
  CHECK_GT(AllValidTablesForP4RtRole(config).size(), 0)  // Crash OK
      << "Cannot generate updates for program with no tables";

  Mutation mutation;
  bool do_mutate = false;
  std::vector<uint32_t> mutation_table_ids;

  if (absl::Bernoulli(*gen, config.mutate_update_probability)) {
    do_mutate = true;
    mutation = FuzzMutation(gen, config);
    switch (mutation) {
      case Mutation::INVALID_ACTION_SELECTOR_WEIGHT:
        mutation_table_ids = GetOneShotTableIds(config);
        break;

      case Mutation::MISSING_MANDATORY_MATCH_FIELD:
        mutation_table_ids = GetMandatoryMatchTableIds(config);
        break;

      case Mutation::INVALID_PORT:
        mutation_table_ids = GetTableIdsWithValuePredicate(config, IsPort);
        break;

      case Mutation::INVALID_QOS_QUEUE:
        mutation_table_ids = GetTableIdsWithValuePredicate(config, IsQosQueue);
        break;

      case Mutation::INVALID_NEIGHBOR_ID:
        mutation_table_ids = GetTableIdsWithValuePredicate(config, IsNeighbor);
        break;

      case Mutation::INVALID_REFERRING_ID:
        mutation_table_ids = GetTableIdsWithValuePredicate(config, IsReferring);
        break;

      case Mutation::DIFFERENT_ROLE:
        mutation_table_ids = GetDifferentRoleTableIds(config);
        break;
      // All other mutations can act on every valid table.
      default:
        mutation_table_ids = AllValidTableIdsForP4rtRole(config);
        break;
    }

    if (mutation_table_ids.empty()) {
      // Retry.
      return FuzzUpdate(gen, config, switch_state);
    }
  }

  Update::Type type = FuzzUpdateType(gen, switch_state);
  Update update;
  update.set_type(type);

  switch (type) {
    case Update::INSERT: {
      int table_id;
      if (do_mutate) {
        table_id = UniformFromSpan(gen, mutation_table_ids);
      } else {
        table_id = FuzzTableId(gen, config);
      }

      // This might (with low probability) generate an entry that already
      // exists leading to a duplicate insert. This is fine since `IsBadUpdate`
      // will catch it and discard the update.
      absl::StatusOr<p4::v1::TableEntry> table_entry =
          FuzzValidTableEntry(gen, config, switch_state, table_id);
      if (!table_entry.ok()) {
        // Retry.
        return FuzzUpdate(gen, config, switch_state);
      }

      *update.mutable_entity()->mutable_table_entry() = *table_entry;

      break;
    }
    case Update::MODIFY: {
      const int table_id = FuzzNonEmptyTableId(gen, config, switch_state);
      TableEntry table_entry =
          UniformValueFromMap(gen, switch_state.GetTableEntries(table_id));
      FuzzNonKeyFields(gen, config, switch_state, &table_entry);
      *update.mutable_entity()->mutable_table_entry() = table_entry;
      break;
    }
    case Update::DELETE: {
      const int table_id = FuzzNonEmptyTableId(gen, config, switch_state);
      // Within a single call of FuzzWriteRequest, this might delete the same
      // entry multiple times. This is fine since `IsBadUpdate` will catch it
      // and discard the update.
      TableEntry table_entry =
          UniformValueFromMap(gen, switch_state.GetTableEntries(table_id));
      FuzzNonKeyFields(gen, config, switch_state, &table_entry);
      *update.mutable_entity()->mutable_table_entry() = table_entry;
      break;
    }
    default:
      LOG(FATAL) << "Unsupported update type " << type;
  }

  if (do_mutate) {
    if (!MutateUpdate(gen, config, &update, switch_state, mutation).ok()) {
      // Retry mutating the update.
      return FuzzUpdate(gen, config, switch_state);
    }

    return GetAnnotatedUpdate(config.info, update,
                              /* mutations = */ {mutation});
  }

  return GetAnnotatedUpdate(config.info, update, /* mutations = */ {});
}

}  // namespace

// Gets the action profile corresponding to the given table from the IrP4Info.
absl::StatusOr<p4::config::v1::ActionProfile> GetActionProfile(
    const pdpi::IrP4Info& ir_info, int table_id) {
  for (const auto& [id, action_profile_definition] :
       Ordered(ir_info.action_profiles_by_id())) {
    if (action_profile_definition.has_action_profile()) {
      // Does the action profile apply to the given table?
      auto& action_profile = action_profile_definition.action_profile();
      if (absl::c_linear_search(action_profile.table_ids(), table_id)) {
        return action_profile;
      }
    }
  }

  return gutil::NotFoundErrorBuilder()
         << "No action profile corresponds to table with id " << table_id;
}

const std::vector<IrTableDefinition> AllValidTablesForP4RtRole(
    const FuzzerConfig& config) {
  std::vector<IrTableDefinition> tables;

  for (auto& [key, table] : Ordered(config.info.tables_by_id())) {
    // Tables with the wrong role can't be modified by the controller.
    if (table.role() != config.role) continue;
    // Tables without actions cannot have valid table entries.
    if (table.entry_actions().empty()) continue;
    // Skip deprecated, unused, and disallowed tables.
    if (pdpi::IsElementDeprecated(table.preamble().annotations()) ||
        IsDisabledForFuzzing(config, table.preamble().name()))
      continue;
    tables.push_back(table);
  }
  return tables;
}

const std::vector<pdpi::IrActionReference> AllValidActions(
    const FuzzerConfig& config, const pdpi::IrTableDefinition& table) {
  std::vector<pdpi::IrActionReference> actions;

  for (const auto& action : table.entry_actions()) {
    // Skip deprecated, unused, and disallowed actions.
    if (pdpi::IsElementDeprecated(action.action().preamble().annotations()) ||
        IsDisabledForFuzzing(config, action.action().preamble().name()))
      continue;
    actions.push_back(action);
  }

  return actions;
}

const std::vector<pdpi::IrMatchFieldDefinition> AllValidMatchFields(
    const FuzzerConfig& config, const pdpi::IrTableDefinition& table) {
  std::vector<pdpi::IrMatchFieldDefinition> match_fields;

  for (const auto& [_, match_field_info] :
       Ordered(table.match_fields_by_id())) {
    // Skip deprecated, unused, and disallowed fields.
    const std::string fully_qualified_match_field = absl::StrCat(
        table.preamble().name(), ".", match_field_info.match_field().name());
    if (pdpi::IsElementDeprecated(
            match_field_info.match_field().annotations()) ||
        IsDisabledForFuzzing(config, fully_qualified_match_field))
      continue;

    match_fields.push_back(match_field_info);
  }

  return match_fields;
}

std::string FuzzRandomId(absl::BitGen* gen, int min_chars, int max_chars) {
  // Only sample from printable/readable characters, to make debugging easier.
  // There is a smoke test that uses crazy characters.
  static constexpr char kIdChars[] = "abcdefghijklmnopqrstuvwxyz0123456789-";

  CHECK_LE(min_chars, max_chars);  // Crash OK
  int num_chars =
      absl::Uniform(absl::IntervalClosedClosed, *gen, min_chars, max_chars);
  std::string id;
  for (int i = 0; i < num_chars; i++) {
    id += kIdChars[absl::Uniform<int>(*gen, 0, sizeof(kIdChars) - 1)];
  }
  return id;
}

// Randomly generates a table id.
int FuzzTableId(absl::BitGen* gen, const FuzzerConfig& config) {
  return DiscreteFromSpan(gen, GenerateAllValidWeightedTableIds(config));
}

int FuzzNonEmptyTableId(absl::BitGen* gen, const FuzzerConfig& config,
                        const SwitchState& switch_state) {
  CHECK(!switch_state.AllTablesEmpty())  // Crash OK
      << "state: " << switch_state.SwitchStateSummary();
  return DiscreteFromSpan(
      gen, GenerateNonEmptyWeightedTableIds(config, switch_state));
}

Mutation FuzzMutation(absl::BitGen* gen, const FuzzerConfig& config) {
  std::vector<int> valid_indexes;

  for (int i = Mutation_MIN; i <= Mutation_MAX; ++i) {
    if (Mutation_IsValid(i)) {
      valid_indexes.push_back(i);
    }
  }

  return static_cast<Mutation>(UniformFromSpan(gen, valid_indexes));
}

std::string SetUnusedBitsToZero(int used_bits, std::string data) {
  const int bytes = data.size();
  const int used_bytes = DivideRoundedUp(used_bits, kBitsInByte);
  const int unused_bytes = bytes - used_bytes;
  const int overhanging_bits = used_bits % kBitsInByte;

  CHECK_GE(used_bits, 0) << "data: '" << data << "'";
  CHECK_GE(bytes * kBitsInByte, used_bits) << "data: '" << data << "'";

  // Zero the completely unused bytes.
  for (int i = 0; i < unused_bytes; ++i) data[i] = 0;

  // Zero the remaining unused bits.
  if (overhanging_bits != 0) {
    const int padding_mask = (1 << overhanging_bits) - 1;
    data[unused_bytes] &= padding_mask;
  }
  return data;
}

std::string ZeroNLeastSignificantBits(int zero_bits, std::string data) {
  const int bytes = data.size();
  const int total_bits = bytes * kBitsInByte;
  const int used_bits = total_bits - zero_bits;
  const int fully_used_bytes = used_bits / kBitsInByte;
  const bool has_partial_byte = used_bits % kBitsInByte != 0;

  CHECK_GE(total_bits, zero_bits);  // Crash okay
  CHECK_GE(zero_bits, 0);           // Crash okay

  for (int i = fully_used_bytes; i < bytes; i++) {
    if (i == fully_used_bytes && has_partial_byte) {
      const int mask = ~((1 << (kBitsInByte - (used_bits % kBitsInByte))) - 1);
      data[i] &= mask;
    } else {
      data[i] = 0;
    }
  }
  return data;
}

uint64_t BitsToUint64(const std::string& data) {
  CHECK_EQ(data.size(), sizeof(uint64_t)) << "Data: " << data;
  return gntohll(reinterpret_cast<const uint64_t&>(data[0]));
}

std::string FuzzBits(absl::BitGen* gen, int bits, int bytes) {
  std::string data(bytes, 0);
  for (int i = 0; i < bytes; ++i)
    data[i] = absl::implicit_cast<char>(Uniform<uint8_t>(*gen));

  return SetUnusedBitsToZero(bits, std::move(data));
}

std::string FuzzBits(absl::BitGen* gen, int bits) {
  return FuzzBits(gen, bits, DivideRoundedUp(bits, kBitsInByte));
}

std::string FuzzNonZeroBits(absl::BitGen* gen, int bits) {
  CHECK_NE(bits, 0);  // Crash okay
  while (true) {
    std::string result = FuzzBits(gen, bits);
    if (!pdpi::IsAllZeros(result)) return result;
  }
}

// Fuzzes a value, with special handling for ports and IDs.
// TODO: This will sometimes return an empty string, which is
// always an invalid value.
absl::StatusOr<std::string> FuzzValue(
    absl::BitGen* gen, const FuzzerConfig& config,
    const SwitchState& switch_state,
    const p4::config::v1::P4NamedType& type_name, int bits,
    const google::protobuf::RepeatedPtrField<pdpi::IrMatchFieldReference>&
        references,
    bool non_zero) {
  // A port: pick any valid port randomly.
  if (IsPort(type_name)) {
    return FuzzPort(gen, config);
  }

  // A qos queue: pick any valid qos queue randomly.
  if (IsQosQueue(type_name)) {
    return UniformFromSpan(gen, config.qos_queues);
  }

  // A neighbor ID (not referring to anything): Pick a random IPv6 address.
  if (IsNeighbor(type_name) && references.empty()) {
    std::bitset<128> ipv6_bits;
    for (int i = 0; i < 128; ++i) {
      ipv6_bits.set(i, absl::Bernoulli(*gen, 0.5));
    }
    return netaddr::Ipv6Address::OfBitset(ipv6_bits).ToString();
  }

  // A string ID (not referring to anything): Pick a fresh random ID.
  if (bits == 0 && references.empty()) {
    return FuzzRandomId(gen, /*min_chars=*/non_zero ? 1 : 0);
  }

  // An ID that refers to another match field: pick any ID that already exists
  // for that match field.
  if (!references.empty()) {
    absl::btree_set<std::string> possible_values =
        switch_state.GetIdsForMatchField(references[0]);
    // Intersect the sets of possible values to ones existing in every table
    // that this field references.
    for (int i = 1; i < references.size(); i++) {
      // If there are no possible IDs left, set intersections will be
      // idempotent.
      if (possible_values.empty()) break;

      absl::btree_set<std::string> intersection;
      absl::c_set_intersection(
          possible_values, switch_state.GetIdsForMatchField(references[i]),
          std::inserter(intersection, intersection.begin()));
      possible_values = std::move(intersection);
    }
    if (possible_values.empty()) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Could not find value, no IDs yet for some referenced fields.";
    }

    std::vector<std::string> value_vector(possible_values.begin(),
                                          possible_values.end());
    return UniformFromSpan(gen, value_vector);
  }

  // Some other value: Normally fuzz bits randomly.
  if (non_zero) return FuzzNonZeroBits(gen, bits);
  return FuzzBits(gen, bits);
}

uint64_t FuzzUint64(absl::BitGen* gen, int bits) {
  return BitsToUint64(FuzzBits(gen, bits, sizeof(uint64_t)));
}

p4::v1::FieldMatch FuzzTernaryFieldMatch(absl::BitGen* gen,
                                         const FuzzerConfig& config, int bits) {
  std::string mask = FuzzNonZeroBits(gen, bits);
  std::string value = FuzzBits(gen, bits);

  // If a mask bit is 0, the corresponding value bit also has to be 0.
  value = pdpi::Intersection(value, mask).value();

  p4::v1::FieldMatch match;
  match.mutable_ternary()->set_mask(mask);
  match.mutable_ternary()->set_value(value);
  return match;
}

p4::v1::FieldMatch FuzzLpmFieldMatch(absl::BitGen* gen,
                                     const FuzzerConfig& config,
                                     const SwitchState& switch_state,
                                     int bits) {
  // Since /8, /16, /24, and /32 are common, we want to bias the fuzzer to
  // generate more of them.
  std::vector<int> likely_bits;
  for (int i = kBitsInByte; i <= bits; i += kBitsInByte) {
    likely_bits.push_back(i);
  }

  int prefix_len;
  if (bits >= kBitsInByte && absl::Bernoulli(*gen, 0.2)) {
    prefix_len = UniformFromSpan(gen, likely_bits);
  } else {
    // Don't generate /0, since we don't want wildcards
    prefix_len = absl::Uniform(*gen, 1, bits + 1);
  }

  p4::v1::FieldMatch match;
  match.mutable_lpm()->set_prefix_len(prefix_len);
  // We need a value that has prefix_len many random bits, followed by zeros.
  match.mutable_lpm()->set_value(
      ZeroNLeastSignificantBits(bits - prefix_len, FuzzBits(gen, bits)));
  return match;
}

absl::StatusOr<p4::v1::FieldMatch> FuzzExactFieldMatch(
    absl::BitGen* gen, const FuzzerConfig& config,
    const SwitchState& switch_state,
    const pdpi::IrMatchFieldDefinition& ir_match_field_info) {
  p4::v1::FieldMatch match;
  p4::config::v1::MatchField field = ir_match_field_info.match_field();
  // Note that exact messages have to be provided, even if the value is 0.
  ASSIGN_OR_RETURN(
      std::string value,
      FuzzValue(gen, config, switch_state, field.type_name(), field.bitwidth(),
                ir_match_field_info.references(), /*non_zero=*/true));

  match.mutable_exact()->set_value(value);
  return match;
}

absl::StatusOr<p4::v1::FieldMatch> FuzzOptionalFieldMatch(
    absl::BitGen* gen, const FuzzerConfig& config,
    const SwitchState& switch_state,
    const pdpi::IrMatchFieldDefinition& ir_match_field_info) {
  p4::v1::FieldMatch match;
  p4::config::v1::MatchField field = ir_match_field_info.match_field();
  ASSIGN_OR_RETURN(
      std::string value,
      FuzzValue(gen, config, switch_state, field.type_name(), field.bitwidth(),
                ir_match_field_info.references(), /*non_zero=*/true));
  match.mutable_optional()->set_value(value);
  return match;
}

absl::StatusOr<p4::v1::FieldMatch> FuzzFieldMatch(
    absl::BitGen* gen, const FuzzerConfig& config,
    const SwitchState& switch_state,
    const pdpi::IrMatchFieldDefinition& ir_match_field_info) {
  const p4::config::v1::MatchField& match_field_info =
      ir_match_field_info.match_field();

  p4::v1::FieldMatch match;
  switch (match_field_info.match_type()) {
    case p4::config::v1::MatchField::TERNARY: {
      match = FuzzTernaryFieldMatch(gen, config, match_field_info.bitwidth());
      break;
    }
    case p4::config::v1::MatchField::LPM: {
      match = FuzzLpmFieldMatch(gen, config, switch_state,
                                match_field_info.bitwidth());
      break;
    }
    case p4::config::v1::MatchField::EXACT: {
      ASSIGN_OR_RETURN(match, FuzzExactFieldMatch(gen, config, switch_state,
                                                  ir_match_field_info));
      break;
    }
    case p4::config::v1::MatchField::OPTIONAL: {
      ASSIGN_OR_RETURN(match, FuzzOptionalFieldMatch(gen, config, switch_state,
                                                     ir_match_field_info));
      break;
    }
    default:
      LOG(FATAL) << "Unsupported match: " << match_field_info.DebugString();
  }
  match.set_field_id(match_field_info.id());
  return match;
}

absl::StatusOr<p4::v1::Action> FuzzAction(
    absl::BitGen* gen, const FuzzerConfig& config,
    const SwitchState& switch_state,
    const pdpi::IrActionDefinition& ir_action_info) {
  p4::v1::Action action;
  action.set_action_id(ir_action_info.preamble().id());

  for (auto& [id, ir_param] : Ordered(ir_action_info.params_by_id())) {
    p4::v1::Action::Param* param = action.add_params();
    param->set_param_id(id);
    ASSIGN_OR_RETURN(
        std::string value,
        FuzzValue(gen, config, switch_state, ir_param.param().type_name(),
                  ir_param.param().bitwidth(), ir_param.references(),
                  /*non_zero=*/true),
        _.SetPrepend() << "while fuzzing parameter '" << ir_param.param().name()
                       << "' of action '" << ir_action_info.preamble().name()
                       << "': ");
    param->set_value(value);
  }

  return action;
}

// Gets a set of actions with a skewed distribution of weights, which add up to
// at most the max_group_size of the action profile by repeatedly sampling a
// uniform weight from 1 to the maximum possible weight remaining. We could
// achieve uniform weights between 1 and max_group_size, which add up to
// max_group_size by using e.g. a Dirichlet Distribution via Pólya's urn (see
// https://en.wikipedia.org/wiki/Dirichlet_distribution#P%C3%B3lya's_urn).
// However, uniform sampling gives us highly clustered weights almost all the
// time and we prefer to generate skewed weights more often. Therefore, this
// simpler approach, should serve us well.
absl::StatusOr<p4::v1::ActionProfileActionSet> FuzzActionProfileActionSet(
    absl::BitGen* gen, const FuzzerConfig& config,
    const SwitchState& switch_state,
    const pdpi::IrTableDefinition& ir_table_info) {
  p4::v1::ActionProfileActionSet action_set;

  ASSIGN_OR_RETURN(
      auto action_profile,
      GetActionProfile(config.info, ir_table_info.preamble().id()));

  if (action_profile.has_sum_of_members()) {
    int max_number_of_actions = action_profile.max_group_size() != 0
                                    ? action_profile.max_group_size()
                                    : kActionProfileActionSetMaxCardinality;
    int number_of_actions = Uniform<int>(
          absl::IntervalClosedClosed, *gen,
          config.no_empty_action_profile_groups ? 1 : 0, max_number_of_actions);

    // Get the max member weight from the P4Info if it is set.
    int max_member_weight =
        action_profile.sum_of_members().max_member_weight() != 0
            ? action_profile.sum_of_members().max_member_weight()
            : kActionProfileMaxMemberWeight;

    for (int i = 0; i < number_of_actions; i++) {
      ASSIGN_OR_RETURN(auto action, FuzzActionProfileAction(
                                        gen, config, switch_state,
                                        ir_table_info, max_member_weight));
      *action_set.add_action_profile_actions() = action;
    }

    return action_set;
  } else {
    // If the action profile does not use SumOfMembers semantics, then it must
    // be SumOfWeights since that is both the default and the only other option.

    // The max_group_size specifies the maximum total weight of a group of
    // actions in an Action Selector (described by an ActionProfileActionSet).
    // If max_group_size is 0, then any weights less than size are allowed by
    // the server.
    int unallocated_weight = action_profile.max_group_size() == 0
                                 ? action_profile.size()
                                 : action_profile.max_group_size();

    // Note that the semantics of `size` in an action selector is the maximum
    // sum of all member weights across ALL selector groups. The
    // `max_group_size` is the maximum sum of all member weights within a
    // single group. Thus, the maximum total weight of a single group should
    // be no larger than either the max_group_size or the size.
    // TODO: When https://github.com/p4lang/p4runtime/issues/355
    // is fixed, `max_group_size` will never be greater than `size`, rendering
    // this assignment unnecessary.
    unallocated_weight = static_cast<int>(
        std::min(int64_t{unallocated_weight}, action_profile.size()));

    // It is entirely unclear what should happen if max_group_size or size is
    // negative or if size is 0. Since these values are nonsensical, we will
    // return an InvalidArgumentError until the specification changes.
    // TODO: This if-statement can also disappear if
    // https://github.com/p4lang/p4runtime/issues/355 is resolved, ruling out
    // these cases.
    if (unallocated_weight <= 0) {
      return gutil::InvalidArgumentErrorBuilder()
             << "non-positive size '" << action_profile.size()
             << "' or negative max_group_size '"
             << action_profile.max_group_size() << "' in action profile '"
             << action_profile.preamble().alias() << "'";
    }

    // We want to randomly select some number of actions up to our max
    // cardinality; however, we can't have more actions than the amount of
    // weight we support since every action must have weight >= 1.
    int number_of_actions =  Uniform<int>(
          absl::IntervalClosedClosed, *gen,
          config.no_empty_action_profile_groups ? 1 : 0,
          std::min(unallocated_weight, kActionProfileActionSetMaxCardinality));

    for (int i = 0; i < number_of_actions; i++) {
      // Since each action must have at least weight 1, we need to take the
      // number of remaining actions into account to determine the acceptable
      // max weight.
      int remaining_actions = number_of_actions - i - 1;
      int max_weight = unallocated_weight - remaining_actions;

      ASSIGN_OR_RETURN(auto action,
                       FuzzActionProfileAction(gen, config, switch_state,
                                               ir_table_info, max_weight));
      *action_set.add_action_profile_actions() = action;
      unallocated_weight -= action.weight();
    }

    return action_set;
  }
}

void EnforceTableConstraints(absl::BitGen* gen, const FuzzerConfig& config,
                             const SwitchState& switch_state,
                             const pdpi::IrTableDefinition& ir_table_info,
                             TableEntry* table_entry) {
  // TODO: implement program independent version of this function.
}

absl::StatusOr<p4::v1::TableAction> FuzzAction(
    absl::BitGen* gen, const FuzzerConfig& config,
    const SwitchState& switch_state,
    const pdpi::IrTableDefinition& table_definition) {
  p4::v1::TableAction result;
  // Generate the action.
  if (!table_definition.uses_oneshot()) {
    // Normal table, so choose a non-default action.
    ASSIGN_OR_RETURN(
        *result.mutable_action(),
        FuzzAction(
            gen, config, switch_state,
            UniformFromSpan(gen, AllValidActions(config, table_definition))
                .action()));
  } else {
    ASSIGN_OR_RETURN(*result.mutable_action_profile_action_set(),
                     FuzzActionProfileActionSet(gen, config, switch_state,
                                                table_definition));
  }
  return result;
}

absl::StatusOr<TableEntry> FuzzValidTableEntry(
    absl::BitGen* gen, const FuzzerConfig& config,
    const SwitchState& switch_state,
    const pdpi::IrTableDefinition& ir_table_info) {
  TableEntry table_entry;
  table_entry.set_table_id(ir_table_info.preamble().id());

  // Generate the matches.
  for (const pdpi::IrMatchFieldDefinition& match_field_info :
       AllValidMatchFields(config, ir_table_info)) {
    // If the field can have wildcards, we generate a wildcard match with
    // probability `kFieldMatchWildcardProbability`.
    // In the P4RT spec, wildcards are represented as the absence of a match
    // field.
    bool can_have_wildcard = match_field_info.match_field().match_type() ==
                                 p4::config::v1::MatchField::TERNARY ||
                             match_field_info.match_field().match_type() ==
                                 p4::config::v1::MatchField::OPTIONAL ||
                             match_field_info.match_field().match_type() ==
                                 p4::config::v1::MatchField::LPM;
    if (can_have_wildcard &&
        absl::Bernoulli(*gen, kFieldMatchWildcardProbability)) {
      continue;
    }

    auto match = FuzzFieldMatch(gen, config, switch_state, match_field_info);
    if (match.ok()) {
      *table_entry.add_match() = *match;
    } else {
      return match.status();
    }
  }

  EnforceTableConstraints(gen, config, switch_state, ir_table_info,
                          &table_entry);

  // Generate the action.
  ASSIGN_OR_RETURN(*table_entry.mutable_action(),
                   FuzzAction(gen, config, switch_state, ir_table_info),
                   _.SetPrepend() << "while fuzzing action: ");

  // Set cookie and priority.
  table_entry.set_metadata(
      absl::StrCat("orion_cookie: ", FuzzUint64(gen, /*bits=*/64)));
  if (ir_table_info.requires_priority()) {
    table_entry.set_priority(FuzzUint64(gen, /*bits=*/16));
  }

  // TODO: Fuzz default actions.
  // TODO: Fuzz meters and counters.
  return table_entry;
}

absl::StatusOr<TableEntry> FuzzValidTableEntry(absl::BitGen* gen,
                                               const FuzzerConfig& config,
                                               const SwitchState& switch_state,
                                               const uint32_t table_id) {
  return FuzzValidTableEntry(
      gen, config, switch_state,
      gutil::FindOrDie(config.info.tables_by_id(), table_id));
}

std::vector<AnnotatedTableEntry> ValidForwardingEntries(
    absl::BitGen* gen, const FuzzerConfig& config, const int num_entries) {
  std::vector<AnnotatedTableEntry> entries;
  SwitchState state(config.info);

  for (int i = 0; i < num_entries; ++i) {
    absl::StatusOr<p4::v1::TableEntry> entry;

    do {
      entry = FuzzValidTableEntry(gen, config, state, FuzzTableId(gen, config));
    } while (entry.ok() && state.GetTableEntry(*entry) != absl::nullopt);
    if (!entry.ok()) {
      // Failed to generate an entry, try again.
      i -= 1;
      continue;
    }

    p4::v1::Update update;
    update.set_type(p4::v1::Update::INSERT);
    *update.mutable_entity()->mutable_table_entry() = *entry;

    CHECK(state.ApplyUpdate(update).ok());  // Crash okay

    entries.push_back(
        GetAnnotatedTableEntry(config.info, *entry, /*mutations = */ {}));
  }

  return entries;
}

AnnotatedWriteRequest FuzzWriteRequest(absl::BitGen* gen,
                                       const FuzzerConfig& config,
                                       const SwitchState& switch_state,
                                       absl::optional<int> max_batch_size) {
  AnnotatedWriteRequest request;
  absl::flat_hash_set<pdpi::TableEntryKey> entry_keys_in_request;

  while (absl::Bernoulli(*gen, kAddUpdateProbability)) {
    if (max_batch_size.has_value() &&
        request.updates_size() >= *max_batch_size) {
      break;
    }
    AnnotatedUpdate update = FuzzUpdate(gen, config, switch_state);
    // Discards updates that are 'bad' and tries again to maintain a simple and
    // predictable distribution of batch sizes. To avoid infinite loops, though
    // other logic should make them impossible, we assume that we produce good
    // updates at least ~0.01% of the time, terminating the loop early w.h.p.
    // only if our success rate is significantly worse than this.
    int update_attempts = 1;
    while (IsAccidentallyInvalidUpdate(config, switch_state, request,
                                       entry_keys_in_request, update) &&
           update_attempts < 10000) {
      update = FuzzUpdate(gen, config, switch_state);
      update_attempts++;
    }
    if (!IsAccidentallyInvalidUpdate(config, switch_state, request,
                                     entry_keys_in_request, update)) {
      *request.add_updates() = update;
      if (update.pi().entity().has_table_entry()) {
        entry_keys_in_request.insert(
            pdpi::TableEntryKey(update.pi().entity().table_entry()));
      }
    }
  }

  return request;
}

}  // namespace p4_fuzzer
