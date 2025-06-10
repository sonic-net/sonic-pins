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
#include "p4_fuzzer/fuzz_util.h"

#include <algorithm>
#include <cstdint>
#include <functional>
#include <iterator>
#include <limits>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/algorithm/container.h"
#include "absl/base/casts.h"
#include "absl/base/internal/endian.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/random/discrete_distribution.h"
#include "absl/random/distributions.h"
#include "absl/random/random.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "absl/types/span.h"
#include "glog/logging.h"
#include "google/protobuf/repeated_field.h"
#include "google/protobuf/repeated_ptr_field.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/config/v1/p4types.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_fuzzer/annotation_util.h"
#include "p4_fuzzer/constraints.h"
#include "p4_fuzzer/fuzzer_config.h"
#include "p4_fuzzer/mutation.h"
#include "p4_fuzzer/switch_state.h"
#include "p4_infra/netaddr/ipv6_address.h"
#include "p4_infra/p4_pdpi/built_ins.h"
#include "p4_infra/p4_pdpi/entity_keys.h"
#include "p4_infra/p4_pdpi/internal/ordered_map.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/ir_utils.h"
#include "p4_infra/p4_pdpi/references.h"
#include "p4_infra/string_encodings/byte_string.h"

namespace p4_fuzzer {

using ::absl::gntohll;

using ::absl::Uniform;
using ::p4::v1::Action;
using ::p4::v1::Entity;
using ::p4::v1::FieldMatch;
using ::p4::v1::MulticastGroupEntry;
using ::p4::v1::Replica;
using ::p4::v1::TableEntry;
using ::p4::v1::Update;
using ::pdpi::EntityKey;
using ::pdpi::IrTableDefinition;
using ::pdpi::IrTableReference;

constexpr int kBitsInByte = 8;

// The probability that another entry is added to an update. 0.98 has been
// empirically determined to lead to big enough updates so that the test runs
// fast, but also sometimes generates small updates, which increases coverage.
constexpr float kAddUpdateProbability = 0.98;

constexpr char kP4PortTypeName[] = "port_id_t";
// Remove unknown queue support when they no longer exist in
// tested images.
constexpr char kP4UnknownQosQueueTypeName[] = "qos_queue_t";
constexpr char kP4CpuQosQueueTypeName[] = "cpu_queue_t";
constexpr char kP4UnicastQosQueueTypeName[] = "unicast_queue_t";
constexpr char kP4MulticastQosQueueTypeName[] = "multicast_queue_t";
constexpr char kP4NeighborTypeName[] = "neighbor_id_t";

bool IsPort(
    const p4::config::v1::P4NamedType& type_name,
    const google::protobuf::RepeatedPtrField<pdpi::IrMatchFieldReference>&
        references) {
  return type_name.name() == kP4PortTypeName;
}

bool IsUnknownQosQueue(
    const p4::config::v1::P4NamedType& type_name,
    const google::protobuf::RepeatedPtrField<pdpi::IrMatchFieldReference>&
        references) {
  return type_name.name() == kP4UnknownQosQueueTypeName;
}

// CPU queues are currently treated the same as unknown QoS queues.
bool IsUnknownQosOrCpuQueue(
    const p4::config::v1::P4NamedType& type_name,
    const google::protobuf::RepeatedPtrField<pdpi::IrMatchFieldReference>&
        references) {
  return type_name.name() == kP4UnknownQosQueueTypeName ||
         type_name.name() == kP4CpuQosQueueTypeName;
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
  return config.GetDisabledFullyQualifiedNames().contains(name);
}

bool IsModifiableTable(const FuzzerConfig& config, absl::string_view name) {
  return !config.GetNonModifiableTables().contains(name);
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

pins_test::P4rtPortId FuzzPort(absl::BitGen* gen, const FuzzerConfig& config) {
  return UniformFromSpan(gen, config.GetPorts());
}

inline int DivideRoundedUp(const unsigned int n, const unsigned int d) {
  if (n == 0 || d == 0) {
    return 0;
  }

  return (n - 1) / d + 1;
}

// Returns a copy of `references` with all non-match field references removed.
// This is done since it is assumed that match field and action references are
// independent an assumption that is enforced by `CheckReferenceAssumptions`
// when constructing `FuzzerConfig`.
absl::StatusOr<google::protobuf::RepeatedPtrField<IrTableReference>>
MatchReferenceInfo(
    const google::protobuf::RepeatedPtrField<IrTableReference>& references) {
  google::protobuf::RepeatedPtrField<IrTableReference> result;
  for (const IrTableReference& reference : references) {
    google::protobuf::RepeatedPtrField<IrTableReference::FieldReference>
        field_references;
    for (const auto& field_reference : reference.field_references()) {
      if (field_reference.source().has_match_field()) {
        *field_references.Add() = field_reference;
      }
    }
    if (!field_references.empty()) {
      IrTableReference table_reference;
      *table_reference.mutable_source_table() = reference.source_table();
      *table_reference.mutable_destination_table() =
          reference.destination_table();
      *table_reference.mutable_field_references() = std::move(field_references);
      result.Add(std::move(table_reference));
    }
  }
  return result;
}

// Returns a copy of `references` with all field references that do not contain
// `action_id` removed. This is done since it is assumed that match field and
// action references are independent, an assumption that is enforced by
// `CheckReferenceAssumptions` when constructing `FuzzerConfig`.
absl::StatusOr<google::protobuf::RepeatedPtrField<IrTableReference>>
ActionReferenceInfo(
    const google::protobuf::RepeatedPtrField<IrTableReference>& references,
    int action_id) {
  google::protobuf::RepeatedPtrField<IrTableReference> result;
  for (const IrTableReference& reference : references) {
    google::protobuf::RepeatedPtrField<IrTableReference::FieldReference>
        field_references;
    for (const auto& field_reference : reference.field_references()) {
      if (field_reference.source()
              .action_field()
              .p4_action_field()
              .action_id() == action_id) {
        *field_references.Add() = field_reference;
      }
    }
    if (!field_references.empty()) {
      IrTableReference table_reference;
      *table_reference.mutable_source_table() = reference.source_table();
      *table_reference.mutable_destination_table() =
          reference.destination_table();
      *table_reference.mutable_field_references() = std::move(field_references);
      result.Add(std::move(table_reference));
    }
  }
  return result;
}

// Creates a map from entry field to concrete value that is generated using
// `references`. For every table reference, a random entry is pulled from that
// table to produce concrete values. This implementation has assumptions that
// are enforced by `CheckReferenceAssumptions` when constructing `FuzzerConfig`.
absl::StatusOr<absl::flat_hash_map<std::string, std::string>>
CreateReferenceMapping(
    absl::BitGen* gen, const SwitchState& switch_state,
    const google::protobuf::RepeatedPtrField<IrTableReference>& references) {
  absl::flat_hash_map<std::string, std::string> reference_map;
  for (const IrTableReference& reference : references) {
    Entity referenced_entity;
    switch (reference.destination_table().table_case()) {
      case pdpi::IrTable::kP4Table: {
        if (reference.destination_table().p4_table().table_name() ==
                "router_interface_table" &&
            reference.source_table().p4_table().table_name() !=
                "neighbor_table") {
          // TODO: - Remove once a less "baked-in" way of masking
          // this is found. This is a mask that is consistent with
          // `CheckReferenceAssumptions`, which is used when creating the
          // `FuzzerConfig`.
          continue;
        }

        if (switch_state.IsTableEmpty(
                reference.destination_table().p4_table().table_id())) {
          return gutil::FailedPreconditionErrorBuilder()
                 << "Table with id "
                 << reference.destination_table().p4_table().table_id()
                 << " is empty. Cannot currently generate references to table.";
        }

        *referenced_entity.mutable_table_entry() = UniformValueFromMap(
            gen, switch_state.GetTableEntries(
                     reference.destination_table().p4_table().table_id()));
        break;
      }
      case pdpi::IrTable::kBuiltInTable: {
        if (reference.destination_table().built_in_table() !=
            pdpi::BUILT_IN_TABLE_MULTICAST_GROUP_TABLE) {
          return gutil::UnimplementedErrorBuilder()
                 << "Only built-in destination table of type "
                    "BUILT_IN_TABLE_MULTICAST_GROUP_TABLE is supported, got: "
                 << reference.DebugString();
        }

        if (switch_state.GetMulticastGroupEntries().empty()) {
          return gutil::FailedPreconditionErrorBuilder()
                 << "Multicast group table is empty. Cannot currently "
                    "generate references.";
        }
        *referenced_entity.mutable_packet_replication_engine_entry()
             ->mutable_multicast_group_entry() =
            UniformValueFromMap(gen, switch_state.GetMulticastGroupEntries());
        break;
      }
      default: {
        return gutil::InvalidArgumentErrorBuilder()
               << "Destination table type in reference info is not known: "
               << reference.DebugString();
      }
    }
    ASSIGN_OR_RETURN(
        absl::flat_hash_set<pdpi::ConcreteTableReference> concrete_references,
        pdpi::PossibleIncomingConcreteTableReferences(reference,
                                                      referenced_entity));
    for (const pdpi::ConcreteTableReference& concrete_reference :
         concrete_references) {
      for (const auto& field : concrete_reference.fields) {
        reference_map[field.source_field] = field.value;
      }
    }
  }
  return reference_map;
}

absl::Status MatchFieldReferenceOverride(absl::BitGen* gen,
                                         const FuzzerConfig& config,
                                         const SwitchState& switch_state,
                                         TableEntry& entry) {
  ASSIGN_OR_RETURN(auto table_def,
                   gutil::FindOrStatus(config.GetIrP4Info().tables_by_id(),
                                       entry.table_id()));

  // NOTE: The ability to fuzz references for actions and match fields
  // independently is based on an assumption enforced in
  // `CheckReferenceAssumptions` when constructing `FuzzerConfig`. Should
  // that assumption ever be removed, this code should be updated.
  ASSIGN_OR_RETURN(auto match_reference_info,
                   MatchReferenceInfo(table_def.outgoing_references()));
  absl::flat_hash_map<std::string, std::string> reference_map;
  ASSIGN_OR_RETURN(reference_map, CreateReferenceMapping(gen, switch_state,
                                                         match_reference_info));

  // Override match fields.
  for (auto& match : *entry.mutable_match()) {
    ASSIGN_OR_RETURN(
        auto match_field_info,
        gutil::FindOrStatus(table_def.match_fields_by_id(), match.field_id()));
    std::string match_field_name = match_field_info.match_field().name();

    if (auto it = reference_map.find(match_field_name);
        it != reference_map.end()) {
      // TODO: - Move to when creating a FuzzerConfig
      if (match_field_info.match_field().match_type() !=
              p4::config::v1::MatchField::EXACT &&
          match_field_info.match_field().match_type() !=
              p4::config::v1::MatchField::OPTIONAL) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Only match fields with type EXACT or OPTIONAL can have "
                  "references.";
      }
      match.mutable_exact()->set_value(it->second);
    }
  }

  return absl::OkStatus();
}

absl::Status ActionParamReferenceOverride(
    absl::BitGen* gen, const FuzzerConfig& config,
    const SwitchState& switch_state, const pdpi::IrTableDefinition& table_def,
    Action& action) {
  ASSIGN_OR_RETURN(auto action_def,
                   gutil::FindOrStatus(config.GetIrP4Info().actions_by_id(),
                                       action.action_id()));

  // NOTE: The ability to fuzz references for actions and match fields
  // independently is based on an assumption enforced in
  // `CheckReferenceAssumptions` when constructing `FuzzerConfig`. Should that
  // assumption ever be removed, this code should be updated.
  ASSIGN_OR_RETURN(auto action_reference_info,
                   ActionReferenceInfo(table_def.outgoing_references(),
                                       action_def.preamble().id()));
  absl::flat_hash_map<std::string, std::string> reference_map;
  ASSIGN_OR_RETURN(
      reference_map,
      CreateReferenceMapping(gen, switch_state, action_reference_info));

  // Override action params.
  for (auto& param : *action.mutable_params()) {
    ASSIGN_OR_RETURN(
        auto param_info,
        gutil::FindOrStatus(action_def.params_by_id(), param.param_id()));
    std::string param_name = param_info.param().name();

    if (auto it = reference_map.find(
            absl::StrCat(action_def.preamble().alias(), ".", param_name));
        it != reference_map.end()) {
      param.set_value(it->second);
    }
  }
  return absl::OkStatus();
}

absl::Status ReferenceOverride(absl::BitGen* gen, const FuzzerConfig& config,
                               const SwitchState& switch_state,
                               TableEntry& entry) {
  RETURN_IF_ERROR(
      MatchFieldReferenceOverride(gen, config, switch_state, entry));

  IrTableDefinition table_def =
      gutil::FindOrDie(config.GetIrP4Info().tables_by_id(), entry.table_id());
  switch (entry.action().type_case()) {
    case p4::v1::TableAction::kAction: {
      RETURN_IF_ERROR(ActionParamReferenceOverride(
          gen, config, switch_state, table_def,
          *entry.mutable_action()->mutable_action()));
      break;
    }
    case p4::v1::TableAction::kActionProfileActionSet: {
      for (auto& action_profile_action :
           *entry.mutable_action()
                ->mutable_action_profile_action_set()
                ->mutable_action_profile_actions()) {
        RETURN_IF_ERROR(ActionParamReferenceOverride(
            gen, config, switch_state, table_def,
            *action_profile_action.mutable_action()));
      }
      break;
    }
    default: {
      return gutil::InvalidArgumentErrorBuilder()
             << "Table action type not supported: "
             << gutil::PrintTextProto(entry.action());
    }
  }
  return absl::OkStatus();
}

// Returns a randomly generated `bits` long number in network byte order, stored
// in a `bytes` long string. Unused bits are set to 0.
std::string FuzzBits(absl::BitGen* gen, int bits, int bytes) {
  std::string data(bytes, 0);
  for (int i = 0; i < bytes; ++i)
    data[i] = absl::implicit_cast<char>(Uniform<uint8_t>(*gen));

  return SetUnusedBitsToZero(bits, std::move(data));
}

absl::StatusOr<p4::v1::ActionProfileAction> FuzzActionProfileAction(
    absl::BitGen* gen, const FuzzerConfig& config,
    const SwitchState& switch_state,
    const pdpi::IrTableDefinition& ir_table_info, int max_weight) {
  p4::v1::ActionProfileAction action;

  ASSIGN_OR_RETURN(
      *action.mutable_action(),
      FuzzAction(
          gen, config, switch_state,
          UniformFromSpan(gen, AllValidActions(config, ir_table_info)).action(),
          ir_table_info));

  action.set_weight(Uniform<int32_t>(*gen, 1, max_weight));
  action.set_watch_port(FuzzPort(gen, config).GetP4rtEncoding());

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
    const absl::flat_hash_set<EntityKey>& entity_keys_in_request,
    const AnnotatedUpdate& candidate_update) {
  // Mutated updates are never accidentally invalid (they should always be
  // invalid) so return early if update contains any mutations.
  if (!candidate_update.mutations().empty()) return false;

  const Entity& candidate_entity = candidate_update.pi().entity();
  // Checks for duplicates in current write request.
  if (auto candidate_entity_key = EntityKey::MakeEntityKey(candidate_entity);
      candidate_entity_key.ok() &&
      entity_keys_in_request.contains(*candidate_entity_key)) {
    return true;
  }
  // Checks that an insert does not insert an existing entry.
  if (candidate_update.pi().type() == p4::v1::Update_Type_INSERT &&
      // This entity is a table entry that exists.
      ((candidate_entity.has_table_entry() &&
        switch_state.GetTableEntry(candidate_entity.table_entry())
            .has_value()) ||
       // This entity is a multicast group entry that exists.
       (candidate_entity.packet_replication_engine_entry()
            .has_multicast_group_entry() &&
        switch_state
            .GetMulticastGroupEntry(
                candidate_entity.packet_replication_engine_entry()
                    .multicast_group_entry())
            .has_value()))) {
    return true;
  }

  const std::string& table_name =
      candidate_update.ir().entity().table_entry().table_name();
  // See if the update should be discarded because it is trying to insert into a
  // table that has a strict resource limit and cannot accommodate more inserts
  // than is already in the write request.
  if (candidate_update.ir().type() == p4::v1::Update_Type_INSERT &&
      config.GetTablesForWhichToNotExceedResourceGuarantees().contains(
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
    if (!switch_state.CanAccommodateInserts(
            candidate_update.pi().entity().table_entry().table_id(),
            num_inserts)) {
      return true;
    }
  }

  absl::StatusOr<bool> is_buggy_update =
      config.GetIsBuggyUpdateThatShouldBeSkipped()(config, candidate_update);
  if (!is_buggy_update.ok()) {
    DLOG(FATAL) << "Failed to determine if update is buggy. Update: "
                << gutil::PrintTextProto(candidate_update)
                << "\nStatus: " << is_buggy_update.status();
    return true;
  }
  return *is_buggy_update;
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

  for (auto& [key, table] : Ordered(config.GetIrP4Info().tables_by_id())) {
    if (table.role() == config.GetRole()) continue;
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

bool ModifiableTableExists(const FuzzerConfig& config,
                           const SwitchState& switch_state) {
  for (const IrTableDefinition& table : AllValidTablesForP4RtRole(config)) {
    // A table with no entries is not conisdered modifiable.
    if (!switch_state.IsTableEmpty(table.preamble().id()) &&
        IsModifiableTable(config, table.preamble().name())) {
      return true;
    }
  }
  return false;
}

// Randomly generates an update type.
Update::Type FuzzUpdateType(absl::BitGen* gen, const FuzzerConfig& config,
                            const SwitchState& state, bool is_multicast) {
  if (!is_multicast) {
    // The probability of inserting a entry is larger than the probability of
    // removing one, which means that eventually the switch fills up. 0.7 is a
    // nice number because it causes the switch to fill up quickly, but there is
    // still a good chance to get a couple of deletes in a row. If all tables
    // are empty, then we must use INSERT.
    if (absl::Bernoulli(*gen, 0.7) || state.AllP4TablesEmpty()) {
      return Update::INSERT;
    }

    // Equally split the rest between modify and delete. If it's not possible
    // to choose modify, delete will be selected.
    if (absl::Bernoulli(*gen, 0.5) && ModifiableTableExists(config, state)) {
      return Update::MODIFY;
    }

    return Update::DELETE;
  } else {
    // Same as non-multicast logic except multicast specific functions are used.
    if (absl::Bernoulli(*gen, 0.7) ||
        state.GetMulticastGroupEntries().empty()) {
      return Update::INSERT;
    }

    if (absl::Bernoulli(*gen, 0.5) &&
        IsModifiableTable(config, pdpi::GetMulticastGroupTableName())) {
      return Update::MODIFY;
    }

    return Update::DELETE;
  }
}

// Fuzzes `Replica` for a packet replication engine entry (multicast
// group/clone session). `packet_replication_engine_definition` provides
// outgoing references.
absl::StatusOr<Replica> FuzzReplica(absl::BitGen* gen,
                                    const FuzzerConfig& config,
                                    const SwitchState& switch_state,
                                    const pdpi::IrBuiltInTableDefinition&
                                        packet_replication_engine_definition) {
  Replica replica;

  // NOTE: The ability to fuzz references for actions and match fields
  // independently is based on an assumption enforced in
  // `CheckReferenceAssumptions` when constructing `FuzzerConfig`. Should that
  // assumption ever be removed, this code should be updated.
  absl::flat_hash_map<std::string, std::string> reference_map;
  ASSIGN_OR_RETURN(
      reference_map,
      CreateReferenceMapping(
          gen, switch_state,
          packet_replication_engine_definition.outgoing_references()));

  ASSIGN_OR_RETURN(
      std::string port_param,
      pdpi::IrBuiltInParameterToString(
          pdpi::IrBuiltInParameter::BUILT_IN_PARAMETER_REPLICA_PORT));
  if (auto it = reference_map.find(port_param); it != reference_map.end()) {
    replica.set_port(it->second);
  } else {
    replica.set_port(FuzzPort(gen, config).GetP4rtEncoding());
  }

  // Inherited from v1model, see `standard_metadata_t.egress_rid`.
  // https://github.com/p4lang/p4c/blob/main/p4include/v1model.p4
  constexpr int kReplicaInstanceBitwidth = 16;

  ASSIGN_OR_RETURN(
      std::string instance_param,
      pdpi::IrBuiltInParameterToString(
          pdpi::IrBuiltInParameter::BUILT_IN_PARAMETER_REPLICA_INSTANCE));
  if (auto it = reference_map.find(instance_param); it != reference_map.end()) {
    ASSIGN_OR_RETURN(
        auto instance,
        string_encodings::ByteStringToBitset<kReplicaInstanceBitwidth>(
            it->second));
    replica.set_instance(instance.to_ullong());
  } else {
    replica.set_instance(FuzzUint64(gen, kReplicaInstanceBitwidth));
  }

  return replica;
}

// Randomly changes the `multicast_group_entry` without affecting the key
// fields.
absl::Status FuzzNonKeyFields(absl::BitGen* gen, const FuzzerConfig& config,
                              const SwitchState& switch_state,
                              MulticastGroupEntry* multicast_group_entry) {
  multicast_group_entry->clear_replicas();
  // Fuzz 0-8 unique replicas
  // TODO: - Replace how iteration count is chosen with information
  // from p4 info or config once multicast resource limits are finalized and
  // modeled.
  int replica_fuzz_iterations = FuzzUint64(gen, /*bits=*/3);
  absl::flat_hash_set<std::pair<int, std::string>> unique_replicas;
  // Depending on references, the number of unique replicas can be capped so
  // replicas generated can be less than `replica_fuzz_iterations`.
  for (int i = 0; i < replica_fuzz_iterations; ++i) {
    // Generate replica.
    ASSIGN_OR_RETURN(Replica replica,
                     FuzzReplica(gen, config, switch_state,
                                 config.GetIrP4Info().built_in_tables().at(
                                     pdpi::GetMulticastGroupTableName())));

    // Within a given multicast entry, replicas must be unique.
    if (unique_replicas
            .insert(std::make_pair(replica.instance(), replica.port()))
            .second) {
      *multicast_group_entry->add_replicas() = std::move(replica);
    }
  }
  return absl::OkStatus();
}

// Randomly changes the table_entry, without affecting the key fields.
absl::Status FuzzNonKeyFields(absl::BitGen* gen, const FuzzerConfig& config,
                              const SwitchState& switch_state,
                              TableEntry* table_entry) {
  // With some probability, don't modify the element at all.
  if (absl::Bernoulli(*gen, 0.2)) return absl::OkStatus();

  if (absl::Bernoulli(*gen, 0.25)) {
    if (absl::Bernoulli(*gen, 0.5)) {
      // TODO: can't remove action at the moment, because
      // IsWellformedUpdate
      // will think the update is no longer well-formed.
    } else {
      ASSIGN_OR_RETURN(auto table_definition,
                       gutil::FindOrStatus(config.GetIrP4Info().tables_by_id(),
                                           table_entry->table_id()));
      // Try up to 3 times to create a new action.
      for (int i = 0; i < 3; ++i) {
        if (auto action =
                FuzzAction(gen, config, switch_state, table_definition);
            action.ok()) {
          *table_entry->mutable_action() = *action;
          break;
        }
      }
    }
  }

  // Remove or modify metadata.
  if (absl::Bernoulli(*gen, 0.25)) {
    if (absl::Bernoulli(*gen, 0.5)) {
      table_entry->clear_metadata();
    }
  }
  // TODO: also fuzz meters
  return absl::OkStatus();
}

// Randomly changes the entity, without affecting the key fields.
absl::Status FuzzNonKeyFields(absl::BitGen* gen, const FuzzerConfig& config,
                              const SwitchState& switch_state, Entity* entity) {
  // This function only supports table entries and multicast group entries.
  CHECK(entity->has_table_entry() ||  // Crash OK
        entity->packet_replication_engine_entry().has_multicast_group_entry());
  if (entity->has_table_entry()) {
    RETURN_IF_ERROR(FuzzNonKeyFields(gen, config, switch_state,
                                     entity->mutable_table_entry()));
  }
  if (entity->packet_replication_engine_entry().has_multicast_group_entry()) {
    RETURN_IF_ERROR(
        FuzzNonKeyFields(gen, config, switch_state,
                         entity->mutable_packet_replication_engine_entry()
                             ->mutable_multicast_group_entry()));
  }
  return absl::OkStatus();
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

std::vector<WeightedItem<uint32_t>> GenerateModifiableWeightedTableIds(
    const FuzzerConfig& config, const SwitchState& switch_state) {
  std::vector<WeightedItem<uint32_t>> modifiable_weighted_table_ids;
  for (const auto& weighted_table_id :
       GenerateNonEmptyWeightedTableIds(config, switch_state)) {
    std::string table_name = config.GetIrP4Info()
                                 .tables_by_id()
                                 .at(weighted_table_id.item)
                                 .preamble()
                                 .name();
    if (!IsModifiableTable(config, table_name)) continue;
    modifiable_weighted_table_ids.push_back(weighted_table_id);
  }
  return modifiable_weighted_table_ids;
}

// Uses the Entity type (and if table entry, its `table_id`) to fuzz a new
// Entity.
// Pre-requisites: Entity must be a table entry with a table id or a multicast
// group entry. All other fields will be ignored.
absl::Status FuzzValidEntity(absl::BitGen* gen, const FuzzerConfig& config,
                             const SwitchState& switch_state, Entity& entity) {
  CHECK((entity.has_table_entry() &&  // Crash OK
         entity.table_entry().table_id() != 0) ||
        entity.packet_replication_engine_entry().has_multicast_group_entry());

  if (entity.has_table_entry()) {
    ASSIGN_OR_RETURN(*entity.mutable_table_entry(),
                     FuzzValidTableEntry(gen, config, switch_state,
                                         entity.table_entry().table_id()));
  }
  if (entity.packet_replication_engine_entry().has_multicast_group_entry()) {
    ASSIGN_OR_RETURN(*entity.mutable_packet_replication_engine_entry()
                          ->mutable_multicast_group_entry(),
                     FuzzValidMulticastGroupEntry(gen, config, switch_state));
  }

  return absl::OkStatus();
}

// Randomly generates an INSERT, MODIFY or DELETE update. The update may be
// mutated (see go/p4-fuzzer-design for mutation types).
AnnotatedUpdate FuzzUpdate(absl::BitGen* gen, const FuzzerConfig& config,
                           const SwitchState& switch_state) {
  CHECK_GT(AllValidTablesForP4RtRole(config).size(), 0)  // Crash OK
      << "Cannot generate updates for program with no tables";

  Mutation mutation;
  bool do_mutate = absl::Bernoulli(*gen, config.GetMutateUpdateProbability());

  // Multicast updates do not support mutations yet.
  bool fuzz_multicast_update =
      !do_mutate &&
      absl::Bernoulli(*gen, config.GetFuzzMulticastGroupEntryProbability());

  std::vector<uint32_t> mutation_table_ids;

  if (do_mutate) {
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
        mutation_table_ids =
	    GetTableIdsWithValuePredicate(config, IsUnknownQosOrCpuQueue);
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

  Update::Type type = FuzzUpdateType(gen, config, switch_state,
                                     /*is_multicast=*/fuzz_multicast_update);
  Update update;
  update.set_type(type);
  Entity& entity = *update.mutable_entity();

  switch (type) {
    case Update::INSERT: {
      if (fuzz_multicast_update) {
        entity.mutable_packet_replication_engine_entry()
            ->mutable_multicast_group_entry();
      } else {
        if (do_mutate) {
          entity.mutable_table_entry()->set_table_id(
              UniformFromSpan(gen, mutation_table_ids));
        } else {
          entity.mutable_table_entry()->set_table_id(FuzzTableId(gen, config));
        }
      }

      // This might (with low probability) generate an entity that already
      // exists leading to a duplicate insert. This is fine since
      // `IsAccidentallyInvalidUpdate` will catch it and discard the update.
      if (!FuzzValidEntity(gen, config, switch_state, entity).ok()) {
        // Retry.
        return FuzzUpdate(gen, config, switch_state);
      }

      break;
    }
    case Update::MODIFY:
    case Update::DELETE: {
      if (fuzz_multicast_update) {
        *entity.mutable_packet_replication_engine_entry()
             ->mutable_multicast_group_entry() =
            UniformValueFromMap(gen, switch_state.GetMulticastGroupEntries());
      } else {
        const int table_id =
            type == Update::DELETE
                // Tables must be non-empty if the update is a delete.
                ? FuzzNonEmptyTableId(gen, config, switch_state)
                // Tables must be modifiable if the update is a modify.
                : FuzzModifiableTableId(gen, config, switch_state);
        // Within a single call of FuzzWriteRequest, this might delete the same
        // entry multiple times. This is fine since
        // `IsAccidentallyInvalidUpdate` will catch it and discard the update.
        *entity.mutable_table_entry() =
            UniformValueFromMap(gen, switch_state.GetTableEntries(table_id));
      }
      if (!FuzzNonKeyFields(gen, config, switch_state, &entity).ok()) {
        // Retry.
        return FuzzUpdate(gen, config, switch_state);
      }
      // TODO: After this we may need to apply the ModifyFuzzedX
      // functions to ensure that modified entities have their non-key fields
      // correctly modified.
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

    return GetAnnotatedUpdate(config.GetIrP4Info(), update,
                              /* mutations = */ {mutation});
  }

  return GetAnnotatedUpdate(config.GetIrP4Info(), update, /* mutations = */ {});
}

struct VariableWithReferences {
  std::string variable;
  ::google::protobuf::RepeatedPtrField<::pdpi::IrMatchFieldReference>
      references;
};

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

  for (auto& [key, table] : Ordered(config.GetIrP4Info().tables_by_id())) {
    // Tables with the wrong role can't be modified by the controller.
    if (table.role() != config.GetRole()) continue;
    // Tables without actions cannot have valid table entries.
    if (table.entry_actions().empty()) continue;
    // Skip deprecated, unused, and disallowed tables.
    if (pdpi::IsElementDeprecated(table.preamble().annotations()) ||
        table.is_unsupported() ||
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
        action.action().is_unsupported() ||
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
    const absl::StatusOr<std::string> fully_qualified_match_field =
        GetFullyQualifiedMatchFieldName(table, match_field_info);
    CHECK(fully_qualified_match_field.ok())  // Crash OK
        << "Failed to get fully qualified match field name for "
        << match_field_info.DebugString();

    if (pdpi::IsElementDeprecated(
            match_field_info.match_field().annotations()) ||
        match_field_info.is_unsupported() ||
        IsDisabledForFuzzing(config, *fully_qualified_match_field))
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
  CHECK(!switch_state.AllP4TablesEmpty())  // Crash OK
      << "state: " << switch_state.SwitchStateSummary();
  return DiscreteFromSpan(
      gen, GenerateNonEmptyWeightedTableIds(config, switch_state));
}

int FuzzModifiableTableId(absl::BitGen* gen, const FuzzerConfig& config,
                          const SwitchState& switch_state) {
  CHECK(ModifiableTableExists(config, switch_state))  // Crash OK
      << "state: " << switch_state.SwitchStateSummary();
  return DiscreteFromSpan(
      gen, GenerateModifiableWeightedTableIds(config, switch_state));
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

absl::StatusOr<std::string> FuzzBits(absl::BitGen* gen, int bits) {
  if (bits <= 0) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Bytestrings must have a non-zero positive length. Length "
           << bits << " was requested.";
  }
  return FuzzBits(gen, bits, DivideRoundedUp(bits, kBitsInByte));
}

absl::StatusOr<std::string> FuzzNonZeroBits(absl::BitGen* gen, int bits) {
  while (true) {
    ASSIGN_OR_RETURN(std::string result, FuzzBits(gen, bits));
    if (!pdpi::IsAllZeros(result)) return result;
  }
}

// Fuzzes a value, with special handling for ports and IDs.
absl::StatusOr<std::string> FuzzValue(
    absl::BitGen* gen, const FuzzerConfig& config,
    const SwitchState& switch_state,
    const p4::config::v1::P4NamedType& type_name, int bits) {
  // A port: pick any valid port randomly.
  if (IsPort(type_name)) {
    return FuzzPort(gen, config).GetP4rtEncoding();
  }

  // A qos queue or CPU queue: pick any valid qos queue randomly.
  if (IsUnknownQosOrCpuQueue(type_name)) {
    return UniformFromSpan(gen, config.GetQosQueues());
  }

  // Add proper support for Unicast and Multicast Qos
  // Queues.
  if (type_name.name() == kP4UnicastQosQueueTypeName) {
    // Hardcoded value that seems to work for now.
    return "0x6";
  }

  //  Add proper support for Unicast and Multicast Qos
  // Queues.
  if (type_name.name() == kP4MulticastQosQueueTypeName) {
    // Hardcoded value that seems to work for now.
    return "0xa";
  }

  // A neighbor ID (not referring to anything): Pick a random IPv6 address.
  if (IsNeighbor(type_name)) {
    std::bitset<128> ipv6_bits;
    for (int i = 0; i < 128; ++i) {
      ipv6_bits.set(i, absl::Bernoulli(*gen, 0.5));
    }
    return netaddr::Ipv6Address::OfBitset(ipv6_bits).ToString();
  }

  // A string ID (not referring to anything): Pick a fresh random ID.
  if (bits == 0) {
    return FuzzRandomId(gen);
  }

  // Some other value: Normally fuzz bits randomly.
  return FuzzBits(gen, bits);
}

uint64_t FuzzUint64(absl::BitGen* gen, int bits) {
  return BitsToUint64(FuzzBits(gen, bits, sizeof(uint64_t)));
}

absl::StatusOr<p4::v1::FieldMatch> FuzzTernaryFieldMatch(
    absl::BitGen* gen, const FuzzerConfig& config, int bits) {
  ASSIGN_OR_RETURN(std::string mask, FuzzNonZeroBits(gen, bits));
  ASSIGN_OR_RETURN(std::string value, FuzzBits(gen, bits));

  // If a mask bit is 0, the corresponding value bit also has to be 0.
  value = pdpi::Intersection(value, mask).value();

  p4::v1::FieldMatch match;
  match.mutable_ternary()->set_mask(mask);
  match.mutable_ternary()->set_value(value);
  return match;
}

absl::StatusOr<p4::v1::FieldMatch> FuzzLpmFieldMatch(
    absl::BitGen* gen, const FuzzerConfig& config,
    const SwitchState& switch_state, int bits) {
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

  ASSIGN_OR_RETURN(std::string value, FuzzBits(gen, bits));

  p4::v1::FieldMatch match;
  match.mutable_lpm()->set_prefix_len(prefix_len);
  // We need a value that has prefix_len many random bits, followed by zeros.
  match.mutable_lpm()->set_value(
      ZeroNLeastSignificantBits(bits - prefix_len, value));
  return match;
}

absl::StatusOr<p4::v1::FieldMatch> FuzzExactFieldMatch(
    absl::BitGen* gen, const FuzzerConfig& config,
    const SwitchState& switch_state,
    const pdpi::IrMatchFieldDefinition& ir_match_field_info) {
  p4::v1::FieldMatch match;
  p4::config::v1::MatchField field = ir_match_field_info.match_field();
  // Note that exact messages have to be provided, even if the value is 0.
  ASSIGN_OR_RETURN(std::string value,
                   FuzzValue(gen, config, switch_state, field.type_name(),
                             field.bitwidth()));

  match.mutable_exact()->set_value(value);
  return match;
}

absl::StatusOr<p4::v1::FieldMatch> FuzzOptionalFieldMatch(
    absl::BitGen* gen, const FuzzerConfig& config,
    const SwitchState& switch_state,
    const pdpi::IrMatchFieldDefinition& ir_match_field_info) {
  p4::v1::FieldMatch match;
  p4::config::v1::MatchField field = ir_match_field_info.match_field();
  ASSIGN_OR_RETURN(std::string value,
                   FuzzValue(gen, config, switch_state, field.type_name(),
                             field.bitwidth()));
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
      ASSIGN_OR_RETURN(match, FuzzTernaryFieldMatch(
                                  gen, config, match_field_info.bitwidth()));
      break;
    }
    case p4::config::v1::MatchField::LPM: {
      ASSIGN_OR_RETURN(match, FuzzLpmFieldMatch(gen, config, switch_state,
                                                match_field_info.bitwidth()));
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
    const pdpi::IrActionDefinition& ir_action_info,
    const pdpi::IrTableDefinition& ir_table_info) {
  p4::v1::Action action;
  action.set_action_id(ir_action_info.preamble().id());

  for (auto& [param_name, ir_param] :
       Ordered(ir_action_info.params_by_name())) {
    p4::v1::Action::Param* param = action.add_params();
    param->set_param_id(ir_param.param().id());
    ASSIGN_OR_RETURN(
        std::string value,
        FuzzValue(gen, config, switch_state, ir_param.param().type_name(),
                  ir_param.param().bitwidth()),
        _.SetPrepend() << "while fuzzing parameter '" << param_name
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
      GetActionProfile(config.GetIrP4Info(), ir_table_info.preamble().id()));

  if (action_profile.has_sum_of_members()) {
    int max_number_of_actions = action_profile.max_group_size() != 0
                                    ? action_profile.max_group_size()
                                    : kActionProfileActionSetMaxCardinality;
    int number_of_actions = Uniform<int>(
        absl::IntervalClosedClosed, *gen,
        config.GetNoEmptyActionProfileGroups() ? 1 : 0, max_number_of_actions);

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
    int number_of_actions = Uniform<int>(
        absl::IntervalClosedClosed, *gen,
        config.GetNoEmptyActionProfileGroups() ? 1 : 0,
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
                .action(),
            table_definition));
  } else {
    ASSIGN_OR_RETURN(*result.mutable_action_profile_action_set(),
                     FuzzActionProfileActionSet(gen, config, switch_state,
                                                table_definition));
  }
  return result;
}

absl::StatusOr<p4::v1::MulticastGroupEntry> FuzzValidMulticastGroupEntry(
    absl::BitGen* gen, const FuzzerConfig& config,
    const SwitchState& switch_state) {
  MulticastGroupEntry entry;

  // Inherited from v1model , see `standard_metadata_t.mcast_grp`.
  // https://github.com/p4lang/p4c/blob/main/p4include/v1model.p4
  constexpr int kMulticastGroupIdWidth = 16;

  // NOTE: References from `multicast_group_id` are not implemented since there
  // is no current use case, but an implementation should exist for general
  // purposes.
  while (entry.multicast_group_id() == 0) {
    entry.set_multicast_group_id(FuzzUint64(gen, kMulticastGroupIdWidth));
  }

  // Fills in replicas randomly.
  RETURN_IF_ERROR(FuzzNonKeyFields(gen, config, switch_state, &entry));

  return entry;
};

// TODO: Optional fields with @refers_to will not be properly
// fuzzed if they refer to fields that currently have no existing entry.
// Fuzzing fails for this, but it should simply omit the optional. Thankfully,
// this situation is not currently in use.
absl::StatusOr<TableEntry> FuzzValidTableEntry(
    absl::BitGen* gen, const FuzzerConfig& config,
    const SwitchState& switch_state,
    const pdpi::IrTableDefinition& ir_table_info,
    std::optional<absl::string_view> additional_constraint) {
  // If the table uses p4-constraints, then we call out to a different
  // generation function that uses an SMT solver.
  if (UsesP4Constraints(ir_table_info, config) &&
      !config.GetIgnoreConstraintsOnTables().contains(
          ir_table_info.preamble().name())) {
    ASSIGN_OR_RETURN(auto entry, FuzzValidConstrainedTableEntry(
                                     config, switch_state, ir_table_info, *gen,
                                     additional_constraint));
    RETURN_IF_ERROR(ReferenceOverride(gen, config, switch_state, entry));
    return entry;
  }

  TableEntry table_entry;
  table_entry.set_table_id(ir_table_info.preamble().id());

  for (const pdpi::IrMatchFieldDefinition& match_field_info :
       AllValidMatchFields(config, ir_table_info)) {
    std::string match_field_name = match_field_info.match_field().name();

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
        absl::Bernoulli(*gen, config.GetMatchFieldWildcardProbability())) {
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

  if (ir_table_info.requires_priority()) {
    uint64_t priority;
    do {
      priority = FuzzUint64(gen, /*bits=*/16);
    } while (priority == 0);
    table_entry.set_priority(priority);
  }

  // TODO: Fuzz default actions.
  // TODO: Fuzz meters and counters.

  RETURN_IF_ERROR(ReferenceOverride(gen, config, switch_state, table_entry));

  return table_entry;
}

absl::StatusOr<TableEntry> FuzzValidTableEntry(
    absl::BitGen* gen, const FuzzerConfig& config,
    const SwitchState& switch_state, const uint32_t table_id,
    std::optional<absl::string_view> additional_constraint) {
  return FuzzValidTableEntry(
      gen, config, switch_state,
      gutil::FindOrDie(config.GetIrP4Info().tables_by_id(), table_id),
      additional_constraint);
}

AnnotatedWriteRequest FuzzWriteRequest(absl::BitGen* gen,
                                       const FuzzerConfig& config,
                                       const SwitchState& switch_state,
                                       absl::optional<int> max_batch_size) {
  AnnotatedWriteRequest request;
  absl::flat_hash_set<EntityKey> entity_keys_in_request;

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
                                       entity_keys_in_request, update) &&
           update_attempts < 10000) {
      update = FuzzUpdate(gen, config, switch_state);
      update_attempts++;
    }
    if (auto update_entity_key = EntityKey::MakeEntityKey(update.pi().entity());
        update_entity_key.ok() &&
        !IsAccidentallyInvalidUpdate(config, switch_state, request,
                                     entity_keys_in_request, update)) {
      *request.add_updates() = update;
      entity_keys_in_request.insert(*update_entity_key);
    }
  }

  return request;
}

absl::Status ModifyEntity(absl::BitGen* gen, const FuzzerConfig& config,
                          const SwitchState& switch_state,
                          p4::v1::Entity& entity) {
  return FuzzNonKeyFields(gen, config, switch_state, &entity);
}

}  // namespace p4_fuzzer
