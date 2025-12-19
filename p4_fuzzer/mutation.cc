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
#include "p4_fuzzer/mutation.h"

#include "absl/algorithm/container.h"
#include "absl/status/status.h"
#include "gutil/collections.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_fuzzer/fuzz_util.h"
#include "p4_fuzzer/fuzzer_config.h"
#include "p4_pdpi/internal/ordered_map.h"

namespace p4_fuzzer {

using ::absl::BitGen;
using ::absl::Uniform;
using ::p4::v1::TableEntry;

namespace {

// Returns a uniformly random ID that is not from a given list.
uint32_t UniformNotFromList(BitGen* gen, const std::vector<uint32_t>& list) {
  uint32_t choice;

  do {
    choice = Uniform<uint32_t>(*gen);
  } while (absl::c_find(list, choice) != list.end());

  return choice;
}

// Returns the list of all table IDs in the underlying P4 program.
const std::vector<uint32_t> AllTableIds(const FuzzerConfig& config) {
  std::vector<uint32_t> table_ids;

  for (auto& [table_id, table_def] :
       Ordered(config.GetIrP4Info().tables_by_id())) {
    table_ids.push_back(table_id);
  }

  return table_ids;
}

// Returns the list of all action IDs in the underlying P4 program.
const std::vector<uint32_t> AllActionIds(const FuzzerConfig& config) {
  std::vector<uint32_t> action_ids;

  for (auto& [action_id, action_def] :
       Ordered(config.GetIrP4Info().actions_by_id())) {
    action_ids.push_back(action_id);
  }

  return action_ids;
}

// Returns the list of all match field IDs in the underlying P4 program for
// table with id table_id.
const std::vector<uint32_t> AllMatchFieldIds(const FuzzerConfig& config,
                                             const uint32_t table_id) {
  std::vector<uint32_t> match_ids;

  for (auto& [match_id, match_def] :
       Ordered(gutil::FindOrDie(config.GetIrP4Info().tables_by_id(), table_id)
                   .match_fields_by_id())) {
    match_ids.push_back(match_id);
  }

  return match_ids;
}

}  // namespace

absl::Status MutateInvalidMatchFieldId(BitGen* gen, TableEntry* entry,
                                       const FuzzerConfig& config) {
  if (entry->match_size() == 0) {
    return absl::InvalidArgumentError("TableEntry has no match fields to fuzz");
  }

  auto table_ids = AllTableIds(config);

  if (absl::c_find(table_ids, entry->table_id()) == table_ids.end()) {
    return absl::InvalidArgumentError(
        "Cannot fuzz matches on invalid table id (it was probably fuzzed)");
  }

  int match_to_fuzz = Uniform<int>(*gen, 0, entry->match_size());
  entry->mutable_match(match_to_fuzz)
      ->set_field_id(
          UniformNotFromList(gen, AllMatchFieldIds(config, entry->table_id())));

  return absl::OkStatus();
}

absl::Status MutateMissingMandatoryMatchField(BitGen* gen, TableEntry* entry) {
  std::vector<int> mandatory_matches;

  int i = 0;
  for (const auto& match : entry->match()) {
    if (match.field_match_type_case() == p4::v1::FieldMatch::kExact) {
      mandatory_matches.push_back(i);
    }

    ++i;
  }

  if (mandatory_matches.empty()) {
    return absl::InvalidArgumentError(
        "Table entry has no mandatory match fields to remove");
  }

  entry->mutable_match()->erase(
      entry->mutable_match()->begin() +
      mandatory_matches[Uniform<int>(*gen, 0, mandatory_matches.size())]);

  return absl::OkStatus();
}

absl::Status MutateDuplicateMatchField(BitGen* gen, TableEntry* entry) {
  if (entry->match_size() == 0) {
    return absl::InvalidArgumentError(
        "TableEntry has no match fields to duplicate");
  }

  *entry->add_match() =
      entry->match(Uniform<int>(*gen, 0, entry->match_size()));

  return absl::OkStatus();
}

void MutateInvalidTableId(BitGen* gen, TableEntry* entry,
                          const FuzzerConfig& config) {
  entry->set_table_id(UniformNotFromList(gen, AllTableIds(config)));
}

void MutateInvalidActionId(BitGen* gen, TableEntry* entry,
                           const FuzzerConfig& config) {
  auto action = entry->mutable_action();

  switch (action->type_case()) {
    case p4::v1::TableAction::kAction:
      action->mutable_action()->set_action_id(
          UniformNotFromList(gen, AllActionIds(config)));
      break;
    case p4::v1::TableAction::kActionProfileActionSet: {
      auto* action_set = action->mutable_action_profile_action_set();
      const int num_actions = action_set->action_profile_actions_size();
      if (num_actions == 0) return;
      const int action_to_fuzz = Uniform<int>(*gen, 0, num_actions);
      auto* action_profile_action =
          action_set->mutable_action_profile_actions(action_to_fuzz);
      action_profile_action->mutable_action()->set_action_id(
          UniformNotFromList(gen, AllActionIds(config)));
    }

    break;
    default:
      LOG(FATAL) << "Only single action table entries or table entries that "
                    "use one one shot action selector programming supported.";
  }
}

absl::Status MutateInvalidTableImplementation(BitGen* gen, TableEntry* entry,
                                              const FuzzerConfig& config,
                                              const SwitchState& switch_state) {
  auto table_ids = AllTableIds(config);

  if (absl::c_find(table_ids, entry->table_id()) == table_ids.end()) {
    return absl::InvalidArgumentError(
        "Cannot fuzz matches on invalid table id (it was probably fuzzed)");
  }

  pdpi::IrTableDefinition ir_table_info =
      gutil::FindOrDie(config.GetIrP4Info().tables_by_id(), entry->table_id());

  switch (entry->action().type_case()) {
    case p4::v1::TableAction::kActionProfileActionSet: {
      ASSIGN_OR_RETURN(
          *entry->mutable_action()->mutable_action(),
          FuzzAction(
              gen, config, switch_state,
              UniformFromSpan(gen, AllValidActions(config, ir_table_info))
                  .action(),
              ir_table_info));
      break;
    }

    case p4::v1::TableAction::kAction: {
      ASSIGN_OR_RETURN(
          *entry->mutable_action()->mutable_action_profile_action_set(),
          FuzzActionProfileActionSet(gen, config, switch_state, ir_table_info));
      break;
    }

    default:
      return absl::InvalidArgumentError(
          "Only single action tables or one shot action selector programming "
          "tables supported.");
  }

  return absl::OkStatus();
}

absl::Status MutateInvalidActionSelectorWeight(BitGen* gen,
                                               p4::v1::TableEntry* entry,
                                               const FuzzerConfig& config) {
  auto action = entry->mutable_action();

  if (action->type_case() != p4::v1::TableAction::kActionProfileActionSet) {
    return absl::InvalidArgumentError(
        "INVALID_ACTION_SELECTOR_WEIGHT mutation only works on tables that use "
        "one shot action selector programming.");
  }

  auto action_set = action->mutable_action_profile_action_set();

  if (action_set->action_profile_actions_size() == 0) {
    return absl::OkStatus();
  }

  int action_to_fuzz =
      Uniform<int>(*gen, 0, action_set->action_profile_actions_size());
  auto action_profile_action =
      action_set->mutable_action_profile_actions(action_to_fuzz);

  ASSIGN_OR_RETURN(auto action_profile,
                   GetActionProfile(config.GetIrP4Info(), entry->table_id()));

  if (absl::Bernoulli(*gen, 0.5)) {
    action_profile_action->set_weight(0);
  } else {
    action_profile_action->set_weight(
        absl::Uniform<int32_t>(*gen, -1 * action_profile.max_group_size(), 0));
  }

  return absl::OkStatus();
}

absl::Status MutateDuplicateInsert(absl::BitGen* gen, p4::v1::Update* update,
                                   const FuzzerConfig& config,
                                   const SwitchState& switch_state) {
  if (switch_state.AllP4TablesEmpty()) {
    return absl::InvalidArgumentError(
        "Cannot do a duplicate insert when there are no installed entries");
  }

  const int table_id = FuzzNonEmptyTableId(gen, config, switch_state);
  update->set_type(p4::v1::Update::INSERT);
  *update->mutable_entity()->mutable_table_entry() =
      UniformValueFromMap(gen, switch_state.GetTableEntries(table_id));

  return absl::OkStatus();
}

absl::Status MutateNonexistingModifyDelete(absl::BitGen* gen,
                                           p4::v1::Update* update,
                                           const FuzzerConfig& config,
                                           const SwitchState& switch_state,
                                           p4::v1::Update_Type type) {
  const int table_id = FuzzTableId(gen, config);

  ASSIGN_OR_RETURN(p4::v1::TableEntry entry,
                   FuzzValidTableEntry(gen, config, switch_state, table_id));
  if (switch_state.GetTableEntry(entry) != absl::nullopt) {
    return absl::InternalError("Generated entry that exists in switch");
  }

  *update->mutable_entity()->mutable_table_entry() = entry;
  update->set_type(type);

  return absl::OkStatus();
}

absl::Status MutateInvalidValue(absl::BitGen* gen, p4::v1::Update* update,
                                const FuzzerConfig& config,
                                const SwitchState& switch_state,
                                P4ValuePredicate predicate) {
  std::string invalid_value = FuzzRandomId(gen);

  // Try to find a match field.
  auto* table_entry = update->mutable_entity()->mutable_table_entry();
  ASSIGN_OR_RETURN(auto table_definition,
                   gutil::FindOrStatus(config.GetIrP4Info().tables_by_id(),
                                       table_entry->table_id()));
  for (auto& match : *table_entry->mutable_match()) {
    ASSIGN_OR_RETURN(auto match_definition,
                     gutil::FindOrStatus(table_definition.match_fields_by_id(),
                                         match.field_id()));
    if (predicate(match_definition.match_field().type_name(),
                  match_definition.references())) {
      switch (match.field_match_type_case()) {
        case p4::v1::FieldMatch::FieldMatchTypeCase::kExact:
          match.mutable_exact()->set_value(invalid_value);
          return absl::OkStatus();
          break;

        case p4::v1::FieldMatch::FieldMatchTypeCase::kOptional:
          match.mutable_optional()->set_value(invalid_value);
          return absl::OkStatus();
        default:
          return absl::InternalError(
              "String fields should be exact or optional, cannot make it more "
              "invalid.");
      }
    }
  }

  // Collect all actions.
  std::vector<p4::v1::Action*> actions;
  switch (table_entry->action().type_case()) {
    case p4::v1::TableAction::kAction:
      actions.push_back(table_entry->mutable_action()->mutable_action());
      break;

    case p4::v1::TableAction::kActionProfileActionSet:
      for (auto& action : *table_entry->mutable_action()
                               ->mutable_action_profile_action_set()
                               ->mutable_action_profile_actions()) {
        actions.push_back(action.mutable_action());
      }
      break;

    default:
      break;
  }

  // Try to find an action parameter.
  for (p4::v1::Action* action : actions) {
    ASSIGN_OR_RETURN(const auto& action_definition,
                     gutil::FindOrStatus(config.GetIrP4Info().actions_by_id(),
                                         action->action_id()));
    for (auto& param : *action->mutable_params()) {
      ASSIGN_OR_RETURN(const auto& param_definition,
                       gutil::FindOrStatus(action_definition.params_by_id(),
                                           param.param_id()));
      if (predicate(param_definition.param().type_name(),
                    param_definition.references())) {
        param.set_value(invalid_value);
        return absl::OkStatus();
      }
    }
  }

  return absl::InternalError(
      "The table entry does not have a port, cannot make it invalid.");
}

absl::Status MutateUpdate(BitGen* gen, const FuzzerConfig& config,
                          p4::v1::Update* update,
                          const SwitchState& switch_state,
                          const Mutation& mutation) {
  TableEntry* entry = update->mutable_entity()->mutable_table_entry();

  switch (mutation) {
    case Mutation::INVALID_TABLE_ID:
      MutateInvalidTableId(gen, entry, config);
      return absl::OkStatus();

    case Mutation::INVALID_ACTION_ID:
      MutateInvalidActionId(gen, entry, config);
      return absl::OkStatus();

    case Mutation::INVALID_MATCH_FIELD_ID:
      return MutateInvalidMatchFieldId(gen, entry, config);

    case Mutation::MISSING_MANDATORY_MATCH_FIELD:
      return MutateMissingMandatoryMatchField(gen, entry);

    case Mutation::DUPLICATE_MATCH_FIELD:
      return MutateDuplicateMatchField(gen, entry);

    case Mutation::INVALID_TABLE_IMPLEMENTATION:
      return MutateInvalidTableImplementation(gen, entry, config, switch_state);

    case Mutation::INVALID_ACTION_SELECTOR_WEIGHT:
      return MutateInvalidActionSelectorWeight(gen, entry, config);

    case Mutation::DUPLICATE_INSERT:
      return MutateDuplicateInsert(gen, update, config, switch_state);

    case Mutation::NONEXISTING_DELETE:
      return MutateNonexistingModifyDelete(gen, update, config, switch_state,
                                           p4::v1::Update::DELETE);

    case Mutation::NONEXISTING_MODIFY:
      return MutateNonexistingModifyDelete(gen, update, config, switch_state,
                                           p4::v1::Update::MODIFY);

    case Mutation::INVALID_PORT:
      return MutateInvalidValue(gen, update, config, switch_state, IsPort);

    case Mutation::INVALID_QOS_QUEUE:
      return MutateInvalidValue(gen, update, config, switch_state,
                                IsUnknownQosOrCpuQueue);

    case Mutation::INVALID_NEIGHBOR_ID:
      return MutateInvalidValue(gen, update, config, switch_state, IsNeighbor);

    case Mutation::INVALID_REFERRING_ID:
      return MutateInvalidValue(gen, update, config, switch_state, IsReferring);

    case Mutation::DIFFERENT_ROLE:
      // We already picked the right table earlier on, so nothing to do here.
      return absl::OkStatus();

    default:
      LOG(FATAL) << "Unsupported mutation type";
  }

  return absl::InternalError("Control flow should have never reached here.");
}

}  // namespace p4_fuzzer
