#include "p4_fuzzer/mutation.h"

// #include "third_party/libprotobuf_mutator/src/mutator.h"
#include "absl/algorithm/container.h"
#include "gutil/collections.h"
#include "p4_fuzzer/fuzz_util.h"

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
const std::vector<uint32_t> AllTableIds(const pdpi::IrP4Info& ir_p4_info) {
  std::vector<uint32_t> table_ids;

  for (auto& [table_id, table_def] : ir_p4_info.tables_by_id()) {
    table_ids.push_back(table_id);
  }

  return table_ids;
}

// Returns the list of all action IDs in the underlying P4 program.
const std::vector<uint32_t> AllActionIds(const pdpi::IrP4Info& ir_p4_info) {
  std::vector<uint32_t> action_ids;

  for (auto& [action_id, action_def] : ir_p4_info.actions_by_id()) {
    action_ids.push_back(action_id);
  }

  return action_ids;
}

// Returns the list of all match field IDs in the underlying P4 program for
// table with id table_id.
const std::vector<uint32_t> AllMatchFieldIds(const pdpi::IrP4Info& ir_p4_info,
                                             const uint32_t table_id) {
  std::vector<uint32_t> match_ids;

  for (auto& [match_id, match_def] :
       gutil::FindOrDie(ir_p4_info.tables_by_id(), table_id)
           .match_fields_by_id()) {
    match_ids.push_back(match_id);
  }

  return match_ids;
}

// Max size hint for lib protobuf mutator's Mutate function.
const int32_t kProtobufMutatorMaxByteSize = 200;

}  // namespace

void MutateInvalidGeneric(TableEntry* entry) {
  // TODO: mutator is not a visible class in google3.
  // static protobuf_mutator::Mutator mutator;
  // mutator.Mutate(entry, kProtobufMutatorMaxByteSize);
}

absl::Status MutateInvalidMatchFieldId(BitGen* gen, TableEntry* entry,
                                       const pdpi::IrP4Info& ir_p4_info) {
  if (entry->match_size() == 0) {
    return absl::InvalidArgumentError("TableEntry has no match fields to fuzz");
  }

  auto table_ids = AllTableIds(ir_p4_info);

  if (absl::c_find(table_ids, entry->table_id()) == table_ids.end()) {
    return absl::InvalidArgumentError(
        "Cannot fuzz matches on invalid table id (it was probably fuzzed)");
  }

  int match_to_fuzz = Uniform<int>(*gen, 0, entry->match_size());
  entry->mutable_match(match_to_fuzz)
      ->set_field_id(UniformNotFromList(
          gen, AllMatchFieldIds(ir_p4_info, entry->table_id())));

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
                          const pdpi::IrP4Info& ir_p4_info) {
  entry->set_table_id(UniformNotFromList(gen, AllTableIds(ir_p4_info)));
}

void MutateInvalidActionId(BitGen* gen, TableEntry* entry,
                           const pdpi::IrP4Info& ir_p4_info) {
  auto action = entry->mutable_action();

  switch (action->type_case()) {
    case p4::v1::TableAction::kAction:
      action->mutable_action()->set_action_id(
          UniformNotFromList(gen, AllActionIds(ir_p4_info)));
      break;
    case p4::v1::TableAction::kActionProfileActionSet: {
      auto* action_set = action->mutable_action_profile_action_set();
      const int num_actions = action_set->action_profile_actions_size();
      if (num_actions == 0) return;
      const int action_to_fuzz = Uniform<int>(*gen, 0, num_actions);
      auto* action_profile_action =
          action_set->mutable_action_profile_actions(action_to_fuzz);
      action_profile_action->mutable_action()->set_action_id(
          UniformNotFromList(gen, AllActionIds(ir_p4_info)));
    }

    break;
    default:
      LOG(FATAL) << "Only single action table entries or table entries that "
                    "use one one shot action selector programming supported.";
  }
}

absl::Status MutateInvalidTableImplementation(
    BitGen* gen, TableEntry* entry, const pdpi::IrP4Info& ir_p4_info) {
  auto table_ids = AllTableIds(ir_p4_info);

  if (absl::c_find(table_ids, entry->table_id()) == table_ids.end()) {
    return absl::InvalidArgumentError(
        "Cannot fuzz matches on invalid table id (it was probably fuzzed)");
  }

  pdpi::IrTableDefinition ir_table_info =
      gutil::FindOrDie(ir_p4_info.tables_by_id(), entry->table_id());

  switch (entry->action().type_case()) {
    case p4::v1::TableAction::kActionProfileActionSet: {
      *entry->mutable_action()->mutable_action() = FuzzAction(
          gen, ChooseNonDefaultActionRef(gen, ir_table_info).action());
      break;
    }

    case p4::v1::TableAction::kAction: {
      *entry->mutable_action()->mutable_action_profile_action_set() =
          FuzzActionProfileActionSet(gen, ir_p4_info, ir_table_info);
      break;
    }

    default:
      return absl::InvalidArgumentError(
          "Only single action tables or one shot action selector programming "
          "tables supported.");
  }

  return absl::OkStatus();
}

absl::Status MutateInvalidActionSelectorWeight(
    BitGen* gen, p4::v1::TableEntry* entry, const pdpi::IrP4Info& ir_p4_info) {
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

  if (absl::Bernoulli(*gen, 0.5)) {
    action_profile_action->set_weight(0);
  } else {
    action_profile_action->set_weight(
        absl::Uniform<int32_t>(*gen, -1 * kActionProfileActionMaxWeight, 0));
  }

  return absl::OkStatus();
}

absl::Status MutateDuplicateInsert(absl::BitGen* gen, p4::v1::Update* update,
                                   const pdpi::IrP4Info& ir_p4_info,
                                   const SwitchState& switch_state) {
  std::vector<TableEntry> entries;

  for (auto id : switch_state.AllTableIds()) {
    std::vector<TableEntry> entries_from_table =
        switch_state.GetTableEntries(id);
    entries.insert(entries.end(), entries_from_table.begin(),
                   entries_from_table.end());
  }

  if (entries.empty()) {
    return absl::InvalidArgumentError(
        "Cannot do a duplicate insert when there are no installed entries");
  }

  update->set_type(p4::v1::Update::INSERT);
  *update->mutable_entity()->mutable_table_entry() =
      UniformFromVector(gen, entries);

  return absl::OkStatus();
}

absl::Status MutateNonexistingDelete(absl::BitGen* gen, p4::v1::Update* update,
                                     const pdpi::IrP4Info& ir_p4_info,
                                     const SwitchState& switch_state) {
  const int table_id = FuzzTableId(gen, switch_state);

  p4::v1::TableEntry entry = FuzzValidTableEntry(gen, ir_p4_info, table_id);
  if (switch_state.GetTableEntry(entry) != absl::nullopt) {
    return absl::InternalError("Generated entry that exists in switch");
  }

  *update->mutable_entity()->mutable_table_entry() = entry;
  update->set_type(p4::v1::Update::DELETE);

  return absl::OkStatus();
}

absl::Status MutateUpdate(BitGen* gen, p4::v1::Update* update,
                          const pdpi::IrP4Info& ir_p4_info,
                          const SwitchState& switch_state,
                          const Mutation& mutation) {
  TableEntry* entry = update->mutable_entity()->mutable_table_entry();

  switch (mutation) {
    case Mutation::INVALID_TABLE_ID:
      MutateInvalidTableId(gen, entry, ir_p4_info);
      return absl::OkStatus();

    case Mutation::INVALID_ACTION_ID:
      MutateInvalidActionId(gen, entry, ir_p4_info);
      return absl::OkStatus();

    case Mutation::INVALID_MATCH_FIELD_ID:
      return MutateInvalidMatchFieldId(gen, entry, ir_p4_info);

    case Mutation::MISSING_MANDATORY_MATCH_FIELD:
      return MutateMissingMandatoryMatchField(gen, entry);

    case Mutation::DUPLICATE_MATCH_FIELD:
      return MutateDuplicateMatchField(gen, entry);

    case Mutation::INVALID_GENERIC:
      MutateInvalidGeneric(entry);
      return absl::OkStatus();

    case Mutation::INVALID_TABLE_IMPLEMENTATION:
      return MutateInvalidTableImplementation(gen, entry, ir_p4_info);

    case Mutation::INVALID_ACTION_SELECTOR_WEIGHT:
      return MutateInvalidActionSelectorWeight(gen, entry, ir_p4_info);

    case Mutation::DUPLICATE_INSERT:
      return MutateDuplicateInsert(gen, update, ir_p4_info, switch_state);

    case Mutation::NONEXISTING_DELETE:
      return MutateNonexistingDelete(gen, update, ir_p4_info, switch_state);

    default:
      LOG(FATAL) << "Unsupported mutation type";
  }

  return absl::InternalError("Control flow should have never reached here.");
}

}  // namespace p4_fuzzer
