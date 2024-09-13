#include "p4_fuzzer/fuzz_util.h"

#include "absl/algorithm/container.h"
#include "absl/base/casts.h"
#include "absl/base/internal/endian.h"
#include "gutil/collections.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_fuzzer/annotation_util.h"
#include "p4_fuzzer/mutation.h"
#include "p4_pdpi/pd.h"
#include "p4_pdpi/utils/ir.h"

namespace p4_fuzzer {

using ::absl::gntohll;

using ::absl::Uniform;
using ::p4::v1::Action;
using ::p4::v1::FieldMatch;
using ::p4::v1::TableEntry;
using ::p4::v1::Update;

constexpr int kBitsInByte = 8;

// The probability that another entry is added to an update. 0.98 has been
// empirically determined to lead to big enough updates so that the test runs
// fast, but also sometimes generates small updates, which increases coverage.
constexpr float kAddUpdateProbability = 0.98;
// The probability of inserting an entry (in contrast to removing one).
// The probability of inserting a entry is larger than the probability of
// removing one, which means that eventually the switch fills up. 0.8 is a nice
// number because it causes the switch to fill up quickly, but there is still a
// good chance to get a couple of deletes in a row.
// TODO: change this back to 0.8 once we can generate enough valid
// inserts.
constexpr float kInsertProbability = 1;
// Upper bound of the number of actions in an ActionProfileActionSet for tables
// that support one-shot action selector programming.
constexpr uint32_t kActionProfileActionSetMax = 16;
// The probability of performing a mutation on a given table entry.
constexpr float kMutateUpdateProbability = 0.1;
// The probability of using a wildcard for a ternary or lpm match field.
constexpr float kFieldMatchWildcardProbability = 0.1;

namespace {

inline int DivideRoundedUp(const unsigned int n, const unsigned int d) {
  if (n == 0 || d == 0) {
    return 0;
  }

  return (n - 1) / d + 1;
}

p4::v1::ActionProfileAction FuzzActionProfileAction(
    absl::BitGen* gen, const pdpi::IrP4Info& ir_p4_info,
    const pdpi::IrTableDefinition& ir_table_info) {
  p4::v1::ActionProfileAction action;

  *action.mutable_action() =
      FuzzAction(gen, ChooseNonDefaultActionRef(gen, ir_table_info).action());

  action.set_weight(Uniform<int32_t>(*gen, 1, kActionProfileActionMaxWeight));

  // TODO: set the watch port field by uniformly selecting from a set
  // of valid watch ports.

  return action;
}

// Returns the table ids of tables that use one shot action selector
// programming.
std::vector<uint32_t> GetOneShotTableIds(const pdpi::IrP4Info& ir_p4_info) {
  std::vector<uint32_t> table_ids;

  for (auto& [id, table] : ir_p4_info.tables_by_id()) {
    if (table.uses_oneshot()) {
      table_ids.push_back(id);
    }
  }

  return table_ids;
}

// Returns the table ids of tables that contain at least one exact match field.
std::vector<uint32_t> GetMandatoryMatchTableIds(
    const pdpi::IrP4Info& ir_p4_info) {
  std::vector<uint32_t> table_ids;

  for (auto& [id, table] : ir_p4_info.tables_by_id()) {
    for (auto& [match_id, match] : table.match_fields_by_id()) {
      if (match.match_field().match_type() ==
          p4::config::v1::MatchField::EXACT) {
        table_ids.push_back(id);
        break;
      }
    }
  }

  return table_ids;
}

// Randomly generates an update type.
Update::Type FuzzUpdateType(absl::BitGen* gen, const SwitchState& state) {
  if (state.AllTablesEmpty()) {
    // Insert if there are no entries to delete.
    return Update::INSERT;
  } else {
    // If both insert and delete are possible, choose one randomly.
    if (absl::Bernoulli(*gen, kInsertProbability)) {
      return Update::INSERT;
    } else {
      return Update::DELETE;
    }
  }
}

// Randomly generates the table id of a non-empty table.
int FuzzNonEmptyTableId(absl::BitGen* gen, const SwitchState& switch_state) {
  CHECK(!switch_state.AllTablesEmpty())
      << "state: " << switch_state.SwitchStateSummary();
  int table_id;
  do {
    table_id = FuzzTableId(gen, switch_state);
  } while (switch_state.IsTableEmpty(table_id));
  return table_id;
}

// Randomly changes the table_entry, without affecting the key fields.
void FuzzNonKeyFields(absl::BitGen* gen, TableEntry* table_entry) {
  // With some probability, don't modify the element at all.
  if (absl::Bernoulli(*gen, 0.5)) return;

  // TODO: can't remove action at the moment, because IsWellformedUpdate
  // will think the update is no longer well-formed.
  if (absl::Bernoulli(*gen, 0.5)) {
    table_entry->clear_controller_metadata();
  }
  // TODO: also add/modify non-key fields.
}

// Randomly generates an INSERT or DELETE update. The update may be mutated (see
// go/p4-fuzzer-design for mutation types).
AnnotatedUpdate FuzzUpdate(absl::BitGen* gen, const pdpi::IrP4Info& ir_p4_info,
                           const SwitchState& switch_state) {
  std::vector<uint32_t> table_ids = switch_state.AllTableIds();
  CHECK_GT(table_ids.size(), 0)
      << "Cannot generate updates for program with no tables";

  Mutation mutation;
  bool do_mutate = false;

  if (absl::Bernoulli(*gen, kMutateUpdateProbability)) {
    do_mutate = true;
    mutation = FuzzMutation(gen);
    switch (mutation) {
      case Mutation::INVALID_ACTION_SELECTOR_WEIGHT:
        table_ids = GetOneShotTableIds(ir_p4_info);
        if (table_ids.empty()) {
          // Retry.
          return FuzzUpdate(gen, ir_p4_info, switch_state);
        }

        break;

      case Mutation::MISSING_MANDATORY_MATCH_FIELD:
        table_ids = GetMandatoryMatchTableIds(ir_p4_info);
        if (table_ids.empty()) {
          // Retry.
          return FuzzUpdate(gen, ir_p4_info, switch_state);
        }
        break;

      default:
        break;
    }
  }

  Update::Type type = FuzzUpdateType(gen, switch_state);
  Update update;
  update.set_type(type);

  switch (type) {
    case Update::INSERT: {
      const int table_id = UniformFromVector(gen, table_ids);

      // This might (with low probability) generate an entry that already
      // exists leading to a duplicate insert. This is fine, this update is just
      // rendered invalid and the oracle incorporates this in its prediction of
      // switch behavior.
      p4::v1::TableEntry table_entry =
          FuzzValidTableEntry(gen, ir_p4_info, table_id);

      *update.mutable_entity()->mutable_table_entry() = table_entry;

      break;
    }
    case Update::DELETE: {
      const int table_id = FuzzNonEmptyTableId(gen, switch_state);
      // Within a single call of FuzzWriteRequest, this might delete the same
      // entry multiple times.  This is fine, all but one of the deletes are
      // just invalid (and it is the oracle's job to know what the switch is
      // supposed to do with this).
      TableEntry table_entry =
          UniformFromVector(gen, switch_state.GetTableEntries(table_id));
      FuzzNonKeyFields(gen, &table_entry);
      *update.mutable_entity()->mutable_table_entry() = table_entry;
      break;
    }
    default:
      LOG(FATAL) << "Unsupported update type " << type;
  }

  if (do_mutate) {
    if (!MutateUpdate(gen, &update, ir_p4_info, switch_state, mutation).ok()) {
      // Retry mutating the update.
      return FuzzUpdate(gen, ir_p4_info, switch_state);
    }

    return GetAnnotatedUpdate(ir_p4_info, update, /* mutations = */ {mutation});
  }

  return GetAnnotatedUpdate(ir_p4_info, update, /* mutations = */ {});
}

}  // namespace

// Randomly generates a table id.
int FuzzTableId(absl::BitGen* gen, const SwitchState& switch_state) {
  return UniformFromVector(gen, switch_state.AllTableIds());
}

Mutation FuzzMutation(absl::BitGen* gen) {
  std::vector<int> valid_indexes;

  for (int i = Mutation_MIN; i <= Mutation_MAX; ++i) {
    if (Mutation_IsValid(i)) {
      valid_indexes.push_back(i);
    }
  }

  return static_cast<Mutation>(
      valid_indexes[Uniform<int>(*gen, 0, valid_indexes.size())]);
}

pdpi::IrActionReference ChooseNonDefaultActionRef(
    absl::BitGen* gen, const pdpi::IrTableDefinition& ir_table_info) {
  std::vector<pdpi::IrActionReference> refs;

  for (const auto& action_ref : ir_table_info.entry_actions()) {
    refs.push_back(action_ref);
  }

  return refs[absl::Uniform(*gen, 0u, refs.size())];
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
  if (bits == 0 && bytes == 0) {
    // TODO: For now, the fuzzer does not fuzz string fields (which have
    // 0 bits), but instead just uses a fixed string.
    return "some-id";
  }
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

uint64_t FuzzUint64(absl::BitGen* gen, int bits) {
  return BitsToUint64(FuzzBits(gen, bits, sizeof(uint64_t)));
}

p4::v1::FieldMatch FuzzTernaryFieldMatch(absl::BitGen* gen, int bits) {
  std::string mask = FuzzNonZeroBits(gen, bits);
  std::string value = FuzzBits(gen, bits);

  // If a mask bit is 0, the corresponding value bit also has to be 0.
  value = pdpi::Intersection(value, mask).value();

  p4::v1::FieldMatch match;
  match.mutable_ternary()->set_mask(mask);
  match.mutable_ternary()->set_value(value);
  return match;
}

p4::v1::FieldMatch FuzzLpmFieldMatch(absl::BitGen* gen, int bits) {
  // Since /8, /16, /24, and /32 are common, we want to bias the fuzzer to
  // generate more of them.
  std::vector<int> likely_bits;
  for (int i = kBitsInByte; i <= bits; i += kBitsInByte) {
    likely_bits.push_back(i);
  }

  int prefix_len;
  if (bits >= kBitsInByte && absl::Bernoulli(*gen, 0.2)) {
    prefix_len = UniformFromVector(gen, likely_bits);
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

p4::v1::FieldMatch FuzzExactFieldMatch(absl::BitGen* gen, int bits) {
  p4::v1::FieldMatch match;
  // Note that exact messages have to be provided, even if the value is 0.
  match.mutable_exact()->set_value(FuzzBits(gen, bits));
  return match;
}

p4::v1::FieldMatch FuzzOptionalFieldMatch(absl::BitGen* gen, int bits) {
  p4::v1::FieldMatch match;
  if (absl::Bernoulli(*gen, 0.5)) {
    match.mutable_optional()->set_value(FuzzBits(gen, bits));
  }
  return match;
}

p4::v1::FieldMatch FuzzExactFieldMatch(absl::BitGen* gen, int bits, int bytes) {
  p4::v1::FieldMatch match;
  match.mutable_optional()->set_value(FuzzNonZeroBits(gen, bits));
  return match;
}

p4::v1::FieldMatch FuzzFieldMatch(
    absl::BitGen* gen,
    const pdpi::IrMatchFieldDefinition& ir_match_field_info) {
  const p4::config::v1::MatchField& match_field_info =
      ir_match_field_info.match_field();

  p4::v1::FieldMatch match;
  switch (match_field_info.match_type()) {
    case p4::config::v1::MatchField::TERNARY:
      match = FuzzTernaryFieldMatch(gen, match_field_info.bitwidth());
      break;
    case p4::config::v1::MatchField::LPM:
      match = FuzzLpmFieldMatch(gen, match_field_info.bitwidth());
      break;
    case p4::config::v1::MatchField::EXACT:
      match = FuzzExactFieldMatch(gen, match_field_info.bitwidth());
      break;
    case p4::config::v1::MatchField::OPTIONAL:
      match = FuzzOptionalFieldMatch(gen, match_field_info.bitwidth());
      break;
    default:
      LOG(FATAL) << "Unsupported match: " << match_field_info.DebugString();
  }
  match.set_field_id(match_field_info.id());
  return match;
}

p4::v1::Action FuzzAction(absl::BitGen* gen,
                          const pdpi::IrActionDefinition& ir_action_info) {
  p4::v1::Action action;
  action.set_action_id(ir_action_info.preamble().id());

  for (auto& [id, ir_param] : ir_action_info.params_by_id()) {
    p4::v1::Action::Param* param = action.add_params();
    param->set_param_id(id);
    param->set_value(FuzzBits(gen, ir_param.param().bitwidth()));
  }

  return action;
}

p4::v1::ActionProfileActionSet FuzzActionProfileActionSet(
    absl::BitGen* gen, const pdpi::IrP4Info& ir_p4_info,
    const pdpi::IrTableDefinition& ir_table_info) {
  p4::v1::ActionProfileActionSet action_set;

  auto number_of_actions =
      Uniform<int32_t>(*gen, 0, kActionProfileActionSetMax);

  for (auto i = 0; i < number_of_actions; i++) {
    *action_set.add_action_profile_actions() =
        FuzzActionProfileAction(gen, ir_p4_info, ir_table_info);
  }

  return action_set;
}

void EnforceTableConstraints(absl::BitGen* gen,
                             const pdpi::IrP4Info& ir_p4_info,
                             const pdpi::IrTableDefinition& ir_table_info,
                             TableEntry* table_entry) {
  // TODO: implement program independent version of this function.
}

TableEntry FuzzValidTableEntry(absl::BitGen* gen,
                               const pdpi::IrP4Info& ir_p4_info,
                               const pdpi::IrTableDefinition& ir_table_info) {
  TableEntry table_entry;
  table_entry.set_table_id(ir_table_info.preamble().id());

  // Generate the matches.
  for (auto& [key, match_field_info] : ir_table_info.match_fields_by_id()) {
    // Skip deprecated fields
    bool deprecated =
        absl::c_any_of(match_field_info.match_field().annotations(),
                       [](const std::string annotation) {
                         return absl::StartsWith(annotation, "@deprecated(");
                       });
    if (deprecated) continue;

    // If the field can have wildcards, this may generate a wildcard match.
    // That's illegal according to P4RT spec, because wilcards must be
    // represented as the absence of that match.
    if (match_field_info.match_field().match_type() ==
            p4::config::v1::MatchField::TERNARY ||
        match_field_info.match_field().match_type() ==
            p4::config::v1::MatchField::OPTIONAL ||
        (match_field_info.match_field().match_type() ==
             p4::config::v1::MatchField::LPM &&
         absl::Bernoulli(*gen, kFieldMatchWildcardProbability))) {
      continue;
    }

    *table_entry.add_match() = FuzzFieldMatch(gen, match_field_info);
  }

  EnforceTableConstraints(gen, ir_p4_info, ir_table_info, &table_entry);

  // Generate the action.
  if (!ir_table_info.uses_oneshot()) {
    // Normal table, so choose a non-default action.
    *table_entry.mutable_action()->mutable_action() =
        FuzzAction(gen, ChooseNonDefaultActionRef(gen, ir_table_info).action());
  } else {
    *table_entry.mutable_action()->mutable_action_profile_action_set() =
        FuzzActionProfileActionSet(gen, ir_p4_info, ir_table_info);
  }

  // Set cookie and priority.
  table_entry.set_controller_metadata(FuzzUint64(gen, /*bits=*/64));
  if (ir_table_info.requires_priority()) {
    table_entry.set_priority(FuzzUint64(gen, /*bits=*/16));
  }

  // TODO: Fuzz default actions.
  // TODO: Fuzz meters and counters.
  return table_entry;
}

TableEntry FuzzValidTableEntry(absl::BitGen* gen,
                               const pdpi::IrP4Info& ir_p4_info,
                               const uint32_t table_id) {
  TableEntry entry;
  return FuzzValidTableEntry(
      gen, ir_p4_info, gutil::FindOrDie(ir_p4_info.tables_by_id(), table_id));
}

std::vector<AnnotatedTableEntry> ValidForwardingEntries(
    absl::BitGen* gen, const pdpi::IrP4Info& ir_p4_info,
    const int num_entries) {
  std::vector<AnnotatedTableEntry> entries;
  SwitchState state(ir_p4_info);

  for (int i = 0; i < num_entries; ++i) {
    p4::v1::TableEntry entry;

    do {
      entry = FuzzValidTableEntry(gen, ir_p4_info, FuzzTableId(gen, state));
    } while (state.GetTableEntry(entry) != absl::nullopt);

    p4::v1::Update update;
    update.set_type(p4::v1::Update::INSERT);
    *update.mutable_entity()->mutable_table_entry() = entry;

    CHECK(state.ApplyUpdate(update).ok());  // Crash okay

    entries.push_back(
        GetAnnotatedTableEntry(ir_p4_info, entry, /*mutations = */ {}));
  }

  return entries;
}

AnnotatedWriteRequest FuzzWriteRequest(absl::BitGen* gen,
                                       const pdpi::IrP4Info& ir_p4_info,
                                       const SwitchState& switch_state) {
  AnnotatedWriteRequest request;

  while (absl::Bernoulli(*gen, kAddUpdateProbability)) {
    *request.add_updates() = FuzzUpdate(gen, ir_p4_info, switch_state);
    // TODO: For now, we only send requests of size <= 1. This makes
    // debugging easier.
    break;
  }

  return request;
}

}  // namespace p4_fuzzer
