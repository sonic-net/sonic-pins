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

// The `FuzzFoo` functions in this file are all of the form:
//
//     Foo foo = FuzzFoo(gen, context)
//
// Each of these functions randomly generates a valid value of type `Foo`.
// The goal is that these functions are also complete, in the sense that every
// valid value of `Foo` has a non-zero (though possibly extremely small)
// propability of being returned from the `FuzzFoo` function. Whenever this is
// violated, there should be a TODO with an associated bug.
//
// The meaning of "valid" depends on the type Foo, and often some context
// parameters. Read each function's documentation to understand validity.
#ifndef P4_FUZZER_FUZZ_UTIL_H_
#define P4_FUZZER_FUZZ_UTIL_H_

#include <optional>
#include <string>
#include <vector>

#include "absl/random/random.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/types/optional.h"
#include "absl/types/span.h"
#include "glog/logging.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_fuzzer/fuzzer.pb.h"
#include "p4_fuzzer/fuzzer_config.h"
#include "p4_fuzzer/switch_state.h"
#include "p4_infra/p4_pdpi/ir.pb.h"

namespace p4_fuzzer {

// Upper bound on the number of actions in an ActionProfileActionSet for tables
// that support one-shot action selector programming.
constexpr int kActionProfileActionSetMaxCardinality = 32;

// Max member weight for action profiles that use SumOfMembers size semantics.
// TODO: Get this information from the P4Info when possible.
constexpr int kActionProfileMaxMemberWeight = 4095;

// A predicate over P4 values (match field or action parameter).
using P4ValuePredicate =
    std::function<bool(const p4::config::v1::P4NamedType &type_name,
                       const google::protobuf::RepeatedPtrField<
                           pdpi::IrMatchFieldReference> &references)>;

bool IsPort(const p4::config::v1::P4NamedType &type_name,
            const google::protobuf::RepeatedPtrField<
                pdpi::IrMatchFieldReference>& references = {});
bool IsUnknownQosQueue(const p4::config::v1::P4NamedType& type_name,
                       const google::protobuf::RepeatedPtrField<
                           pdpi::IrMatchFieldReference>& references = {});
bool IsUnknownQosOrCpuQueue(const p4::config::v1::P4NamedType& type_name,
                            const google::protobuf::RepeatedPtrField<
                                pdpi::IrMatchFieldReference>& references = {});
bool IsNeighbor(const p4::config::v1::P4NamedType& type_name,
                const google::protobuf::RepeatedPtrField<
                    pdpi::IrMatchFieldReference> &references = {});
bool IsReferring(
    const p4::config::v1::P4NamedType &type_name,
    const google::protobuf::RepeatedPtrField<pdpi::IrMatchFieldReference>
        &references);

bool IsDisabledForFuzzing(const FuzzerConfig &config, absl::string_view name);

template <typename T>
const T &UniformFromSpan(absl::BitGen *gen, absl::Span<const T> span) {
  CHECK(!span.empty());
  int index = absl::Uniform<int>(*gen, /*lo=*/0, /*hi=*/span.size());
  return span[index];
}

// Implicit conversion to Span does not seem to work correctly for templated
// code.
template <typename T>
const T &UniformFromSpan(absl::BitGen *gen, const std::vector<T> &vec) {
  return UniformFromSpan(gen, absl::MakeConstSpan(vec));
}

template <typename T>
const typename T::mapped_type &UniformValueFromMap(absl::BitGen *gen,
                                                   const T &map) {
  CHECK(!map.empty()); // Crash OK
  int index = absl::Uniform<int>(*gen, /*lo=*/0, /*hi=*/map.size());
  auto iter = map.begin();
  while (index > 0) {
    iter++;
    index--;
  }
  return iter->second;
}

// Gets the action profile corresponding to the given table from the IrP4Info.
absl::StatusOr<p4::config::v1::ActionProfile>
GetActionProfile(const pdpi::IrP4Info &ir_info, int table_id);

// Returns the list of all "valid" tables in the underlying P4 program. Valid
// tables are those that can legally have entries inserted into them (e.g. due
// to the Fuzzer's role (specified in `config`)) and are not @deprecated,
// @unsupported, or disabled.
const std::vector<pdpi::IrTableDefinition>
AllValidTablesForP4RtRole(const FuzzerConfig &config);

// Returns the list of all "valid" actions in the underlying P4 program for
// `table`. Valid actions are those that are legal for use in table entries and
// not @deprecated, @unsupported, or disabled.
const std::vector<pdpi::IrActionReference>
AllValidActions(const FuzzerConfig &config,
                const pdpi::IrTableDefinition &table);

// Returns the list of all "valid" match fields in the underlying P4 program for
// `table`. Valid match fields are those that are not @deprecated, @unsupported,
// or disabled.
const std::vector<pdpi::IrMatchFieldDefinition>
AllValidMatchFields(const FuzzerConfig &config,
                    const pdpi::IrTableDefinition &table);

// Takes a string `data` that represents a number in network byte
// order (big-endian), and masks off all but the least significant `used_bits`
// bits.
//
// For example, given a 3 byte string, that represents the 10 bit number 1000
// (binary 1111101000):
//
//                      1                   2
//  0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3
// +---------------+---------------+---------------+
// |0 0 0 0 0 0 0 0|0 0 0 0 0 0 1 1|1 1 1 0 1 0 0 0|
// +---------------+---------------+---------------+
// |          padding          |
//
// and a `used_bits` value of 7, the function will generate this string:
//
//                      1                   2
//  0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3
// +---------------+---------------+---------------+
// |0 0 0 0 0 0 0 0|0 0 0 0 0 0 0 0|0 1 1 0 1 0 0 0|
// +---------------+---------------+---------------+
// |          padding                |
//
// The numbers above the string indicate each bit's index in the string.
std::string SetUnusedBitsToZero(int used_bits, std::string data);

// Set the N least significant bits to zero in data.
std::string ZeroNLeastSignificantBits(int zero_bits, std::string data);

// Takes an 8 byte string that represents a number in network byte order, and
// turns it into a uint64 in host byte order. Dies if the string is not 8 byte.
uint64_t BitsToUint64(const std::string &data);

// Returns a mutation type uniformly randomly chosen from the enum in
// fuzzer.proto.
Mutation FuzzMutation(absl::BitGen *gen, const FuzzerConfig &config);

// Returns a randomly generated `bits` long number in network byte order. The
// returned string has just enough bytes to hold the randomly generated number.
// Returns an error if `bits` is <= 0, as empty bytestrings are disallowed.
absl::StatusOr<std::string> FuzzBits(absl::BitGen *gen, int bits);

// Generates a `bits` long uint64 in host byte order.
uint64_t FuzzUint64(absl::BitGen *gen, int bits);

// Returns a random ID with a length in the closed interval
// [`min_chars`, `max_chars`].
std::string FuzzRandomId(absl::BitGen *gen, int min_chars = 1,
                         int max_chars = 10);

// Randomly generates a ternary field match with a bitwidth of `bits`.
// Does not set the match field id. See "9.1.1. Match Format" in the P4Runtime
// specification for details about which FieldMatch values are valid.
// Guarantees not to be a wildcard match.
absl::StatusOr<p4::v1::FieldMatch>
FuzzTernaryFieldMatch(absl::BitGen *gen, const FuzzerConfig &config, int bits);

// Randomly generates a field match that conforms to the given
// match field info. See "9.1.1. Match Format" in the P4Runtime
// specification for details about which FieldMatch values are valid.
// May fail if a reference to another table is required.
absl::StatusOr<p4::v1::FieldMatch>
FuzzFieldMatch(absl::BitGen *gen, const FuzzerConfig &config,
               const SwitchState &switch_state,
               const pdpi::IrMatchFieldDefinition &ir_match_field_info);

// Randomly generate an action for a table.
// May fail if a reference to another table is required.
absl::StatusOr<p4::v1::TableAction>
FuzzAction(absl::BitGen *gen, const FuzzerConfig &config,
           const SwitchState &switch_state,
           const pdpi::IrTableDefinition &table_definition);

// Randomly generates an action that conforms to the given `ir_action_info` and
// the reference info in `ir_table_info`. See "9.1.2. Action Specification"  in
// the P4Runtime specification for details about which Action values are valid.
// Will fail if a reference to an empty table is required.
absl::StatusOr<p4::v1::Action>
FuzzAction(absl::BitGen *gen, const FuzzerConfig &config,
           const SwitchState &switch_state,
           const pdpi::IrActionDefinition &ir_action_info,
           const pdpi::IrTableDefinition &ir_table_info);

// Randomly generates an ActionProfileActionSet that conforms to the given
// `ir_table_info` and `ir_p4_info` for tables that support one-shot
// action selector programming. Refer to section "9.2.3. One Shot Action
// Selector Programming" in the P4Runtime specification for details on
// ActionProfileActionSets.
// Will fail if a reference to an empty table is required.
absl::StatusOr<p4::v1::ActionProfileActionSet>
FuzzActionProfileActionSet(absl::BitGen *gen, const FuzzerConfig &config,
                           const SwitchState &switch_state,
                           const pdpi::IrTableDefinition &ir_table_info);

// Randomly chooses an id that belongs to a table in the switch.
int FuzzTableId(absl::BitGen *gen, const FuzzerConfig &config);

// Randomly generates the table id of a non-empty table.
int FuzzNonEmptyTableId(absl::BitGen *gen, const FuzzerConfig &config,
                        const SwitchState &switch_state);

// Randomly generates the table id of a modifiable table.
int FuzzModifiableTableId(absl::BitGen *gen, const FuzzerConfig &config,
                          const SwitchState &switch_state);

// Randomly generates a table entry that conforms to the given table info.
// The p4 info is used to lookup action references. See go/p4-fuzzer-design for
// details about which TableEntry values are valid. Additional constraints that
// aren't in the p4 program can be added by passing in a P4-constraint string to
// `additional_constraint`. May fail if a reference to another table is
// required.
absl::StatusOr<p4::v1::TableEntry> FuzzValidTableEntry(
    absl::BitGen* gen, const FuzzerConfig& config,
    const SwitchState& switch_state,
    const pdpi::IrTableDefinition& ir_table_info,
    std::optional<absl::string_view> additional_constraint = std::nullopt);

// Same as above, but for a table_id.
absl::StatusOr<p4::v1::TableEntry> FuzzValidTableEntry(
    absl::BitGen* gen, const FuzzerConfig& config,
    const SwitchState& switch_state, const uint32_t table_id,
    std::optional<absl::string_view> additional_constraint = std::nullopt);

// Randomly generates a multicast group entry. May fail if a reference to
// another table is required.
absl::StatusOr<p4::v1::MulticastGroupEntry>
FuzzValidMulticastGroupEntry(absl::BitGen *gen, const FuzzerConfig &config,
                             const SwitchState &switch_state);

// Randomly generates a set of updates, both valid and invalid. Optionally takes
// a max_batch_size parameter determining the maximum number of updates in a
// request.
AnnotatedWriteRequest
FuzzWriteRequest(absl::BitGen *gen, const FuzzerConfig &config,
                 const SwitchState &switch_state,
                 absl::optional<int> max_batch_size = absl::nullopt);

// Modifies non-key fields of `entity`.
absl::Status ModifyEntity(absl::BitGen* gen, const FuzzerConfig& config,
                          const SwitchState& switch_state,
                          p4::v1::Entity& entity);

}  // namespace p4_fuzzer

#endif // P4_FUZZER_FUZZ_UTIL_H_
