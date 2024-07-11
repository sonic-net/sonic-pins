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

#include <string>
#include <vector>

#include "absl/random/random.h"
#include "absl/strings/match.h"
#include "glog/logging.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_fuzzer/fuzzer.pb.h"
#include "p4_fuzzer/switch_state.h"
#include "p4_pdpi/ir.h"

namespace p4_fuzzer {

// Upper bound on the weight of each ActionProfileAction in an
// ActionProfileActionSet for tables that support one-shot action selector
// programming.
constexpr int32_t kActionProfileActionMaxWeight = 100;

template <typename T>
const T& UniformFromVector(absl::BitGen* gen, const std::vector<T>& vec) {
  CHECK(!vec.empty());
  int index = absl::Uniform<int>(*gen, /*lo=*/0, /*hi=*/vec.size());
  return vec[index];
}

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

// Takes an 8 byte string that represents a number in network byte order, and
// turns it into a uint64 in host byte order. Dies if the string is not 8 byte.
uint64_t BitsToUint64(const std::string& data);

// Returns a mutation type uniformly randomly chosen from the enum in
// fuzzer.proto.
Mutation FuzzMutation(absl::BitGen* gen);

// Returns a randomly generated `bits` long number in network byte order, stored
// in a `bytes` long string. Unused bits are set to 0.
std::string FuzzBits(absl::BitGen* gen, int bits, int bytes);

// Just like above, but the returned string is just long enough to hold the
// randomly generated number.
std::string FuzzBits(absl::BitGen* gen, int bits);

// Generates a `bits` long uint64 in host byte order.
uint64_t FuzzUint64(absl::BitGen* gen, int bits);

// Randomly generates a ternary field match with a bitwidth of `bits`.
// Does not set the match field id. See "9.1.1. Match Format" in the P4Runtime
// specification for details about which FieldMatch values are valid.
p4::v1::FieldMatch FuzzTernaryFieldMatch(absl::BitGen* gen, int bits);

// Randomly generates a field match that conforms to the given
// match field info. See "9.1.1. Match Format" in the P4Runtime
// specification for details about which FieldMatch values are valid.
p4::v1::FieldMatch FuzzFieldMatch(
    absl::BitGen* gen, const pdpi::IrMatchFieldDefinition& ir_match_field_info);

// Randomly generates an action that conforms to the given `ir_action_info`.
// See "9.1.2. Action Specification"  in the P4Runtime specification for details
// about which Action values are valid.
p4::v1::Action FuzzAction(absl::BitGen* gen,
                          const pdpi::IrActionDefinition& ir_action_info);

// Randomly generates an ActionProfileActionSet that conforms to the given
// `ir_table_info` and `ir_p4_info` for tables that support one-shot
// action selector programming. Refer to section "9.2.3. One Shot Action
// Selector Programming" in the P4Runtime specification for details on
// ActionProfileActionSets.
p4::v1::ActionProfileActionSet FuzzActionProfileActionSet(
    absl::BitGen* gen, const pdpi::IrP4Info& ir_p4_info,
    const pdpi::IrTableDefinition& ir_table_info);

// Randomly chooses an id that belongs to a table in the switch.
int FuzzTableId(absl::BitGen* gen, const SwitchState& switch_state);

// Randomly generates a table entry that conforms to the given table info.
// The p4 info is used to lookup action references. See go/p4-fuzzer-design for
// details about which TableEntry values are valid.
p4::v1::TableEntry FuzzValidTableEntry(
    absl::BitGen* gen, const pdpi::IrP4Info& ir_p4_info,
    const pdpi::IrTableDefinition& ir_table_info);

// Randomly generates a table entry that conforms to the table info in the
// p4 info with the given table id. See go/p4-fuzzer-design for details about
// which TableEntry values are valid.
p4::v1::TableEntry FuzzValidTableEntry(absl::BitGen* gen,
                                       const pdpi::IrP4Info& p4_info,
                                       const uint32_t table_id);

// Randomly generates a set of valid table entries that, when installed in order
// to an empty switch state, all install correctly.
std::vector<AnnotatedTableEntry> ValidForwardingEntries(
    absl::BitGen* gen, const pdpi::IrP4Info& ir_p4_info, const int num_entries);

// Randomly generates a set of updates, both valid and invalid.
AnnotatedWriteRequest FuzzWriteRequest(absl::BitGen* gen,
                                       const pdpi::IrP4Info& ir_p4_info,
                                       const SwitchState& switch_state);

// Takes a P4 Runtime table and returns randomly chosen action ref from the
// action refs that are not in default only scope.
pdpi::IrActionReference ChooseNonDefaultActionRef(
    absl::BitGen* gen, const pdpi::IrTableDefinition& ir_table_info);

}  // namespace p4_fuzzer

#endif  // P4_FUZZER_FUZZ_UTIL_H_
