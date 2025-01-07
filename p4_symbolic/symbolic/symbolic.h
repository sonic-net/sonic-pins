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

// Contains the entry point to our symbolic interpretation code, as well
// as helpers for debugging and finding concrete packets and their context.

#ifndef P4_SYMBOLIC_SYMBOLIC_SYMBOLIC_H_
#define P4_SYMBOLIC_SYMBOLIC_SYMBOLIC_H_

#include <optional>
#include <string>
#include <utility>

#include "absl/container/btree_map.h"
#include "absl/strings/string_view.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_symbolic/ir/table_entries.h"
#include "p4_symbolic/symbolic/context.h"
#include "p4_symbolic/symbolic/values.h"
#include "p4_symbolic/z3_util.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {

// A port reserved to encode dropping packets.
// The value is arbitrary; we choose the same value as BMv2:
// https://github.com/p4lang/behavioral-model/blob/main/docs/simple_switch.md#standard-metadata
constexpr int kDropPort = 511; // 2^9 - 1.
// An arbitrary port we reserve for the CPU port (for PacketIO packets).
constexpr int kCpuPort = 510; // 2^9 - 2.
constexpr int kPortBitwidth = 9;

// Boolean pseudo header field that is initialized to false, set to true when
// the header is extracted, and set to true/false when `setValid`/`setInvalid`
// is called, respectively.
constexpr absl::string_view kValidPseudoField = "$valid$";
// Boolean pseudo header field denoting that the header has been extracted by
// the parser. It is initialized to false and set to true when the header is
// extracted. This is necessary to distinguish between headers extracted and
// headers set to valid in the parsers via the `setValid` primitives. For
// example, a `packet_in` header may be set to valid but should never be
// extracted from the input packet.
constexpr absl::string_view kExtractedPseudoField = "$extracted$";
// Boolean pseudo header field that is set to true by p4-symbolic if the packet
// gets cloned. Not an actual header field, but convenient for analysis.
constexpr absl::string_view kGotClonedPseudoField = "$got_cloned$";
// 32-bit bit-vector field in standard metadata indicating whether there is a
// parser error. The error code is defined in core.p4 and can be extended by the
// P4 program. 0 means no error.
constexpr absl::string_view kParserErrorField =
    "standard_metadata.parser_error";

// The overall state of our symbolic solver/interpreter.
// This is returned by our main analysis/interpration function, and is used
// to find concrete test packets and for debugging.
// This is internal to our solver code. External code that uses our solver
// is not expected to access any of these fields or modify them.
// Only one instance of this struct will be constructed per P4 program
// evaluation, which can be then used to solve for particular assertions
// many times.
class SolverState {
 public:
  SolverState(ir::P4Program program, ir::TableEntries entries)
      : program(std::move(program)),
        entries(std::move(entries)),
        solver(std::make_unique<z3::solver>(*context.z3_context)) {}
  SolverState(const SolverState &) = delete;
  SolverState(SolverState &&) = default;
  ~SolverState() {
    // During the destruction of a z3::solver object, previously added
    // assertions (through z3::solver::add) sometimes lead to memory leaks. The
    // exact details of the root cause is not yet clear. Here we explicitly
    // clear the assertions upon releasing a solver.
    // See b/285990074 for more details.
    if (solver) solver->reset();
  }

  // Returns the SMT formulae of all assertions in the solver.
  std::string GetSolverSMT();
  // Returns the SMT formulae of all ingress, parsed, and egress headers and
  // solver constraints.
  std::string GetHeadersAndSolverConstraintsSMT();

  // The IR of the p4 program being analyzed.
  ir::P4Program program;
  // Maps the name of a table to a list of its entries.
  ir::TableEntries entries;
  // The symbolic context of our interpretation/analysis of the program,
  // including symbolic handles on packet headers and its trace. A new
  // z3::context object is created within each symbolic context. Note that this
  // has to precede the solver object so that the solver will be destroyed
  // before the z3 context during destruction.
  SymbolicContext context;
  // Having the z3 solver defined here allows Z3 to remember interesting
  // deductions it made while solving for one particular assertion, and re-use
  // them during solving with future assertions.
  std::unique_ptr<z3::solver> solver;
  // Store the p4 runtime translator state for use by .Solve(...).
  values::P4RuntimeTranslator translator;
};

// An assertion is a user defined function that takes a symbolic context
// as input, and returns constraints on symbolic handles exposed by that
// context. For example:
// z3::expr portIsOne(const SymbolicContext &ctx) {
//   return ctx.ingress_port == 1;
// }
using Assertion =
    std::function<absl::StatusOr<z3::expr>(const SymbolicContext &)>;

// User provided TranslationData for P4 types. This is a partial
// map. For any P4 type included in this map, the statically provided
// TranslationData is used. For other types, if runtime translated (i.e. have
// @p4runtime_translation("", string) annotation),
// TranslationData{.static_mapping = {}, .dynamic_translation = true} is used.
using TranslationPerType =
    absl::btree_map<std::string, values::TranslationData>;

// Symbolically evaluates/interprets the given program against the given
// entries for every table in the program, and the available physical ports
// on the switch. Optionally, for types that have @p4runtime_translate(_,
// string) annotation, a static mapping between the P4RT values and the
// underlying bitvector values may be provided. Otherwise, a mapping is
// inferred dynamically for such types.
absl::StatusOr<std::unique_ptr<symbolic::SolverState>> EvaluateP4Program(
    const p4::v1::ForwardingPipelineConfig &config,
    const std::vector<p4::v1::TableEntry> &entries,
    const std::vector<int> &physical_ports = {},
    const TranslationPerType &translation_per_type = {});

// Finds a concrete packet and flow in the program that satisfies the given
// assertion and meets the structure constrained by solver_state.
absl::StatusOr<std::optional<ConcreteContext>> Solve(SolverState &solver_state);
absl::StatusOr<std::optional<ConcreteContext>> Solve(
    SolverState &solver_state, const Assertion &assertion);

// Dumps the underlying SMT program for debugging.
std::string DebugSMT(const std::unique_ptr<SolverState> &solver_state,
                     const Assertion &assertion);

} // namespace symbolic
} // namespace p4_symbolic

#endif // P4_SYMBOLIC_SYMBOLIC_SYMBOLIC_H_
