// Copyright 2025 Google LLC
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
// limitations under the License

#ifndef PINS_P4_SYMBOLIC_SYMBOLIC_SOLVER_STATE_H_
#define PINS_P4_SYMBOLIC_SYMBOLIC_SOLVER_STATE_H_

#include <cstdint>
#include <functional>
#include <memory>
#include <string>
#include <utility>

#include "absl/container/btree_map.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/context.h"
#include "p4_symbolic/symbolic/values.h"
#include "z3++.h"
namespace p4_symbolic {
namespace symbolic {

// A port reserved to encode dropping packets.
// The value is arbitrary; we choose the same value as BMv2:
// https://github.com/p4lang/behavioral-model/blob/main/docs/simple_switch.md#standard-metadata
constexpr int kDropPort = 511;  // 2^9 - 1.

// An arbitrary port we reserve for the CPU port (for PacketIO packets).
constexpr int kCpuPort = 510;  // 2^9 - 2.

// Bit-width of port numbers.
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

// Boolean pseudo header field that is set to true by p4-symbolic if the packet
// gets recirculated. Not an actual header field, but convenient for analysis.
constexpr absl::string_view kGotRecirculatedPseudoField = "$got_recirculated$";

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
  SolverState(ir::P4Program program)
      : program(std::move(program)),
        solver(std::make_unique<z3::solver>(*context.z3_context)) {}
  SolverState(const SolverState &) = delete;
  SolverState(SolverState &&) = default;
  ~SolverState() {
    // During the destruction of a z3::solver object, previously added
    // assertions (through z3::solver::add) sometimes lead to memory leaks. The
    // exact details of the root cause is not yet clear. Here we explicitly
    // clear the assertions upon releasing a solver.
    if (solver) solver->reset();
  }

  // Returns the SMT formulae of all assertions in the solver.
  std::string GetSolverSMT();
  // Returns the SMT formulae of all ingress, parsed, and egress headers and
  // solver constraints.
  std::string GetHeadersAndSolverConstraintsSMT();

  // The IR of the p4 program being analyzed.
  ir::P4Program program;
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

}  // namespace symbolic
}  // namespace p4_symbolic

#endif // PINS_P4_SYMBOLIC_SYMBOLIC_SOLVER_STATE_H_
