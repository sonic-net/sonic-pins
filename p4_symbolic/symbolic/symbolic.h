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

#include <cstdint>
#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/btree_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/ir/table_entries.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesizer.pb.h"
#include "p4_symbolic/symbolic/context.h"
#include "p4_symbolic/symbolic/solver_state.h"
#include "p4_symbolic/symbolic/values.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {

// Symbolically evaluates/interprets the given program against the given
// entries for every table in the program, and the available physical ports
// on the switch. Optionally, for types that have @p4runtime_translate(_,
// string) annotation, a static mapping between the P4RT values and the
// underlying bitvector values may be provided. Otherwise, a mapping is
// inferred dynamically for such types.
// The given `entries` may contain symbolic or concrete table entries.
absl::StatusOr<std::unique_ptr<SolverState>> EvaluateP4Program(
    const ir::P4Program &program, const ir::TableEntries &entries,
    const std::vector<int> &physical_ports = {},
    const TranslationPerType &translation_per_type = {});

// Symbolically evaluates/interprets the given program against the given
// entries for every table in the program, and the available physical ports
// on the switch. Optionally, for types that have @p4runtime_translate(_,
// string) annotation, a static mapping between the P4RT values and the
// underlying bitvector values may be provided. Otherwise, a mapping is
// inferred dynamically for such types.
absl::StatusOr<std::unique_ptr<SolverState>> EvaluateP4Program(
    const p4::v1::ForwardingPipelineConfig &config,
    const std::vector<p4::v1::Entity> &entries,
    const std::vector<int> &physical_ports = {},
    const TranslationPerType &translation_per_type = {});

// Symbolically evaluates/interprets the given program against the given
// entries for every table in the program, and the available physical ports
// on the switch. Optionally, for types that have @p4runtime_translate(_,
// string) annotation, a static mapping between the P4RT values and the
// underlying bitvector values may be provided. Otherwise, a mapping is
// inferred dynamically for such types.
// The given `entries` may contain symbolic or concrete table entries.
// This is currently being used to generate packets for path coverage
// (go/p4-symbolic-path-coverage).
absl::StatusOr<packet_synthesizer::PacketSynthesisResults>
EvaluateP4ProgramAndSynthesizePacketsCoveringAllControlFlowPaths(
    const p4::v1::ForwardingPipelineConfig &config,
    const std::vector<p4::v1::Entity> &entities,
    const std::vector<int> &physical_ports = {},
    const TranslationPerType &translation_per_type = {});

// Finds a concrete packet and flow in the program that satisfies the given
// assertion and meets the structure constrained by solver_state.
absl::StatusOr<std::optional<ConcreteContext>> Solve(SolverState &state);
absl::StatusOr<std::optional<ConcreteContext>> Solve(
    SolverState &state, const Assertion &assertion);

// Dumps the underlying SMT program for debugging.
std::string DebugSMT(const std::unique_ptr<SolverState> &state,
                     const Assertion &assertion);

absl::Status AddConstraintsForStaticallyTranslatedValues(
    SolverState &state,
    std::optional<SymbolicPerPacketState> headers = std::nullopt);

}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_SYMBOLIC_H_
