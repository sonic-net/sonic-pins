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

#ifndef PINS_P4_SYMBOLIC_PACKET_SYNTHESIZER_CRITERIA_GENERATOR_H_
#define PINS_P4_SYMBOLIC_PACKET_SYNTHESIZER_CRITERIA_GENERATOR_H_

#include <vector>

#include "absl/status/statusor.h"
#include "p4_symbolic/packet_synthesizer/coverage_goal.pb.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesis_criteria.pb.h"
#include "p4_symbolic/symbolic/symbolic.h"

namespace p4_symbolic::packet_synthesizer {

// Generates a list of packet synthesis criteria for the given list of
// (composite) coverage `goals`, consistent with the semantics defined in
// coverage_goal.proto:CoverageGoals.
absl::StatusOr<std::vector<PacketSynthesisCriteria>>
GenerateSynthesisCriteriaFor(const CoverageGoals& goals,
                             const symbolic::SolverState& solver_state);

}  // namespace p4_symbolic::packet_synthesizer

#endif  // PINS_P4_SYMBOLIC_PACKET_SYNTHESIZER_CRITERIA_GENERATOR_H_
