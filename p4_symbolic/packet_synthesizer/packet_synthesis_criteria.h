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

#ifndef PINS_P4_SYMBOLIC_PACKET_SYNTHESIZER_PACKET_SYNTHESIS_CRITERIA_H_
#define PINS_P4_SYMBOLIC_PACKET_SYNTHESIZER_PACKET_SYNTHESIS_CRITERIA_H_

#include <vector>

#include "absl/status/statusor.h"
#include "absl/types/span.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesis_criteria.pb.h"

namespace p4_symbolic::packet_synthesizer {

// Returns whether two CriteriaVariants are considered equal.
bool Equals(const CriteriaVariant& lhs, const CriteriaVariant& rhs);

// Get a single CriteriaVariant corresponding to the given `criteria_case` in
// the given `criteria`.
absl::StatusOr<CriteriaVariant> GetCriteriaVariant(
    const PacketSynthesisCriteria& criteria,
    CriteriaVariant::CriteriaCase criteria_case);

// Checks whether `lhs` and `rhs` have equal criteria variants corresponding
// to the given `criteria_case`.
absl::StatusOr<bool> HaveEqualCriteriaVariants(
    const PacketSynthesisCriteria& lhs, const PacketSynthesisCriteria& rhs,
    CriteriaVariant::CriteriaCase criteria_case);

// Returns either a criteria effectively reflecting the logical conjunction of
// the operands or an error.
// Precisely, in the resulting criteria, for each criteria case c:
// - If lhs.c is empty, rhs.c is used
// - If rhs.c is empty, lhs.c is used
// - If lhs.c and rhs.c are equal, lhs.c is used
// - If both are non-empty and non-equal, an error is returned.
absl::StatusOr<PacketSynthesisCriteria> MakeConjunction(
    const PacketSynthesisCriteria& lhs, const PacketSynthesisCriteria& rhs);

// Returns a list of criteria in which each member is the result of conjuncting
// a pair of criteria corresponding to an element with the same index in the
// cartesian product of `lhs` and `rhs`.
// In other words, [MakeConjunction(l,r) for (l,r) in lhs x rhs].
absl::StatusOr<std::vector<PacketSynthesisCriteria>>
MakeCartesianProductConjunction(absl::Span<const PacketSynthesisCriteria> lhs,
                                absl::Span<const PacketSynthesisCriteria> rhs);

}  // namespace p4_symbolic::packet_synthesizer

#endif  // PINS_P4_SYMBOLIC_PACKET_SYNTHESIZER_PACKET_SYNTHESIS_CRITERIA_H_
