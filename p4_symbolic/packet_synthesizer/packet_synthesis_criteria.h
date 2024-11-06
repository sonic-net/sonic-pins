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

#include "absl/status/statusor.h"
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

}  // namespace p4_symbolic::packet_synthesizer

#endif  // PINS_P4_SYMBOLIC_PACKET_SYNTHESIZER_PACKET_SYNTHESIS_CRITERIA_H_
