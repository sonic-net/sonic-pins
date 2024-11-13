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

#include "p4_symbolic/packet_synthesizer/packet_synthesis_criteria.h"

#include "google/protobuf/util/message_differencer.h"
#include "gutil/status.h"

namespace p4_symbolic::packet_synthesizer {

bool Equals(const CriteriaVariant& lhs, const CriteriaVariant& rhs) {
  return google::protobuf::util::MessageDifferencer::Equals(lhs, rhs);
}

absl::StatusOr<CriteriaVariant> GetCriteriaVariant(
    const PacketSynthesisCriteria& criteria,
    CriteriaVariant::CriteriaCase criteria_case) {
  CriteriaVariant criteria_variant;
  switch (criteria_case) {
    case CriteriaVariant::kOutputCriteria:
      if (criteria.has_output_criteria()) {
        *criteria_variant.mutable_output_criteria() =
            criteria.output_criteria();
      }
      break;
    case CriteriaVariant::kInputPacketHeaderCriteria:
      if (criteria.has_input_packet_header_criteria()) {
        *criteria_variant.mutable_input_packet_header_criteria() =
            criteria.input_packet_header_criteria();
      }
      break;
    case CriteriaVariant::kTableReachabilityCriteria:
      if (criteria.has_table_reachability_criteria()) {
        *criteria_variant.mutable_table_reachability_criteria() =
            criteria.table_reachability_criteria();
      }
      break;
    case CriteriaVariant::kTableEntryReachabilityCriteria:
      if (criteria.has_table_entry_reachability_criteria()) {
        *criteria_variant.mutable_table_entry_reachability_criteria() =
            criteria.table_entry_reachability_criteria();
      }
      break;
    case CriteriaVariant::kPayloadCriteria:
      if (criteria.has_payload_criteria()) {
        *criteria_variant.mutable_payload_criteria() =
            criteria.payload_criteria();
      }
      break;
    default:
      return gutil::InvalidArgumentErrorBuilder()
             << "Unexpected criteria case " << criteria_case;
  }
  return criteria_variant;
}

absl::StatusOr<bool> HaveEqualCriteriaVariants(
    const PacketSynthesisCriteria& lhs, const PacketSynthesisCriteria& rhs,
    CriteriaVariant::CriteriaCase criteria_case) {
  ASSIGN_OR_RETURN(const auto lhs_variant,
                   GetCriteriaVariant(lhs, criteria_case));
  ASSIGN_OR_RETURN(const auto rhs_variant,
                   GetCriteriaVariant(rhs, criteria_case));
  return Equals(lhs_variant, rhs_variant);
}

}  // namespace p4_symbolic::packet_synthesizer
