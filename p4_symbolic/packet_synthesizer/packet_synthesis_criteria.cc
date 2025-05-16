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

#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/substitute.h"
#include "absl/types/span.h"
#include "google/protobuf/util/message_differencer.h"
#include "gutil/status.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesis_criteria.pb.h"

namespace p4_symbolic::packet_synthesizer {

namespace {

// LINT.IfChange(set_criteria_variant)
absl::Status SetCriteriaVariant(PacketSynthesisCriteria& criteria,
                                const CriteriaVariant& criteria_variant,
                                CriteriaVariant::CriteriaCase criteria_case) {
  switch (criteria_case) {
    case CriteriaVariant::kOutputCriteria:
      if (criteria_variant.has_output_criteria()) {
        *criteria.mutable_output_criteria() =
            criteria_variant.output_criteria();
      } else {
        criteria.clear_output_criteria();
      }
      break;
    case CriteriaVariant::kInputPacketHeaderCriteria:
      if (criteria_variant.has_input_packet_header_criteria()) {
        *criteria.mutable_input_packet_header_criteria() =
            criteria_variant.input_packet_header_criteria();
      } else {
        criteria.clear_input_packet_header_criteria();
      }
      break;
    case CriteriaVariant::kTableReachabilityCriteria:
      if (criteria_variant.has_table_reachability_criteria()) {
        *criteria.mutable_table_reachability_criteria() =
            criteria_variant.table_reachability_criteria();
      } else {
        criteria.clear_table_reachability_criteria();
      }
      break;
    case CriteriaVariant::kTableEntryReachabilityCriteria:
      if (criteria_variant.has_table_entry_reachability_criteria()) {
        *criteria.mutable_table_entry_reachability_criteria() =
            criteria_variant.table_entry_reachability_criteria();
      } else {
        criteria.clear_table_entry_reachability_criteria();
      }
      break;
    case CriteriaVariant::kPayloadCriteria:
      if (criteria_variant.has_payload_criteria()) {
        *criteria.mutable_payload_criteria() =
            criteria_variant.payload_criteria();
      } else {
        criteria.clear_payload_criteria();
      }
      break;
    case CriteriaVariant::kIngressPortCriteria:
      if (criteria_variant.has_ingress_port_criteria()) {
        *criteria.mutable_ingress_port_criteria() =
            criteria_variant.ingress_port_criteria();
      } else {
        criteria.clear_ingress_port_criteria();
      }
      break;
    default:
      return gutil::InvalidArgumentErrorBuilder()
             << "Unexpected criteria case " << criteria_case;
  }

  return absl::OkStatus();
}
// LINT.ThenChange()

}  // namespace

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
    case CriteriaVariant::kIngressPortCriteria:
      if (criteria.has_ingress_port_criteria()) {
        *criteria_variant.mutable_ingress_port_criteria() =
            criteria.ingress_port_criteria();
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

absl::StatusOr<PacketSynthesisCriteria> MakeConjunction(
    const PacketSynthesisCriteria& lhs, const PacketSynthesisCriteria& rhs) {
  PacketSynthesisCriteria merged_criteria;
  for (auto criteria_case : {
           CriteriaVariant::kOutputCriteria,
           CriteriaVariant::kInputPacketHeaderCriteria,
           CriteriaVariant::kTableReachabilityCriteria,
           CriteriaVariant::kTableEntryReachabilityCriteria,
           CriteriaVariant::kPayloadCriteria,
           CriteriaVariant::kIngressPortCriteria,
       }) {
    ASSIGN_OR_RETURN(const CriteriaVariant lhs_variant,
                     GetCriteriaVariant(lhs, criteria_case));
    ASSIGN_OR_RETURN(const CriteriaVariant rhs_variant,
                     GetCriteriaVariant(rhs, criteria_case));

    if (lhs_variant.criteria_case() == CriteriaVariant::CRITERIA_NOT_SET) {
      // LHS is empty, so we can just copy RHS.
      RETURN_IF_ERROR(
          SetCriteriaVariant(merged_criteria, rhs_variant, criteria_case));
    } else if (rhs_variant.criteria_case() ==
               CriteriaVariant::CRITERIA_NOT_SET) {
      // RHS is empty, so we can just copy LHS.
      RETURN_IF_ERROR(
          SetCriteriaVariant(merged_criteria, lhs_variant, criteria_case));
    } else if (Equals(lhs_variant, rhs_variant)) {
      // LHS and RHS are the same.
      RETURN_IF_ERROR(
          SetCriteriaVariant(merged_criteria, lhs_variant, criteria_case));
    } else {
      // LHS and RHS are not empty and NOT equal.
      if (lhs_variant.has_input_packet_header_criteria()) {
        // Merge input packet header conditions.
        RETURN_IF_ERROR(
            SetCriteriaVariant(merged_criteria, lhs_variant, criteria_case));
        for (const auto& rhs_field_criteria :
             rhs_variant.input_packet_header_criteria().field_criteria()) {
          *merged_criteria.mutable_input_packet_header_criteria()
               ->add_field_criteria() = rhs_field_criteria;
        }
      } else {
        // The rest of the non-empty, non-equal criteria variants are not
        // supported for merging.
        return absl::UnimplementedError(
            absl::Substitute("Merging of non-empty, non-equal variants of the "
                             "same type (except of header conditions) "
                             "not supported.\nlhs: '$0' \n rhs: '$1'",
                             lhs.ShortDebugString(), rhs.ShortDebugString()));
      }
    }
  }

  if (lhs.has_metadata() || rhs.has_metadata()) {
    *merged_criteria.mutable_metadata() = lhs.metadata();
    merged_criteria.mutable_metadata()
        ->mutable_covered_entity_debug_strings()
        ->Add(rhs.metadata().covered_entity_debug_strings().begin(),
              rhs.metadata().covered_entity_debug_strings().end());
  }

  return merged_criteria;
}

absl::StatusOr<std::vector<PacketSynthesisCriteria>>
MakeCartesianProductConjunction(absl::Span<const PacketSynthesisCriteria> lhs,
                                absl::Span<const PacketSynthesisCriteria> rhs) {
  std::vector<PacketSynthesisCriteria> cartesian_product;

  for (auto& lhs_criteria : lhs) {
    for (auto& rhs_criteria : rhs) {
      ASSIGN_OR_RETURN(cartesian_product.emplace_back(),
                       MakeConjunction(lhs_criteria, rhs_criteria));
    }
  }

  return cartesian_product;
}

}  // namespace p4_symbolic::packet_synthesizer
