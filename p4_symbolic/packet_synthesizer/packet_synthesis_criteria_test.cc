#include "p4_symbolic/packet_synthesizer/packet_synthesis_criteria.h"

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesis_criteria.pb.h"

namespace p4_symbolic::packet_synthesizer {
namespace {
using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;

TEST(GetCriteriaVariantTest, EmptyCriteriaYieldsEmptyVariant) {
  PacketSynthesisCriteria criteria;
  CriteriaVariant variant;

  for (const auto criteria_case : {
           CriteriaVariant::kTableEntryReachabilityCriteria,
           CriteriaVariant::kTableReachabilityCriteria,
           CriteriaVariant::kOutputCriteria,
           CriteriaVariant::kInputPacketHeaderCriteria,
           CriteriaVariant::kPayloadCriteria,
       }) {
    ASSERT_THAT(GetCriteriaVariant(criteria, criteria_case),
                IsOkAndHolds(EqualsProto(variant)));
  }
}

TEST(GetCriteriaVariantTest,
     YieldsCorrectVariantForTableEntryReachabilityCriteria) {
  auto table_entry_reachablity_criteria =
      gutil::ParseProtoOrDie<TableEntryReachabilityCriteria>(
          R"pb(table_name: "dummy" match_index: 10)pb");

  PacketSynthesisCriteria criteria;
  *criteria.mutable_table_entry_reachability_criteria() =
      table_entry_reachablity_criteria;

  CriteriaVariant expected_variant;
  *expected_variant.mutable_table_entry_reachability_criteria() =
      table_entry_reachablity_criteria;

  ASSERT_THAT(GetCriteriaVariant(
                  criteria, CriteriaVariant::kTableEntryReachabilityCriteria),
              IsOkAndHolds(EqualsProto(expected_variant)));
}

TEST(GetCriteriaVariantTest, YieldsCorrectVariantForTableReachabilityCriteria) {
  auto table_reachablity_criteria =
      gutil::ParseProtoOrDie<TableReachabilityCriteria>(
          R"pb(table_name: "dummy")pb");

  PacketSynthesisCriteria criteria;
  *criteria.mutable_table_reachability_criteria() = table_reachablity_criteria;

  CriteriaVariant expected_variant;
  *expected_variant.mutable_table_reachability_criteria() =
      table_reachablity_criteria;

  ASSERT_THAT(
      GetCriteriaVariant(criteria, CriteriaVariant::kTableReachabilityCriteria),
      IsOkAndHolds(EqualsProto(expected_variant)));
}

TEST(GetCriteriaVariantTest, YieldsCorrectVariantForOutputCriteria) {
  auto output_criteria =
      gutil::ParseProtoOrDie<OutputCriteria>(R"pb(drop_expected: true)pb");

  PacketSynthesisCriteria criteria;
  *criteria.mutable_output_criteria() = output_criteria;

  CriteriaVariant expected_variant;
  *expected_variant.mutable_output_criteria() = output_criteria;

  ASSERT_THAT(GetCriteriaVariant(criteria, CriteriaVariant::kOutputCriteria),
              IsOkAndHolds(EqualsProto(expected_variant)));
}

TEST(GetCriteriaVariantTest, YieldsCorrectVariantForInputPacketHeaderCriteria) {
  auto input_header_criteria =
      gutil::ParseProtoOrDie<HeaderCriteria>(R"pb(field_criteria {
                                                    field_match {
                                                      name: "dummy.field"
                                                      exact { str: "dummy" }
                                                    }
                                                  })pb");

  PacketSynthesisCriteria criteria;
  *criteria.mutable_input_packet_header_criteria() = input_header_criteria;

  CriteriaVariant expected_variant;
  *expected_variant.mutable_input_packet_header_criteria() =
      input_header_criteria;

  ASSERT_THAT(
      GetCriteriaVariant(criteria, CriteriaVariant::kInputPacketHeaderCriteria),
      IsOkAndHolds(EqualsProto(expected_variant)));
}

TEST(GetCriteriaVariantTest, YieldsCorrectVariantForPayloadCriteria) {
  auto payload_cretia =
      gutil::ParseProtoOrDie<PayloadCriteria>(R"pb(payload: "dummy")pb");

  PacketSynthesisCriteria criteria;
  *criteria.mutable_payload_criteria() = payload_cretia;

  CriteriaVariant expected_variant;
  *expected_variant.mutable_payload_criteria() = payload_cretia;

  ASSERT_THAT(GetCriteriaVariant(criteria, CriteriaVariant::kPayloadCriteria),
              IsOkAndHolds(EqualsProto(expected_variant)));
}

}  // namespace
}  // namespace p4_symbolic::packet_synthesizer
