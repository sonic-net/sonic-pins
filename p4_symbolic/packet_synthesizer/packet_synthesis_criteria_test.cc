#include "p4_symbolic/packet_synthesizer/packet_synthesis_criteria.h"

#include <vector>

#include "absl/status/status.h"
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
using ::gutil::ParseProtoOrDie;

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
      ParseProtoOrDie<TableEntryReachabilityCriteria>(
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
      ParseProtoOrDie<TableReachabilityCriteria>(R"pb(table_name: "dummy")pb");

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
      ParseProtoOrDie<OutputCriteria>(R"pb(drop_expected: true)pb");

  PacketSynthesisCriteria criteria;
  *criteria.mutable_output_criteria() = output_criteria;

  CriteriaVariant expected_variant;
  *expected_variant.mutable_output_criteria() = output_criteria;

  ASSERT_THAT(GetCriteriaVariant(criteria, CriteriaVariant::kOutputCriteria),
              IsOkAndHolds(EqualsProto(expected_variant)));
}

TEST(GetCriteriaVariantTest, YieldsCorrectVariantForInputPacketHeaderCriteria) {
  auto input_header_criteria =
      ParseProtoOrDie<HeaderCriteria>(R"pb(field_criteria {
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
      ParseProtoOrDie<PayloadCriteria>(R"pb(payload: "dummy")pb");

  PacketSynthesisCriteria criteria;
  *criteria.mutable_payload_criteria() = payload_cretia;

  CriteriaVariant expected_variant;
  *expected_variant.mutable_payload_criteria() = payload_cretia;

  ASSERT_THAT(GetCriteriaVariant(criteria, CriteriaVariant::kPayloadCriteria),
              IsOkAndHolds(EqualsProto(expected_variant)));
}

TEST(GetCriteriaVariantTest, YieldsCorrectVariantForIngressPortCriteria) {
  auto ingress_port_criteria =
      ParseProtoOrDie<PortCriteria>(R"pb(v1model_port: 5)pb");

  PacketSynthesisCriteria criteria;
  *criteria.mutable_ingress_port_criteria() = ingress_port_criteria;

  CriteriaVariant expected_variant;
  *expected_variant.mutable_ingress_port_criteria() = ingress_port_criteria;

  ASSERT_THAT(
      GetCriteriaVariant(criteria, CriteriaVariant::kIngressPortCriteria),
      IsOkAndHolds(EqualsProto(expected_variant)));
}

TEST(MakeConjunctionTest, YieldsCorrectCriteria) {
  auto lhs = ParseProtoOrDie<PacketSynthesisCriteria>(
      R"pb(output_criteria { drop_expected: true })pb");
  auto rhs = ParseProtoOrDie<PacketSynthesisCriteria>(
      R"pb(ingress_port_criteria { v1model_port: 5 })pb");

  ASSERT_THAT(MakeConjunction(lhs, rhs),
              IsOkAndHolds(EqualsProto(
                  R"pb(
                    output_criteria { drop_expected: true }
                    ingress_port_criteria { v1model_port: 5 }
                  )pb")));
}

TEST(MakeConjunctionTest,
     FailsWhenOperandsHaveNonEqualNonEmptyValuesForTheSameCriteriaCase) {
  auto lhs = ParseProtoOrDie<PacketSynthesisCriteria>(
      R"pb(output_criteria { drop_expected: true })pb");
  auto rhs = ParseProtoOrDie<PacketSynthesisCriteria>(
      R"pb(output_criteria { drop_expected: false })pb");

  ASSERT_THAT(MakeConjunction(lhs, rhs),
              gutil::StatusIs(absl::StatusCode::kUnimplemented));
}

TEST(MakeConjunctionTest,
     SucceedsWhenOperandsHaveEqualNonEmptyValuesForTheSameCriteriaCase) {
  auto lhs = ParseProtoOrDie<PacketSynthesisCriteria>(
      R"pb(output_criteria { drop_expected: true })pb");
  auto rhs = ParseProtoOrDie<PacketSynthesisCriteria>(
      R"pb(output_criteria { drop_expected: true })pb");

  PacketSynthesisCriteria expected_criteria = lhs;

  ASSERT_THAT(MakeConjunction(lhs, rhs),
              IsOkAndHolds(EqualsProto(expected_criteria)));
}

TEST(MakeConjunctionTest,
     SucceedsWhenOperandsHaveNonEqualInputPacketHeaderCriteria) {
  auto lhs = ParseProtoOrDie<PacketSynthesisCriteria>(
      R"pb(input_packet_header_criteria {
             field_criteria {
               field_match {
                 name: "dummy.field1"
                 exact { str: "dummy1" }
               }
               negated: true
             }
           })pb");
  auto rhs = ParseProtoOrDie<PacketSynthesisCriteria>(
      R"pb(input_packet_header_criteria {
             field_criteria {
               field_match {
                 name: "dummy.field2"
                 exact { str: "dummy2" }
               }
             }
           })pb");

  PacketSynthesisCriteria expected_criteria;
  *expected_criteria.mutable_input_packet_header_criteria()
       ->mutable_field_criteria()
       ->Add() = lhs.input_packet_header_criteria().field_criteria(0);
  *expected_criteria.mutable_input_packet_header_criteria()
       ->mutable_field_criteria()
       ->Add() = rhs.input_packet_header_criteria().field_criteria(0);

  ASSERT_THAT(MakeConjunction(lhs, rhs),
              IsOkAndHolds(EqualsProto(expected_criteria)));
}

TEST(MakeCartesianProductConjunctionTest, YieldsCorrectResult) {
  std::vector<PacketSynthesisCriteria> lhs = {
      ParseProtoOrDie<PacketSynthesisCriteria>(
          R"pb(output_criteria { drop_expected: false })pb"),
      ParseProtoOrDie<PacketSynthesisCriteria>(
          R"pb(output_criteria { drop_expected: true })pb"),
  };

  std::vector<PacketSynthesisCriteria> rhs = {
      ParseProtoOrDie<PacketSynthesisCriteria>(
          R"pb(ingress_port_criteria { v1model_port: 5 })pb"),
      ParseProtoOrDie<PacketSynthesisCriteria>(
          R"pb(ingress_port_criteria { v1model_port: 6 })pb"),
  };

  std::vector<PacketSynthesisCriteria> expected = {
      ParseProtoOrDie<PacketSynthesisCriteria>(
          R"pb(output_criteria { drop_expected: false }
               ingress_port_criteria { v1model_port: 5 })pb"),
      ParseProtoOrDie<PacketSynthesisCriteria>(
          R"pb(output_criteria { drop_expected: false }
               ingress_port_criteria { v1model_port: 6 })pb"),
      ParseProtoOrDie<PacketSynthesisCriteria>(
          R"pb(output_criteria { drop_expected: true }
               ingress_port_criteria { v1model_port: 5 })pb"),
      ParseProtoOrDie<PacketSynthesisCriteria>(
          R"pb(output_criteria { drop_expected: true }
               ingress_port_criteria { v1model_port: 6 })pb"),
  };

  ASSERT_OK_AND_ASSIGN(auto cartesian_product,
                       MakeCartesianProductConjunction(lhs, rhs));
  ASSERT_EQ(cartesian_product.size(), expected.size());
  for (int i = 0; i < cartesian_product.size(); i++) {
    ASSERT_THAT(cartesian_product[i], EqualsProto(expected[i]));
  }
}

}  // namespace

}  // namespace p4_symbolic::packet_synthesizer
