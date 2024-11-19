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

#include "p4_symbolic/packet_synthesizer/criteria_generator.h"

#include <string>
#include <vector>

#include "absl/types/optional.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/pd.h"
#include "p4_symbolic/packet_synthesizer/coverage_goal.pb.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesis_criteria.pb.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesizer.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesizer.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_nonstandard_platforms.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

namespace p4_symbolic::packet_synthesizer {
namespace {

using ::gutil::ParseProtoOrDie;

// Returns packet synthesis parameters with the pipeline config for FBR and a
// simple table entry.
// If `in_port_match` is not null, the added entry matches on the provided
// ingress port.
PacketSynthesisParams GetParams(
    // TODO: Use non-SAI program and move test out of SAI
    // directory.
    std::optional<std::string> in_port_match = std::nullopt) {
  const sai::Instantiation instantiation =
      sai::Instantiation::kFabricBorderRouter;
  const pdpi::IrP4Info ir_p4info = sai::GetIrP4Info(instantiation);
  const p4::v1::ForwardingPipelineConfig pipeline_config =
      sai::GetNonstandardForwardingPipelineConfig(
          instantiation, sai::NonstandardPlatform::kP4Symbolic);

  PacketSynthesisParams params;
  *params.mutable_pipeline_config() = pipeline_config;
  auto pd_entry = ParseProtoOrDie<sai::TableEntry>(R"pb(
    acl_pre_ingress_table_entry {
      match {}
      action { set_vrf { vrf_id: "vrf-80" } }
      priority: 1
    })pb");
  if (in_port_match.has_value())
    pd_entry.mutable_acl_pre_ingress_table_entry()
        ->mutable_match()
        ->mutable_in_port()
        ->set_value(*in_port_match);
  const auto pi_entry = pdpi::PdTableEntryToPi(ir_p4info, pd_entry);

  CHECK_OK(pi_entry.status());
  *params.mutable_pi_entries()->Add() = *pi_entry;

  return params;
}

void ExpectEqualCriteriaList(
    const std::vector<PacketSynthesisCriteria>& result,
    const std::vector<PacketSynthesisCriteria>& expected) {
  ASSERT_EQ(result.size(), expected.size());
  for (int i = 0; i < result.size(); i++) {
    ASSERT_THAT(result[i], gutil::EqualsProto(expected[i]));
  }
}

TEST(GenerateSynthesisCriteriaTest,
     EntryCoverageGoalWithWildcardIncludeYieldsCorrectCriteriaList) {
  // Get a packet synthesizer object.
  ASSERT_OK_AND_ASSIGN(auto synthesizer,
                       PacketSynthesizer::Create(GetParams()));

  ASSERT_OK_AND_ASSIGN(
      auto criteria_list,
      GenerateSynthesisCriteriaFor(
          ParseProtoOrDie<CoverageGoals>(R"pb(
            coverage_goals { entry_coverage { tables { patterns: [ "*" ] } } }
          )pb"),
          synthesizer->SolverState()));

  ExpectEqualCriteriaList(
      criteria_list,
      {
          ParseProtoOrDie<PacketSynthesisCriteria>(
              R"pb(
                table_reachability_criteria {
                  table_name: "ingress.acl_pre_ingress.acl_pre_ingress_table"
                }
                table_entry_reachability_criteria {
                  table_name: "ingress.acl_pre_ingress.acl_pre_ingress_table"
                  match_index: 0
                }
              )pb"),
      });
}

TEST(GenerateSynthesisCriteriaTest,
     EntryCoverageGoalWithWildcardExcludeYieldsEmptyCriteriaList) {
  // Get a packet synthesizer object.
  ASSERT_OK_AND_ASSIGN(auto synthesizer,
                       PacketSynthesizer::Create(GetParams()));

  ASSERT_OK_AND_ASSIGN(
      auto criteria_list,
      GenerateSynthesisCriteriaFor(ParseProtoOrDie<CoverageGoals>(R"pb(
                                     coverage_goals {
                                       entry_coverage {
                                         tables { patterns: [ "*" ] }
                                         table_exclusions { patterns: [ "*" ] }
                                       }
                                     }
                                   )pb"),
                                   synthesizer->SolverState()));

  ASSERT_EQ(criteria_list.size(), 0);
}

TEST(GenerateSynthesisCriteriaTest,
     EntryCoverageGoalWithCoverDefaultActionsIncludesEmptyTables) {
  // Get a packet synthesizer object.
  ASSERT_OK_AND_ASSIGN(auto synthesizer,
                       PacketSynthesizer::Create(GetParams()));

  ASSERT_OK_AND_ASSIGN(
      auto criteria_list,
      GenerateSynthesisCriteriaFor(ParseProtoOrDie<CoverageGoals>(R"pb(
                                     coverage_goals {
                                       entry_coverage {
                                         tables { patterns: [ "*" ] }
                                         cover_default_actions: true
                                       }
                                     }
                                   )pb"),
                                   synthesizer->SolverState()));

  ASSERT_GT(criteria_list.size(), 1);
}

TEST(GenerateSynthesisCriteriaTest,
     EntryCoverageGoalWithCoverDefaultActionsYieldsCorrectCriteriaList) {
  // Get a packet synthesizer object.
  ASSERT_OK_AND_ASSIGN(auto synthesizer,
                       PacketSynthesizer::Create(GetParams()));

  ASSERT_OK_AND_ASSIGN(
      auto criteria_list,
      GenerateSynthesisCriteriaFor(
          ParseProtoOrDie<CoverageGoals>(R"pb(
            coverage_goals {
              entry_coverage {
                tables {
                  patterns: [ "ingress.acl_pre_ingress.acl_pre_ingress_table" ]
                }
                cover_default_actions: true
              }
            }
          )pb"),
          synthesizer->SolverState()));

  ExpectEqualCriteriaList(
      criteria_list,
      {
          ParseProtoOrDie<PacketSynthesisCriteria>(
              R"pb(
                table_reachability_criteria {
                  table_name: "ingress.acl_pre_ingress.acl_pre_ingress_table"
                }
                table_entry_reachability_criteria {
                  table_name: "ingress.acl_pre_ingress.acl_pre_ingress_table"
                  match_index: 0
                }
              )pb"),
          ParseProtoOrDie<PacketSynthesisCriteria>(
              R"pb(
                table_reachability_criteria {
                  table_name: "ingress.acl_pre_ingress.acl_pre_ingress_table"
                }
                table_entry_reachability_criteria {
                  table_name: "ingress.acl_pre_ingress.acl_pre_ingress_table"
                  match_index: -1
                }
              )pb"),
      });
}

TEST(GenerateSynthesisCriteriaTest,
     PacketFateCoverageGoalYieldsCorrectCriteriaList) {
  // Get a packet synthesizer object.
  ASSERT_OK_AND_ASSIGN(auto synthesizer,
                       PacketSynthesizer::Create(GetParams()));

  ASSERT_OK_AND_ASSIGN(
      auto criteria_list,
      GenerateSynthesisCriteriaFor(
          ParseProtoOrDie<CoverageGoals>(
              R"pb(
                coverage_goals {
                  packet_fate_coverage { fates: [ DROP, NOT_DROP ] }
                }
              )pb"),
          synthesizer->SolverState()));

  ExpectEqualCriteriaList(criteria_list,
                          {
                              ParseProtoOrDie<PacketSynthesisCriteria>(
                                  R"pb(
                                    output_criteria { drop_expected: true }
                                  )pb"),
                              ParseProtoOrDie<PacketSynthesisCriteria>(
                                  R"pb(
                                    output_criteria { drop_expected: false }
                                  )pb"),
                          });
}

TEST(GenerateSynthesisCriteriaTest,
     CoverageGoalWithEntryAndFateCoverageYieldsCorrectResults) {
  // Get a packet synthesizer object.
  ASSERT_OK_AND_ASSIGN(auto synthesizer,
                       PacketSynthesizer::Create(GetParams()));

  ASSERT_OK_AND_ASSIGN(
      auto criteria_list,
      GenerateSynthesisCriteriaFor(
          ParseProtoOrDie<CoverageGoals>(
              R"pb(
                coverage_goals {
                  entry_coverage { tables { patterns: [ "*" ] } }
                  packet_fate_coverage { fates: [ DROP, NOT_DROP ] }
                }
              )pb"),
          synthesizer->SolverState()));

  ExpectEqualCriteriaList(
      criteria_list,
      {
          ParseProtoOrDie<PacketSynthesisCriteria>(
              R"pb(
                table_reachability_criteria {
                  table_name: "ingress.acl_pre_ingress.acl_pre_ingress_table"
                }
                table_entry_reachability_criteria {
                  table_name: "ingress.acl_pre_ingress.acl_pre_ingress_table"
                  match_index: 0
                }
                output_criteria { drop_expected: true }
              )pb"),
          ParseProtoOrDie<PacketSynthesisCriteria>(
              R"pb(
                table_reachability_criteria {
                  table_name: "ingress.acl_pre_ingress.acl_pre_ingress_table"
                }
                table_entry_reachability_criteria {
                  table_name: "ingress.acl_pre_ingress.acl_pre_ingress_table"
                  match_index: 0
                }
                output_criteria { drop_expected: false }
              )pb"),
      });
}

TEST(GenerateSynthesisCriteriaTest, CoverageGoalsYieldsCorrectResults) {
  // Get a packet synthesizer object.
  ASSERT_OK_AND_ASSIGN(auto synthesizer,
                       PacketSynthesizer::Create(GetParams()));

  ASSERT_OK_AND_ASSIGN(
      auto criteria_list,
      GenerateSynthesisCriteriaFor(
          ParseProtoOrDie<CoverageGoals>(
              R"pb(
                coverage_goals {
                  entry_coverage { tables { patterns: [ "*" ] } }

                }
                coverage_goals {
                  packet_fate_coverage { fates: [ DROP, NOT_DROP ] }
                }
              )pb"),
          synthesizer->SolverState()));

  ExpectEqualCriteriaList(
      criteria_list,
      {
          ParseProtoOrDie<PacketSynthesisCriteria>(
              R"pb(
                table_reachability_criteria {
                  table_name: "ingress.acl_pre_ingress.acl_pre_ingress_table"
                }
                table_entry_reachability_criteria {
                  table_name: "ingress.acl_pre_ingress.acl_pre_ingress_table"
                  match_index: 0
                }
              )pb"),
          ParseProtoOrDie<PacketSynthesisCriteria>(
              R"pb(
                output_criteria { drop_expected: true }
              )pb"),
          ParseProtoOrDie<PacketSynthesisCriteria>(
              R"pb(
                output_criteria { drop_expected: false }
              )pb"),
      });
}

}  // namespace
}  // namespace p4_symbolic::packet_synthesizer
