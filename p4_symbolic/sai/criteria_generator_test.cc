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

#include "absl/log/log.h"
#include "absl/types/optional.h"
#include "gmock/gmock.h"
#include "google/protobuf/message.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/pd.h"
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
  const auto pi_entry =
      pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, pd_entry);

  CHECK_OK(pi_entry.status());
  *params.add_pi_entities()->mutable_table_entry() = *pi_entry;

  return params;
}

void ExpectEqualCriteriaList(
    const std::vector<PacketSynthesisCriteria>& result,
    const std::vector<PacketSynthesisCriteria>& expected,
    bool ignore_metadata = true) {
  ASSERT_EQ(result.size(), expected.size());
  for (int i = 0; i < result.size(); i++) {
    PacketSynthesisCriteria result_criteria = result[i];
    PacketSynthesisCriteria expected_criteria = expected[i];
    LOG(INFO) << result_criteria.ShortDebugString();
    if (ignore_metadata) {
      result_criteria.clear_metadata();
      expected_criteria.clear_metadata();
    }
    ASSERT_THAT(result_criteria, gutil::EqualsProto(expected_criteria));
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
     EntryCoverageGoalWithExcludeEmptyTablesExcludesEmptyTables) {
  // Get a packet synthesizer object.
  ASSERT_OK_AND_ASSIGN(auto synthesizer,
                       PacketSynthesizer::Create(GetParams()));

  ASSERT_OK_AND_ASSIGN(
      auto criteria_list,
      GenerateSynthesisCriteriaFor(
          ParseProtoOrDie<CoverageGoals>(R"pb(
            coverage_goals {
              entry_coverage {
                tables { patterns: [ "ingress.l3_admit.l3_admit_table" ] }
                cover_default_actions: true
                exclude_empty_tables: true
              }
            }
          )pb"),
          synthesizer->SolverState()));

  ExpectEqualCriteriaList(criteria_list, {});
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

TEST(
    GenerateSynthesisCriteriaTest,
    CartersianProductCoverageGoalWithEntryAndFateCoverageYieldsCorrectResults) {
  // Get a packet synthesizer object.
  ASSERT_OK_AND_ASSIGN(auto synthesizer,
                       PacketSynthesizer::Create(GetParams()));

  ASSERT_OK_AND_ASSIGN(
      auto criteria_list,
      GenerateSynthesisCriteriaFor(
          ParseProtoOrDie<CoverageGoals>(
              R"pb(
                coverage_goals {
                  cartesian_product_coverage {
                    entry_coverage { tables { patterns: [ "*" ] } }
                    packet_fate_coverage { fates: [ DROP, NOT_DROP ] }
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

TEST(GenerateSynthesisCriteriaTest,
     HeaderCoverageGoalYieldsCorrectCriteriaList) {
  // Get a packet synthesizer object.
  ASSERT_OK_AND_ASSIGN(auto synthesizer,
                       PacketSynthesizer::Create(GetParams()));

  ASSERT_OK_AND_ASSIGN(
      auto criteria_list,
      GenerateSynthesisCriteriaFor(
          ParseProtoOrDie<CoverageGoals>(
              R"pb(
                coverage_goals {
                  header_coverage { headers { patterns: [ "ipv4", "ipv6" ] } }
                }
              )pb"),
          synthesizer->SolverState()));

  ExpectEqualCriteriaList(criteria_list,
                          {
                              ParseProtoOrDie<PacketSynthesisCriteria>(
                                  R"pb(
                                    input_packet_header_criteria {
                                      field_criteria {
                                        field_match {
                                          name: "ipv4.$valid$"
                                          exact { hex_str: "0x1" }
                                        }
                                      }
                                    }
                                  )pb"),
                              ParseProtoOrDie<PacketSynthesisCriteria>(
                                  R"pb(
                                    input_packet_header_criteria {
                                      field_criteria {
                                        field_match {
                                          name: "ipv6.$valid$"
                                          exact { hex_str: "0x1" }
                                        }
                                      }
                                    }
                                  )pb"),
                          });
}

TEST(GenerateSynthesisCriteriaTest,
     HeaderCoverageGoalDoesNotYieldMetadataValidtyCriteria) {
  // Get a packet synthesizer object.
  ASSERT_OK_AND_ASSIGN(auto synthesizer,
                       PacketSynthesizer::Create(GetParams()));

  ASSERT_OK_AND_ASSIGN(
      auto criteria_list,
      GenerateSynthesisCriteriaFor(
          ParseProtoOrDie<CoverageGoals>(
              R"pb(
                coverage_goals {
                  header_coverage {
                    headers { patterns: [ "standard_metadata", "scalars" ] }
                  }
                }
              )pb"),
          synthesizer->SolverState()));

  ExpectEqualCriteriaList(criteria_list, {});
}

TEST(GenerateSynthesisCriteriaTest,
     HeaderCoverageGoalWithWildcardExcludeYieldsEmptyCriteriaList) {
  // Get a packet synthesizer object.
  ASSERT_OK_AND_ASSIGN(auto synthesizer,
                       PacketSynthesizer::Create(GetParams()));

  ASSERT_OK_AND_ASSIGN(auto criteria_list,
                       GenerateSynthesisCriteriaFor(
                           ParseProtoOrDie<CoverageGoals>(
                               R"pb(
                                 coverage_goals {
                                   header_coverage {
                                     headers { patterns: [ "ipv4", "ipv6" ] }
                                     header_exclusions { patterns: [ "*" ] }
                                   }
                                 }
                               )pb"),
                           synthesizer->SolverState()));

  ExpectEqualCriteriaList(criteria_list, {});
}

TEST(GenerateSynthesisCriteriaTest,
     HeaderCoverageGoalWithHeaderExcludeYieldsCorrectCriteriaList) {
  // Get a packet synthesizer object.
  ASSERT_OK_AND_ASSIGN(auto synthesizer,
                       PacketSynthesizer::Create(GetParams()));

  ASSERT_OK_AND_ASSIGN(auto criteria_list,
                       GenerateSynthesisCriteriaFor(
                           ParseProtoOrDie<CoverageGoals>(
                               R"pb(
                                 coverage_goals {
                                   header_coverage {
                                     headers { patterns: [ "ipv4", "ipv6" ] }
                                     header_exclusions { patterns: [ "ipv4" ] }
                                   }
                                 }
                               )pb"),
                           synthesizer->SolverState()));

  ExpectEqualCriteriaList(criteria_list,
                          {
                              ParseProtoOrDie<PacketSynthesisCriteria>(
                                  R"pb(
                                    input_packet_header_criteria {
                                      field_criteria {
                                        field_match {
                                          name: "ipv6.$valid$"
                                          exact { hex_str: "0x1" }
                                        }
                                      }
                                    }
                                  )pb"),
                          });
}

TEST(GenerateSynthesisCriteriaTest,
     HeaderCoverageGoalWithHeaderPreventationYieldCorrectResults) {
  // Get a packet synthesizer object.
  ASSERT_OK_AND_ASSIGN(auto synthesizer,
                       PacketSynthesizer::Create(GetParams()));

  ASSERT_OK_AND_ASSIGN(
      auto criteria_list,
      GenerateSynthesisCriteriaFor(
          ParseProtoOrDie<CoverageGoals>(
              R"pb(
                coverage_goals {
                  header_coverage {
                    headers { patterns: [ "ipv4", "vlan" ] }
                    headers_to_prevent_unless_explicitly_covered {
                      patterns: [ "vlan" ]
                    }
                  }
                }
              )pb"),
          synthesizer->SolverState()));

  ExpectEqualCriteriaList(criteria_list,
                          {
                              ParseProtoOrDie<PacketSynthesisCriteria>(
                                  R"pb(
                                    input_packet_header_criteria {
                                      field_criteria {
                                        field_match {
                                          name: "ipv4.$valid$"
                                          exact { hex_str: "0x1" }
                                        }
                                      }
                                      field_criteria {
                                        field_match {
                                          name: "vlan.$valid$"
                                          exact { hex_str: "0x0" }
                                        }
                                      }
                                    }
                                  )pb"),
                              ParseProtoOrDie<PacketSynthesisCriteria>(
                                  R"pb(
                                    input_packet_header_criteria {
                                      field_criteria {
                                        field_match {
                                          name: "vlan.$valid$"
                                          exact { hex_str: "0x1" }
                                        }
                                      }
                                    }
                                  )pb"),
                          });
}

TEST(GenerateSynthesisCriteriaTest,
     HeaderCoverageGoalWithIncludeWildcardHeaderYieldCorrectCriteriaList) {
  // Get a packet synthesizer object.
  ASSERT_OK_AND_ASSIGN(auto synthesizer,
                       PacketSynthesizer::Create(GetParams()));

  ASSERT_OK_AND_ASSIGN(
      auto criteria_list,
      GenerateSynthesisCriteriaFor(
          ParseProtoOrDie<CoverageGoals>(
              R"pb(
                coverage_goals {
                  header_coverage {
                    headers { patterns: [ "ipv4" ] }
                    headers_to_prevent_unless_explicitly_covered {
                      patterns: [ "vlan" ]
                    }
                    include_wildcard_header: true
                  }
                }
              )pb"),
          synthesizer->SolverState()));

  ExpectEqualCriteriaList(criteria_list,
                          {
                              ParseProtoOrDie<PacketSynthesisCriteria>(
                                  R"pb(
                                    input_packet_header_criteria {
                                      field_criteria {
                                        field_match {
                                          name: "vlan.$valid$"
                                          exact { hex_str: "0x0" }
                                        }
                                      }
                                    }
                                  )pb"),
                              ParseProtoOrDie<PacketSynthesisCriteria>(
                                  R"pb(
                                    input_packet_header_criteria {
                                      field_criteria {
                                        field_match {
                                          name: "ipv4.$valid$"
                                          exact { hex_str: "0x1" }
                                        }
                                      }
                                      field_criteria {
                                        field_match {
                                          name: "vlan.$valid$"
                                          exact { hex_str: "0x0" }
                                        }
                                      }
                                    }
                                  )pb"),
                          });
}

TEST(GenerateSynthesisCriteriaTest,
     CartesianProdCoverageWithHeaderAndEntryAndFateCoverageYieldsCorrectRes) {
  // Get a packet synthesizer object.
  ASSERT_OK_AND_ASSIGN(auto synthesizer,
                       PacketSynthesizer::Create(GetParams()));

  ASSERT_OK_AND_ASSIGN(
      auto criteria_list,
      GenerateSynthesisCriteriaFor(
          ParseProtoOrDie<CoverageGoals>(
              R"pb(
                coverage_goals {
                  cartesian_product_coverage {
                    header_coverage { headers { patterns: [ "ipv4", "ipv6" ] } }
                    packet_fate_coverage { fates: [ DROP, NOT_DROP ] }
                    entry_coverage { tables { patterns: [ "*" ] } }
                  }
                }
              )pb"),
          synthesizer->SolverState()));

  ExpectEqualCriteriaList(
      criteria_list,
      {
          ParseProtoOrDie<PacketSynthesisCriteria>(
              R"pb(
                input_packet_header_criteria {
                  field_criteria {
                    field_match {
                      name: "ipv4.$valid$"
                      exact { hex_str: "0x1" }
                    }
                  }
                }
                output_criteria { drop_expected: true }
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
                input_packet_header_criteria {
                  field_criteria {
                    field_match {
                      name: "ipv4.$valid$"
                      exact { hex_str: "0x1" }
                    }
                  }
                }
                output_criteria { drop_expected: false }
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
                input_packet_header_criteria {
                  field_criteria {
                    field_match {
                      name: "ipv6.$valid$"
                      exact { hex_str: "0x1" }
                    }
                  }
                }
                output_criteria { drop_expected: true }
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
                input_packet_header_criteria {
                  field_criteria {
                    field_match {
                      name: "ipv6.$valid$"
                      exact { hex_str: "0x1" }
                    }
                  }
                }
                output_criteria { drop_expected: false }
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
     CustomCritetiaCoverageGoalYieldsCorrectCriteriaList) {
  // Get a packet synthesizer object.
  ASSERT_OK_AND_ASSIGN(auto synthesizer,
                       PacketSynthesizer::Create(GetParams()));

  ASSERT_OK_AND_ASSIGN(
      auto criteria_list,
      GenerateSynthesisCriteriaFor(
          ParseProtoOrDie<CoverageGoals>(
              R"pb(
                coverage_goals {
                  custom_criteria_coverage {
                    criteria_list { output_criteria { drop_expected: true } }
                    criteria_list { output_criteria { drop_expected: false } }
                  }
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
     CartesianProdCoverageWithFateAndCustomCriteriaYieldsCorrectCriteriaList) {
  // Get a packet synthesizer object.
  ASSERT_OK_AND_ASSIGN(auto synthesizer,
                       PacketSynthesizer::Create(GetParams()));

  ASSERT_OK_AND_ASSIGN(
      auto criteria_list,
      GenerateSynthesisCriteriaFor(
          ParseProtoOrDie<CoverageGoals>(
              R"pb(
                coverage_goals {
                  cartesian_product_coverage {
                    packet_fate_coverage { fates: [ DROP, NOT_DROP ] }
                    custom_criteria_coverage {
                      criteria_list {
                        input_packet_header_criteria {
                          field_criteria {
                            field_match {
                              name: "ipv4.$valid$"
                              exact { hex_str: "0x1" }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              )pb"),
          synthesizer->SolverState()));

  ExpectEqualCriteriaList(criteria_list,
                          {
                              ParseProtoOrDie<PacketSynthesisCriteria>(
                                  R"pb(
                                    output_criteria { drop_expected: true }
                                    input_packet_header_criteria {
                                      field_criteria {
                                        field_match {
                                          name: "ipv4.$valid$"
                                          exact { hex_str: "0x1" }
                                        }
                                      }
                                    }
                                  )pb"),
                              ParseProtoOrDie<PacketSynthesisCriteria>(
                                  R"pb(
                                    output_criteria { drop_expected: false }
                                    input_packet_header_criteria {
                                      field_criteria {
                                        field_match {
                                          name: "ipv4.$valid$"
                                          exact { hex_str: "0x1" }
                                        }
                                      }
                                    }
                                  )pb"),
                          });
}

TEST(
    GenerateSynthesisCriteriaTest,
    CartesianProdCoverageWithHeaderAndCustomCriteriaYieldsCorrectCriteriaList) {
  // Get a packet synthesizer object.
  ASSERT_OK_AND_ASSIGN(auto synthesizer,
                       PacketSynthesizer::Create(GetParams()));

  ASSERT_OK_AND_ASSIGN(
      auto criteria_list,
      GenerateSynthesisCriteriaFor(
          ParseProtoOrDie<CoverageGoals>(
              R"pb(
                coverage_goals {
                  cartesian_product_coverage {
                    header_coverage { headers { patterns: [ "ipv4", "ipv6" ] } }
                    custom_criteria_coverage {
                      criteria_list {
                        input_packet_header_criteria {
                          field_criteria {
                            field_match {
                              name: "vlan.$valid$"
                              exact { hex_str: "0x1" }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              )pb"),
          synthesizer->SolverState()));

  ExpectEqualCriteriaList(criteria_list,
                          {
                              ParseProtoOrDie<PacketSynthesisCriteria>(
                                  R"pb(
                                    input_packet_header_criteria {
                                      field_criteria {
                                        field_match {
                                          name: "ipv4.$valid$"
                                          exact { hex_str: "0x1" }
                                        }
                                      }
                                      field_criteria {
                                        field_match {
                                          name: "vlan.$valid$"
                                          exact { hex_str: "0x1" }
                                        }
                                      }
                                    }
                                  )pb"),
                              ParseProtoOrDie<PacketSynthesisCriteria>(
                                  R"pb(
                                    input_packet_header_criteria {
                                      field_criteria {
                                        field_match {
                                          name: "ipv6.$valid$"
                                          exact { hex_str: "0x1" }
                                        }
                                      }
                                      field_criteria {
                                        field_match {
                                          name: "vlan.$valid$"
                                          exact { hex_str: "0x1" }
                                        }
                                      }
                                    }
                                  )pb"),
                          });
}

}  // namespace
}  // namespace p4_symbolic::packet_synthesizer
