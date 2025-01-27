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
#include "p4_symbolic/sai/sai.h"

#include <memory>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/test_artifact_writer.h"
#include "gutil/gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/pd.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/symbolic/values.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_nonstandard_platforms.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "z3++.h"

namespace p4_symbolic {
namespace {

TEST(SaiTranslationChecks, NoErrorWithEmptyPortsAndTranslation) {
  EXPECT_OK(CheckPhysicalPortAndPortIdTypeValueConsistency(
      /*physical_ports=*/{},
      /*translation_per_type=*/{}));

  symbolic::TranslationPerType translations;
  EXPECT_OK(AddVrfIdTypeTranslation(translations));
  EXPECT_EQ(translations.size(), 1);
  ASSERT_TRUE(translations.contains(kVrfIdTypeName));
  std::vector<std::pair<std::string, uint64_t>> expected_static_mapping{
      {"", 0}};
  EXPECT_EQ(translations.at(kVrfIdTypeName).static_mapping,
            expected_static_mapping);
  EXPECT_TRUE(translations.at(kVrfIdTypeName).dynamic_translation);
}

TEST(SaiTranslationChecks, FailsForInconsistentPortAndPortIdTypeTranslation) {
  std::vector<int> ports{1, 2, 3};
  symbolic::TranslationPerType translations;
  translations[kPortIdTypeName] = symbolic::values::TranslationData{
      .static_mapping = {{"a", 1}, {"b", 2}},
      .dynamic_translation = false,
  };
  EXPECT_THAT(
      CheckPhysicalPortAndPortIdTypeValueConsistency(ports, translations),
      gutil::StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(SaiTranslationChecks, PassForConsistentPortAndPortIdTypeTranslation) {
  std::vector<int> ports{1, 2};
  symbolic::TranslationPerType translations;
  translations[kPortIdTypeName] = symbolic::values::TranslationData{
      .static_mapping = {{"a", 1}, {"b", 2}},
      .dynamic_translation = false,
  };
  EXPECT_OK(
      CheckPhysicalPortAndPortIdTypeValueConsistency(ports, translations));
}

TEST(SaiTranslationChecks, FailsIfInputContainsTranslationForVrfIdType) {
  symbolic::TranslationPerType translations;
  translations[kVrfIdTypeName] = symbolic::values::TranslationData{};
  EXPECT_THAT(AddVrfIdTypeTranslation(translations),
              gutil::StatusIs(absl::StatusCode::kInvalidArgument));
}

using GetLocalMetadataIngressPortFromModelTest =
    testing::TestWithParam<sai::Instantiation>;

TEST_P(GetLocalMetadataIngressPortFromModelTest,
       IngressPortIsAmongPassedValues) {
  //  Get config.
  const auto config = sai::GetNonstandardForwardingPipelineConfig(
      /*instantiation=*/GetParam(), sai::NonstandardPlatform::kP4Symbolic);

  gutil::BazelTestArtifactWriter artifact_writer;
  ASSERT_OK(artifact_writer.StoreTestArtifact(
      "p4info.textproto", gutil::PrintTextProto(config.p4info())));
  ASSERT_OK(artifact_writer.StoreTestArtifact("bmv2.json",
                                              config.p4_device_config()));

  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(config.p4info()));

  // Note: We need to install a table entry with the given translated field
  // (in this case, local_metadata.ingress_port) for P4Symbolic to understand
  // that the field is a translated type.
  auto pd_entries = gutil::ParseProtoOrDie<sai::TableEntries>(
      R"pb(entries {
             acl_pre_ingress_table_entry {
               match { in_port { value: "b" } }
               action { set_vrf { vrf_id: "vrf-80" } }
               priority: 1
             }
           })pb");
  ASSERT_OK_AND_ASSIGN(std::vector<p4::v1::Entity> pi_entities,
                       pdpi::PdTableEntriesToPiEntities(ir_p4info, pd_entries));

  symbolic::TranslationPerType translations;
  translations[kPortIdTypeName] = symbolic::values::TranslationData{
      .static_mapping = {{"a", 1}, {"b", 2}},
      .dynamic_translation = false,
  };

  // Evaluate the SAI pipeline.
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<symbolic::SolverState> state,
      symbolic::EvaluateP4Program(config, pi_entities, /*ports=*/{1, 2},
                                  translations));

  // Check local_metadata.ingress_port value.
  EXPECT_EQ(state->solver->check(), z3::check_result::sat);
  ASSERT_OK_AND_ASSIGN(const std::string local_metadata_ingress_port,
                       GetLocalMetadataIngressPortFromModel(*state));
  EXPECT_THAT(local_metadata_ingress_port,
              testing::AnyOf(testing::Eq("a"), testing::Eq("b")));
}

INSTANTIATE_TEST_SUITE_P(
    GetLocalMetadataIngressPortFromModelTests,
    GetLocalMetadataIngressPortFromModelTest,
    testing::ValuesIn(sai::AllSaiInstantiations()),
    [](const testing::TestParamInfo<sai::Instantiation>& info) -> std::string {
      return sai::InstantiationToString(info.param);
    });

}  // namespace
}  // namespace p4_symbolic
