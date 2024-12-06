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
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/pd.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/symbolic/values.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_nonstandard_platforms.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

namespace p4_symbolic {
namespace {

TEST(EvaluateSaiPipeline,
     SatisfiableForAllInstantiationsWithEmptyEntriesAndPorts) {
  for (auto instantiation : sai::AllSaiInstantiations()) {
    const auto config = sai::GetNonstandardForwardingPipelineConfig(
        instantiation, sai::NonstandardPlatform::kP4Symbolic);
    ASSERT_OK_AND_ASSIGN(
        auto state, EvaluateSaiPipeline(config, /*entries=*/{}, /*ports=*/{}));
    EXPECT_EQ(state->solver->check(), z3::check_result::sat);
  }
}

TEST(EvaluateSaiPipeline, FailsForInconsistentPortAndPortIdTypeTranslation) {
  const auto config = sai::GetNonstandardForwardingPipelineConfig(
      sai::Instantiation::kFabricBorderRouter,
      sai::NonstandardPlatform::kP4Symbolic);
  symbolic::TranslationPerType translations;
  translations[kPortIdTypeName] = symbolic::values::TranslationData{
      .static_mapping = {{"a", 1}, {"b", 2}},
      .dynamic_translation = false,
  };
  absl::StatusOr<std::unique_ptr<symbolic::SolverState>> state =
      EvaluateSaiPipeline(config, /*entries=*/{}, /*ports=*/{1, 2, 3},
                          translations);
  ASSERT_THAT(state.status(),
              gutil::StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(EvaluateSaiPipeline, PassForConsistentPortAndPortIdTypeTranslation) {
  const auto config = sai::GetNonstandardForwardingPipelineConfig(
      sai::Instantiation::kFabricBorderRouter,
      sai::NonstandardPlatform::kP4Symbolic);
  symbolic::TranslationPerType translations;
  translations[kPortIdTypeName] = symbolic::values::TranslationData{
      .static_mapping = {{"a", 1}, {"b", 2}},
      .dynamic_translation = false,
  };
  absl::StatusOr<std::unique_ptr<symbolic::SolverState>> state =
      EvaluateSaiPipeline(config, /*entries=*/{}, /*ports=*/{1, 2},
                          translations);
  ASSERT_OK(state.status());
  EXPECT_EQ((*state)->solver->check(), z3::check_result::sat);
}

TEST(EvaluateSaiPipeline, FailsIfInputContainsTranslationForVrfIdType) {
  const auto config = sai::GetNonstandardForwardingPipelineConfig(
      sai::Instantiation::kFabricBorderRouter,
      sai::NonstandardPlatform::kP4Symbolic);
  symbolic::TranslationPerType translations;
  translations[kVrfIdTypeName] = symbolic::values::TranslationData{};
  absl::StatusOr<std::unique_ptr<symbolic::SolverState>> state =
      EvaluateSaiPipeline(config, /*entries=*/{}, /*ports=*/{}, translations);
  ASSERT_THAT(state.status(),
              gutil::StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(EvaluateSaiPipeline, IngressPortIsAmongPassedValues) {
  // Get config.
  const auto config = sai::GetNonstandardForwardingPipelineConfig(
      sai::Instantiation::kFabricBorderRouter,
      sai::NonstandardPlatform::kP4Symbolic);
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(config.p4info()));

  // Note: We need to install a table entry with the given translated field (in
  // this case, local_metadata.ingress_port) for P4Symbolic to understand that
  // the field is a translated type.
  auto pd_entries = gutil::ParseProtoOrDie<sai::TableEntries>(
      R"pb(entries {
             acl_pre_ingress_table_entry {
               match { in_port { value: "b" } }
               action { set_vrf { vrf_id: "vrf-80" } }
               priority: 1
             }
           })pb");
  std::vector<p4::v1::TableEntry> pi_entries;
  for (auto& pd_entry : pd_entries.entries()) {
    ASSERT_OK_AND_ASSIGN(pi_entries.emplace_back(),
                         pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, pd_entry));
  }

  // Evaluate the SAI pipeline.
  symbolic::TranslationPerType translations;
  translations[kPortIdTypeName] = symbolic::values::TranslationData{
      .static_mapping = {{"a", 1}, {"b", 2}},
      .dynamic_translation = false,
  };
  absl::StatusOr<std::unique_ptr<symbolic::SolverState>> state =
      EvaluateSaiPipeline(config, pi_entries, /*ports=*/{1, 2}, translations);
  ASSERT_OK(state.status());

  // Check local_metadata.ingress_port value.
  EXPECT_EQ((*state)->solver->check(), z3::check_result::sat);
  ASSERT_OK_AND_ASSIGN(const std::string local_metadata_ingress_port,
                       ExtractLocalMetadataIngressPortFromModel(**state));
  ASSERT_THAT(local_metadata_ingress_port,
              testing::AnyOf(testing::Eq("a"), testing::Eq("b")));
}

}  // namespace
}  // namespace p4_symbolic
