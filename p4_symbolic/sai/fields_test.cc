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
#include "p4_symbolic/sai/fields.h"

#include <memory>
#include <vector>

#include "absl/status/statusor.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "p4_symbolic/sai/sai.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_nonstandard_platforms.h"

namespace p4_symbolic {
namespace {

TEST(GetSaiFields, CanGetIngressAndEgressFieldsForAllInstantiations) {
  for (auto instantiation : sai::AllSaiInstantiations()) {
    const auto config = sai::GetNonstandardForwardingPipelineConfig(
        instantiation, sai::NonstandardPlatform::kP4Symbolic);
    ASSERT_OK_AND_ASSIGN(
        auto state, EvaluateSaiPipeline(config, /*entries=*/{}, /*ports=*/{}));
    for (auto& headers :
         {state->context.ingress_headers, state->context.egress_headers}) {
      EXPECT_OK(GetSaiFields(headers).status());
    }
  }
}

TEST(GetUserMetadataFieldNameTest, FailsForNonExistingFields) {
  const auto config = sai::GetNonstandardForwardingPipelineConfig(
      sai::Instantiation::kMiddleblock, sai::NonstandardPlatform::kP4Symbolic);
  ASSERT_OK_AND_ASSIGN(
      auto state, EvaluateSaiPipeline(config, /*entries=*/{}, /*ports=*/{}));
  ASSERT_THAT(GetUserMetadataFieldName("dummy_nonexisting_field",
                                       state->context.ingress_headers),
              gutil::StatusIs(absl::StatusCode::kInternal));
}

}  // namespace
}  // namespace p4_symbolic
