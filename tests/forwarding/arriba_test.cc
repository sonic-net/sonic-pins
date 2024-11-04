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

#include "tests/forwarding/arriba_test.h"

#include "dvaas/arriba_test_vector_validation.h"
#include "dvaas/mirror_testbed_config.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "p4_pdpi/p4_runtime_session.h"

namespace pins_test {
namespace {

TEST_P(ArribaTest, SwitchUnderTestPassesArribaTestVector) {
  ASSERT_OK_AND_ASSIGN(
      dvaas::MirrorTestbedConfigurator configured_testbed,
      dvaas::MirrorTestbedConfigurator::Create(GetParam().mirror_testbed));

  ASSERT_OK(configured_testbed.ConfigureForForwardingTest());

  EXPECT_OK(dvaas::ValidateAgaistArribaTestVector(
      *configured_testbed.SutApi().p4rt,
      *configured_testbed.ControlSwitchApi().p4rt,
      GetParam().arriba_test_vector));

  ASSERT_OK(configured_testbed.RestoreToOriginalConfiguration());
}

}  // namespace
}  // namespace pins_test
