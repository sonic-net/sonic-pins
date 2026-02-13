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

#include "p4_symbolic/symbolic/util.h"

#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4_symbolic/ir/ir.pb.h"

namespace p4_symbolic::symbolic::util {
namespace {

TEST(GetFieldBitwidthTest, FailsForSyntacticallyIncorrectInput) {
  ir::P4Program program;
  ASSERT_THAT(GetFieldBitwidth("a.b.c.d", program),
              gutil::StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(GetFieldBitwidthTest, FailsForNonExistingHeader) {
  ir::P4Program program;
  ASSERT_THAT(GetFieldBitwidth("dummy_header.dummy_field", program),
              gutil::StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(GetFieldBitwidthTest, FailsForNonExistingField) {
  ir::P4Program program;
  (*program.mutable_headers())["dummy_header"] = ir::HeaderType();
  ASSERT_THAT(GetFieldBitwidth("dummy_header.dummy_field", program),
              gutil::StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(GetFieldBitwidthTest, YieldCorrectFieldBitwidth) {
  auto program = gutil::ParseProtoOrDie<ir::P4Program>(R"pb(
    headers {
      key: "dummy_header"
      value {
        fields {
          key: "dummy_field"
          value { bitwidth: 10 }
        }
      }
    })pb");
  ASSERT_THAT(GetFieldBitwidth("dummy_header.dummy_field", program),
              gutil::IsOkAndHolds(testing::Eq(10)));
}

}  // namespace
}  // namespace p4_symbolic::symbolic::util
