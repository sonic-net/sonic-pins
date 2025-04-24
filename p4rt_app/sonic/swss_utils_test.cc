// Copyright 2025 Google LLC
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

#include "p4rt_app/sonic/swss_utils.h"

#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "swss/rediscommand.h"
#include "swss/schema.h"
#include "swss/table.h"

namespace p4rt_app {
namespace sonic {
namespace {
using gutil::IsOkAndHolds;
using gutil::StatusIs;

TEST(kfvEq, ReturnsTrueForSameObject) {
  swss::KeyOpFieldsValuesTuple kfv;
  kfvKey(kfv) = "kfv_key";
  kfvOp(kfv) = SET_COMMAND;
  kfvFieldsValues(kfv) = {
      {"field_a", "value_a"},
      {"field_b", "value_b"},
      {"field_c", "value_c"},
  };

  EXPECT_TRUE(kfvEq(kfv, kfv));
}

TEST(kfvEq, ReturnsFalseForDifferentKey) {
  swss::KeyOpFieldsValuesTuple kfv;
  kfvKey(kfv) = "kfv_key";
  kfvOp(kfv) = SET_COMMAND;
  kfvFieldsValues(kfv) = {
      {"field_a", "value_a"},
      {"field_b", "value_b"},
      {"field_c", "value_c"},
  };

  swss::KeyOpFieldsValuesTuple other_kfv = kfv;
  kfvKey(other_kfv) = "other_kfv_key";

  EXPECT_FALSE(kfvEq(kfv, other_kfv));
  EXPECT_FALSE(kfvEq(other_kfv, kfv));
}

TEST(kfvEq, ReturnsFalseForDifferentOperation) {
  swss::KeyOpFieldsValuesTuple kfv;
  kfvKey(kfv) = "kfv_key";
  kfvOp(kfv) = SET_COMMAND;
  kfvFieldsValues(kfv) = {
      {"field_a", "value_a"},
      {"field_b", "value_b"},
      {"field_c", "value_c"},
  };

  swss::KeyOpFieldsValuesTuple other_kfv = kfv;
  kfvOp(other_kfv) = DEL_COMMAND;

  EXPECT_FALSE(kfvEq(kfv, other_kfv));
  EXPECT_FALSE(kfvEq(other_kfv, kfv));
}

TEST(kfvEq, ReturnsFalseForDifferentFieldCount) {
  swss::KeyOpFieldsValuesTuple kfv;
  kfvKey(kfv) = "kfv_key";
  kfvOp(kfv) = SET_COMMAND;
  kfvFieldsValues(kfv) = {
      {"field_a", "value_a"},
      {"field_b", "value_b"},
      {"field_c", "value_c"},
  };

  swss::KeyOpFieldsValuesTuple other_kfv = kfv;
  kfvFieldsValues(other_kfv).push_back({"field_c", "value_c"});

  EXPECT_FALSE(kfvEq(kfv, other_kfv));
  EXPECT_FALSE(kfvEq(other_kfv, kfv));
}

TEST(kfvEq, ReturnsFalseForDifferentField) {
  swss::KeyOpFieldsValuesTuple kfv;
  kfvKey(kfv) = "kfv_key";
  kfvOp(kfv) = SET_COMMAND;
  kfvFieldsValues(kfv) = {
      {"field_a", "value_a"},
      {"field_b", "value_b"},
      {"field_c", "value_c"},
  };

  swss::KeyOpFieldsValuesTuple other_kfv = kfv;
  kfvFieldsValues(other_kfv)[1].first = "field_d";

  EXPECT_FALSE(kfvEq(kfv, other_kfv));
  EXPECT_FALSE(kfvEq(other_kfv, kfv));
}

TEST(kfvEq, ReturnsFalseForDifferentValue) {
  swss::KeyOpFieldsValuesTuple kfv;
  kfvKey(kfv) = "kfv_key";
  kfvOp(kfv) = SET_COMMAND;
  kfvFieldsValues(kfv) = {
      {"field_a", "value_a"},
      {"field_b", "value_b"},
      {"field_c", "value_c"},
  };

  swss::KeyOpFieldsValuesTuple other_kfv = kfv;
  kfvFieldsValues(other_kfv)[1].second = "value_d";

  EXPECT_FALSE(kfvEq(kfv, other_kfv));
  EXPECT_FALSE(kfvEq(other_kfv, kfv));
}

TEST(kfvEq, ReturnsFalseForDifferentFieldValuePair) {
  swss::KeyOpFieldsValuesTuple kfv;
  kfvKey(kfv) = "kfv_key";
  kfvOp(kfv) = SET_COMMAND;
  kfvFieldsValues(kfv) = {
      {"field_a", "value_a"},
      {"field_b", "value_b"},
      {"field_c", "value_c"},
  };

  swss::KeyOpFieldsValuesTuple other_kfv = kfv;
  kfvFieldsValues(other_kfv)[1] = {"field_d", "value_d"};

  EXPECT_FALSE(kfvEq(kfv, other_kfv));
  EXPECT_FALSE(kfvEq(other_kfv, kfv));
}

TEST(kfvFieldLookup, ReturnsTheFieldValue) {
  swss::KeyOpFieldsValuesTuple kfv;
  kfvKey(kfv) = "kfv_key";
  kfvOp(kfv) = SET_COMMAND;
  kfvFieldsValues(kfv) = {
      {"field_a", "value_a"},
      {"field_b", "value_b"},
      {"field_d", "value_d"},
      {"field_c", "value_c"},
  };

  ASSERT_THAT(kfvFieldLookup(kfv, "field_a"), IsOkAndHolds("value_a"));
  ASSERT_THAT(kfvFieldLookup(kfv, "field_b"), IsOkAndHolds("value_b"));
  ASSERT_THAT(kfvFieldLookup(kfv, "field_c"), IsOkAndHolds("value_c"));
  ASSERT_THAT(kfvFieldLookup(kfv, "field_d"), IsOkAndHolds("value_d"));
}

TEST(kfvFieldLookup, ReturnsNotFoundForNonexistentField) {
  swss::KeyOpFieldsValuesTuple kfv;
  kfvKey(kfv) = "kfv_key";
  kfvOp(kfv) = SET_COMMAND;
  kfvFieldsValues(kfv) = {
      {"field_a", "value_a"},
      {"field_b", "value_b"},
      {"field_c", "value_c"},
  };

  EXPECT_THAT(kfvFieldLookup(kfv, "field_d"),
              StatusIs(absl::StatusCode::kNotFound));
}

}  // namespace
}  // namespace sonic
}  // namespace p4rt_app
