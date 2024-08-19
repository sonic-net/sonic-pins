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

#include "p4_pdpi/built_ins.h"

#include <string>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"  // IWYU pragma: keep
#include "p4_pdpi/ir.pb.h"

namespace pdpi {
namespace {

TEST(IrBuitInTable, AllTablesSupportedAndRoundTrip) {
  for (int i = IrBuiltInTable_MIN; i <= IrBuiltInTable_MAX; ++i) {
    // Skip unknown and default value of UNSPECIFIED.
    if (!IrBuiltInTable_IsValid(i) || i == 0) continue;
    IrBuiltInTable built_in_table = static_cast<IrBuiltInTable>(i);
    ASSERT_OK_AND_ASSIGN(std::string built_in_string,
                         IrBuiltInTableToString(built_in_table));
    ASSERT_TRUE(IsBuiltInTable(built_in_string));
    ASSERT_OK_AND_ASSIGN(IrBuiltInTable roundtrip_built_in_table,
                         StringToIrBuiltInTable(built_in_string));
    EXPECT_EQ(built_in_table, roundtrip_built_in_table);
  }
}

TEST(IrBuiltInMatchField, AllMatchFieldsSupportedAndRoundTrip) {
  for (int i = IrBuiltInMatchField_MIN; i <= IrBuiltInMatchField_MAX; ++i) {
    // Skip unknown and default value of UNSPECIFIED.
    if (!IrBuiltInMatchField_IsValid(i) || i == 0) continue;
    IrBuiltInMatchField built_in_field = static_cast<IrBuiltInMatchField>(i);
    ASSERT_OK_AND_ASSIGN(std::string built_in_string,
                         IrBuiltInMatchFieldToString(built_in_field));
    ASSERT_OK_AND_ASSIGN(IrBuiltInMatchField roundtrip_built_in_field,
                         StringToIrBuiltInMatchField(built_in_string));
    EXPECT_EQ(built_in_field, roundtrip_built_in_field);
  }
}

TEST(IrBuiltInAction, AllActionsSupportedAndRoundTrip) {
  for (int i = IrBuiltInAction_MIN; i <= IrBuiltInAction_MAX; ++i) {
    // Skip unknown and default value of UNSPECIFIED.
    if (!IrBuiltInAction_IsValid(i) || i == 0) continue;
    IrBuiltInAction built_in_action = static_cast<IrBuiltInAction>(i);
    ASSERT_OK_AND_ASSIGN(std::string built_in_string,
                         IrBuiltInActionToString(built_in_action));
    ASSERT_TRUE(IsBuiltInAction(built_in_string));
    ASSERT_OK_AND_ASSIGN(IrBuiltInAction roundtrip_built_in_action,
                         StringToIrBuiltInAction(built_in_string));
    EXPECT_EQ(built_in_action, roundtrip_built_in_action);
  }
}

TEST(IrBuiltInParameter, AllParametersSupportedAndRoundTrip) {
  for (int i = IrBuiltInParameter_MIN; i <= IrBuiltInParameter_MAX; ++i) {
    // Skip unknown and default value of UNSPECIFIED.
    if (!IrBuiltInParameter_IsValid(i) || i == 0) continue;
    IrBuiltInParameter built_in_parameter = static_cast<IrBuiltInParameter>(i);
    ASSERT_OK_AND_ASSIGN(std::string built_in_string,
                         IrBuiltInParameterToString(built_in_parameter));
    ASSERT_OK_AND_ASSIGN(IrBuiltInParameter roundtrip_built_in_parameter,
                         StringToIrBuiltInParameter(built_in_string));
    EXPECT_EQ(built_in_parameter, roundtrip_built_in_parameter);
  }
}

TEST(IrBuiltInParameter, AllParametersHaveAnAction) {
  for (int i = IrBuiltInParameter_MIN; i <= IrBuiltInParameter_MAX; ++i) {
    // Skip unknown and default value of UNSPECIFIED.
    if (!IrBuiltInParameter_IsValid(i) || i == 0) continue;
    EXPECT_OK(GetBuiltInActionFromBuiltInParameter(
        static_cast<IrBuiltInParameter>(i)));
  }
}

}  // namespace
}  // namespace pdpi
