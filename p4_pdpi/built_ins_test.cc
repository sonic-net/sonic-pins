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

TEST(IrBuitInField, AllFieldsSupportedAndRoundTrip) {
  for (int i = IrBuiltInField_MIN; i <= IrBuiltInField_MAX; ++i) {
    // Skip unknown and default value of UNSPECIFIED.
    if (!IrBuiltInField_IsValid(i) || i == 0) continue;
    IrBuiltInField built_in_field = static_cast<IrBuiltInField>(i);
    ASSERT_OK_AND_ASSIGN(std::string built_in_string,
                         IrBuiltInFieldToString(built_in_field));
    ASSERT_OK_AND_ASSIGN(IrBuiltInField roundtrip_built_in_field,
                         StringToIrBuiltInField(built_in_string));
    EXPECT_EQ(built_in_field, roundtrip_built_in_field);
  }
}

}  // namespace
}  // namespace pdpi
