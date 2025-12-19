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

#include "sai_p4/instantiations/google/test_tools/table_entry_generator.h"

#include <algorithm>
#include <cstdint>
#include <string>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/entity_keys.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/pd.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

namespace sai {
namespace {

struct TestParam {
  sai::Instantiation instantiation;
  std::string table_name;
};

std::vector<TestParam> TestParams() {
  std::vector<TestParam> params;
  for (sai::Instantiation instantiation : sai::AllSaiInstantiations()) {
    pdpi::IrP4Info ir_p4info = sai::GetIrP4Info(instantiation);
    for (const auto& [table_name, table] : ir_p4info.tables_by_name()) {
      params.push_back({instantiation, table_name});
    }
  }
  return params;
}

class GeneratorTest : public testing::TestWithParam<TestParam> {};

TEST_P(GeneratorTest, GeneratesEntriesOrReturnsUnimplemented) {
  pdpi::IrP4Info ir_p4info = sai::GetIrP4Info(GetParam().instantiation);
  const std::string& table_name = GetParam().table_name;
  const pdpi::IrTableDefinition& table =
      ir_p4info.tables_by_name().at(table_name);

  auto generator = GetGenerator(table);
  if (generator.status().code() == absl::StatusCode::kUnimplemented) {
    GTEST_SKIP() << "Generator for table " << table_name
                 << " is known and unimplemented.";
  }
  ASSERT_OK(generator);
}

TEST_P(GeneratorTest, GeneratesValidPrerequisites) {
  pdpi::IrP4Info ir_p4info = sai::GetIrP4Info(GetParam().instantiation);
  const std::string& table_name = GetParam().table_name;
  const pdpi::IrTableDefinition& table =
      ir_p4info.tables_by_name().at(table_name);
  auto generator = GetGenerator(table);
  if (generator.status().code() == absl::StatusCode::kUnimplemented) {
    GTEST_SKIP() << "Generator for table " << table_name
                 << " is known and unimplemented.";
  }
  ASSERT_OK(generator);
  if (generator->prerequisites.empty()) {
    GTEST_SKIP() << "Generator for table " << table_name
                 << " has no prerequisites.";
  }

  for (const pdpi::IrTableEntry& prerequisite : generator->prerequisites) {
    sai::TableEntry pd_table_entry;
    SCOPED_TRACE(absl::StrCat("Invalid prerequisite IrTableEntry: ",
                              prerequisite.ShortDebugString()));
    EXPECT_OK(pdpi::IrTableEntryToPd(ir_p4info, prerequisite, &pd_table_entry));
    EXPECT_OK(pdpi::IrTableEntryToPi(ir_p4info, prerequisite));
  }
}

// Test sanity and uniqueness for each generated table entry. Go above the
// table size to ensure we can test for 'real capacity'.
TEST_P(GeneratorTest, GeneratesValidEntries) {
  pdpi::IrP4Info ir_p4info = sai::GetIrP4Info(GetParam().instantiation);
  const std::string& table_name = GetParam().table_name;
  const pdpi::IrTableDefinition& table =
      ir_p4info.tables_by_name().at(table_name);
  auto generator = GetGenerator(table);
  if (generator.status().code() == absl::StatusCode::kUnimplemented) {
    GTEST_SKIP() << "Generator for table " << table_name
                 << " is known and unimplemented.";
  }
  ASSERT_OK(generator);

  absl::flat_hash_map<pdpi::TableEntryKey, int> generated_keys;
  for (int i = 0;
       i <= std::min(2 * table.size(), static_cast<int64_t>(INT32_MAX - 1));
       ++i) {
    SCOPED_TRACE(absl::StrCat("Failed to generate entry at index ", i));
    pdpi::IrTableEntry ir_table_entry = generator->generator(i);
    ASSERT_EQ(ir_table_entry.table_name(), table_name);
    sai::TableEntry pd_table_entry;
    EXPECT_OK(
        pdpi::IrTableEntryToPd(ir_p4info, ir_table_entry, &pd_table_entry));
    ASSERT_OK_AND_ASSIGN(p4::v1::TableEntry p4_table_entry,
                         pdpi::IrTableEntryToPi(ir_p4info, ir_table_entry));

    pdpi::TableEntryKey key(p4_table_entry);
    ASSERT_FALSE(generated_keys.contains(key))
        << "Table entry key overlaps between entries " << generated_keys.at(key)
        << " and " << i << ". Entry: " << ir_table_entry.ShortDebugString();
    generated_keys.insert_or_assign(key, i);
  }
}

INSTANTIATE_TEST_SUITE_P(
    TableEntry, GeneratorTest, testing::ValuesIn(TestParams()),
    [](const testing::TestParamInfo<TestParam>& info) {
      return absl::StrCat(
          gutil::SnakeCaseToCamelCase(
              sai::InstantiationToString(info.param.instantiation)),
          gutil::SnakeCaseToCamelCase(info.param.table_name));
    });

}  // namespace
}  // namespace sai
