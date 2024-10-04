// Copyright 2021 Google LLC
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
#include "p4_fuzzer/switch_state.h"

#include <cstdint>

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/substitute.h"
#include "glog/logging.h"
#include "gtest/gtest.h"
#include "gutil/collections.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_fuzzer/test_utils.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/testing/test_p4info.h"
#include "p4_pdpi/testing/main_p4_pd.pb.h"
#include "p4_pdpi/pd.h"

namespace p4_fuzzer {
namespace {

using ::p4::config::v1::P4Info;
using ::p4::config::v1::Preamble;
using ::p4::config::v1::Table;
using ::p4::v1::TableEntry;
using ::p4::v1::Update;
using ::pdpi::CreateIrP4Info;
using ::pdpi::IrP4Info;
using ::testing::StrEq;

// All P4Runtime table IDs must have their most significant byte equal to this
// value.
constexpr uint32_t kTableIdMostSignificantByte = 0x02'00'00'00;

TEST(SwitchStateTest, TableEmptyTrivial) {
  IrP4Info info;
  SwitchState state(info);

  EXPECT_TRUE(state.AllTablesEmpty());
}

TEST(SwitchStateTest, TableEmptyFromP4Info) {
  P4Info info;
  Table* ptable = info.add_tables();
  ptable->mutable_preamble()->set_id(42);

  IrP4Info ir_info = CreateIrP4Info(info).value();

  SwitchState state(ir_info);
  EXPECT_TRUE(state.AllTablesEmpty());
}

TEST(SwitchStateTest, RuleInsert) {
  P4Info info;
  Table* ptable = info.add_tables();
  Preamble* preamble = ptable->mutable_preamble();
  preamble->set_id(42);
  preamble->set_alias("Spam");

  ptable = info.add_tables();
  preamble = ptable->mutable_preamble();
  preamble->set_id(43);
  preamble->set_alias("Eggs");

  IrP4Info ir_info = CreateIrP4Info(info).value();

  SwitchState state(ir_info);

  Update update;
  update.set_type(Update::INSERT);

  TableEntry* entry = update.mutable_entity()->mutable_table_entry();
  entry->set_table_id(42);

  ASSERT_OK(state.ApplyUpdate(update));

  EXPECT_FALSE(state.AllTablesEmpty());
  EXPECT_FALSE(state.IsTableEmpty(42));
  EXPECT_TRUE(state.IsTableEmpty(43));

  EXPECT_EQ(state.GetNumTableEntries(42), 1);
  EXPECT_EQ(state.GetNumTableEntries(43), 0);

  EXPECT_EQ(state.GetTableEntries(42).size(), 1);
  EXPECT_EQ(state.GetTableEntries(43).size(), 0);

  state.ClearTableEntries();
  EXPECT_TRUE(state.AllTablesEmpty());
}

TEST(SwitchStateTest, ClearTableEntriesPreservesP4Info) {
  const IrP4Info p4info = pdpi::GetTestIrP4Info();
  SwitchState state(p4info);
  EXPECT_THAT(state.GetIrP4Info(), gutil::EqualsProto(p4info));

  state.ClearTableEntries();
  EXPECT_THAT(state.GetIrP4Info(), gutil::EqualsProto(p4info));
}

TEST(SwitchStateTest, RuleDelete) {
  P4Info info;
  Table* ptable = info.add_tables();
  Preamble* preamble = ptable->mutable_preamble();
  preamble->set_id(42);
  preamble->set_alias("Spam");

  ptable = info.add_tables();
  preamble = ptable->mutable_preamble();
  preamble->set_id(43);
  preamble->set_alias("Eggs");

  IrP4Info ir_info = CreateIrP4Info(info).value();

  SwitchState state(ir_info);

  Update update;
  update.set_type(Update::INSERT);

  TableEntry* entry = update.mutable_entity()->mutable_table_entry();
  entry->set_table_id(42);

  ASSERT_OK(state.ApplyUpdate(update));

  update.set_type(Update::DELETE);
  ASSERT_OK(state.ApplyUpdate(update));

  EXPECT_TRUE(state.AllTablesEmpty());

  EXPECT_EQ(state.GetNumTableEntries(42), 0);
  EXPECT_EQ(state.GetTableEntries(42).size(), 0);
}

Update MakePiUpdate(const pdpi::IrP4Info& info, Update::Type type,
                    const pdpi::TableEntry& entry) {
  pdpi::Update pd;
  pd.set_type(type);
  *pd.mutable_table_entry() = entry;
  auto pi = pdpi::PdUpdateToPi(info, pd);
  CHECK_OK(pi.status());  // Crash ok
  return *pi;
}

TEST(SwitchStateTest, SetTableEntriesSetsTableEntries) {
  // Initialize state.
  SwitchState state(pdpi::GetTestIrP4Info());
  EXPECT_TRUE(state.AllTablesEmpty());
  constexpr uint32_t kTableId1 = 1 | kTableIdMostSignificantByte;
  constexpr uint32_t kTableId2 = 2 | kTableIdMostSignificantByte;

  // Call SetTableEntries and ensure it indeed populates the correct tables.
  std::vector<p4::v1::TableEntry> entries;
  entries.emplace_back().set_table_id(kTableId1);  // Entry #1 in table 1.
  entries.emplace_back().set_table_id(kTableId2);  // Entry #1 in table 2.
  entries.emplace_back() =                         // Entry #2 in table 1.
      gutil::ParseProtoOrDie<p4::v1::TableEntry>(
          absl::Substitute(R"pb(
                             table_id: $0
                             match {
                               field_id: 1
                               exact { value: "second entry in table 1" }
                             }
                           )pb",
                           kTableId1));
  ASSERT_OK(state.SetTableEntries(entries))
      << " with the following P4Info:\n " << state.GetIrP4Info().DebugString();
  EXPECT_EQ(state.GetNumTableEntries(kTableId1), 2);
  EXPECT_EQ(state.GetNumTableEntries(kTableId2), 1);
  EXPECT_EQ(state.GetNumTableEntries(), 3);

  state.ClearTableEntries();
  EXPECT_EQ(state.GetNumTableEntries(kTableId1), 0);
  EXPECT_EQ(state.GetNumTableEntries(kTableId2), 0);
  EXPECT_EQ(state.GetNumTableEntries(), 0);
  EXPECT_TRUE(state.AllTablesEmpty());
}

TEST(SwitchStateTest, SetTableEntriesFailsForUnknownTableIds) {
  SwitchState state(pdpi::GetTestIrP4Info());
  EXPECT_THAT(
      state.SetTableEntries(std::vector{
          gutil::ParseProtoOrDie<p4::v1::TableEntry>("table_id: 123456789")}),
      gutil::StatusIs(absl::StatusCode::kInvalidArgument));
}

}  // namespace
}  // namespace p4_fuzzer
