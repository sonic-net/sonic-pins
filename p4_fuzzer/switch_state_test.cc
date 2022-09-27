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
#include "absl/types/optional.h"
#include "glog/logging.h"
#include "gtest/gtest.h"
#include "gutil/collections.h"
#include "gutil/proto.h"
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

using ::gutil::EqualsProto;
using ::p4::config::v1::P4Info;
using ::p4::config::v1::Preamble;
using ::p4::config::v1::Table;
using ::p4::v1::TableEntry;
using ::p4::v1::Update;
using ::pdpi::CreateIrP4Info;
using ::pdpi::IrP4Info;
using ::testing::Not;
using ::testing::Optional;

// All P4Runtime table IDs must have their most significant byte equal to this
// value.
constexpr uint32_t kTableIdMostSignificantByte = 0x02'00'00'00;
constexpr uint32_t kBareTable1 = 1;
constexpr uint32_t kBareTable2 = 2;
constexpr uint32_t kSpamTableId = 41;
constexpr uint32_t kEggTableId = 42;

IrP4Info GetIrP4Info() {
  P4Info info;

  Table* bare_table_1 = info.add_tables();
  Preamble* preamble = bare_table_1->mutable_preamble();
  preamble->set_id(kBareTable1);
  preamble->set_alias("bare_table_1");

  Table* bare_table_2 = info.add_tables();
  preamble = bare_table_2->mutable_preamble();
  preamble->set_id(kBareTable2);
  preamble->set_alias("bare_table_2");

  Table* spam_table = info.add_tables();
  preamble = spam_table->mutable_preamble();
  preamble->set_id(kSpamTableId);
  preamble->set_alias("spam_table");
  p4::config::v1::MatchField* match_field =
      spam_table->mutable_match_fields()->Add();
  match_field->set_id(1);
  match_field->set_name("field1");
  match_field->set_bitwidth(32);
  match_field->set_match_type(p4::config::v1::MatchField::EXACT);

  Table* egg_table = info.add_tables();
  preamble = egg_table->mutable_preamble();
  preamble->set_id(kEggTableId);
  preamble->set_alias("egg_table");

  return CreateIrP4Info(info).value();
}

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
  SwitchState state(GetIrP4Info());

  Update update;
  update.set_type(Update::INSERT);

  TableEntry* entry = update.mutable_entity()->mutable_table_entry();
  entry->set_table_id(kBareTable1);

  ASSERT_OK(state.ApplyUpdate(update));

  EXPECT_FALSE(state.AllTablesEmpty());
  EXPECT_FALSE(state.IsTableEmpty(kBareTable1));
  EXPECT_TRUE(state.IsTableEmpty(kBareTable2));

  EXPECT_EQ(state.GetNumTableEntries(kBareTable1), 1);
  EXPECT_EQ(state.GetNumTableEntries(kBareTable2), 0);

  EXPECT_EQ(state.GetTableEntries(kBareTable1).size(), 1);
  EXPECT_EQ(state.GetTableEntries(kBareTable2).size(), 0);

  EXPECT_EQ(state.GetCanonicalTableEntries(kBareTable1).size(), 1);
  EXPECT_EQ(state.GetCanonicalTableEntries(kBareTable2).size(), 0);

  EXPECT_OK(state.CheckConsistency());

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

TEST(SwitchStateTest, RuleModify) {
  SwitchState state(GetIrP4Info());

  // Construct old_entry and new_entry.
  TableEntry old_entry = gutil::ParseProtoOrDie<TableEntry>(
      absl::Substitute(R"pb(
                         table_id: $0
                         match {
                           field_id: 1
                           exact { value: "\378\"" }
                         }
                         metadata: "cookie: 42"
                       )pb",
                       kSpamTableId));

  TableEntry new_entry = old_entry;
  new_entry.set_metadata("not_a_cookie");

  // Set up SwitchState.
  Update update;
  update.set_type(Update::INSERT);
  *update.mutable_entity()->mutable_table_entry() = old_entry;

  ASSERT_OK(state.ApplyUpdate(update));

  ASSERT_THAT(state.GetTableEntry(old_entry),
              Optional(Not(EqualsProto(new_entry))));

  // Modify SwitchState
  update.set_type(Update::MODIFY);
  update.mutable_entity()->mutable_table_entry()->set_metadata("not_a_cookie");

  ASSERT_OK(state.ApplyUpdate(update));

  ASSERT_THAT(state.GetTableEntry(new_entry), Optional(EqualsProto(new_entry)));

  ASSERT_OK(state.CheckConsistency());
}

TEST(SwitchStateTest, RuleDelete) {
  SwitchState state(GetIrP4Info());

  Update update;
  update.set_type(Update::INSERT);

  TableEntry* entry = update.mutable_entity()->mutable_table_entry();
  entry->set_table_id(kBareTable1);

  ASSERT_OK(state.ApplyUpdate(update));

  EXPECT_OK(state.CheckConsistency());

  update.set_type(Update::DELETE);
  ASSERT_OK(state.ApplyUpdate(update));

  EXPECT_TRUE(state.AllTablesEmpty());

  EXPECT_EQ(state.GetNumTableEntries(kBareTable1), 0);
  EXPECT_EQ(state.GetTableEntries(kBareTable1).size(), 0);
  EXPECT_EQ(state.GetCanonicalTableEntries(kBareTable1).size(), 0);

  EXPECT_OK(state.CheckConsistency());
}

TEST(SwitchStateTest,
     NonCanonicalAndCanonicalEntriesAreProperlyStoredAndRetrieved) {
  SwitchState state(GetIrP4Info());

  // Construct non-canonical entry and its canonical counterpart.
  TableEntry entry_in_update = gutil::ParseProtoOrDie<TableEntry>(
      absl::Substitute(R"pb(
                         table_id: $0
                         match {
                           field_id: 1
                           exact { value: "\000\378\"" }
                         }
                       )pb",
                       kSpamTableId));

  TableEntry canonicalized_entry = gutil::ParseProtoOrDie<TableEntry>(
      absl::Substitute(R"pb(
                         table_id: $0
                         match {
                           field_id: 1
                           exact { value: "\378\"" }
                         }
                       )pb",
                       kSpamTableId));

  // Check for correct canonicalization.
  ASSERT_OK_AND_ASSIGN(TableEntry canonicalized_entry_in_update,
                       CanonicalizeTableEntry(GetIrP4Info(), entry_in_update,
                                              /*key_only=*/false));
  ASSERT_THAT(canonicalized_entry_in_update,
              gutil::EqualsProto(canonicalized_entry));

  // Set up SwitchState.
  Update update;
  update.set_type(Update::INSERT);
  *update.mutable_entity()->mutable_table_entry() = entry_in_update;

  ASSERT_OK(state.ApplyUpdate(update));

  // Ensure that entry_in_update is stored in standard table.
  ASSERT_FALSE(state.GetTableEntry(canonicalized_entry).has_value());
  ASSERT_THAT(state.GetTableEntry(entry_in_update),
              Optional(EqualsProto(entry_in_update)));

  // Ensure that canonical entry is stored in canonical table.
  ASSERT_FALSE(state.GetCanonicalTableEntry(entry_in_update).has_value());
  ASSERT_THAT(state.GetCanonicalTableEntry(canonicalized_entry),
              testing::Optional(gutil::EqualsProto(canonicalized_entry)));

  ASSERT_OK(state.CheckConsistency());
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
  SwitchState state(GetIrP4Info());

  EXPECT_TRUE(state.AllTablesEmpty());

  // Call SetTableEntries and ensure it indeed populates the correct tables.
  std::vector<p4::v1::TableEntry> entries;
  entries.emplace_back() =  // Entry #1 in table 1.
      gutil::ParseProtoOrDie<p4::v1::TableEntry>(
          absl::Substitute(R"pb(
                             table_id: $0
                             match {
                               field_id: 1
                               exact { value: "\378\"" }
                             }
                           )pb",
                           kSpamTableId));
  entries.emplace_back().set_table_id(kEggTableId);  // Entry #1 in table 2.
  entries.emplace_back() =                           // Entry #2 in table 1.
      gutil::ParseProtoOrDie<p4::v1::TableEntry>(
          absl::Substitute(R"pb(
                             table_id: $0
                             match {
                               field_id: 1
                               exact { value: "\377\"" }
                             }
                           )pb",
                           kSpamTableId));
  ASSERT_OK(state.SetTableEntries(entries))
      << " with the following P4Info:\n " << state.GetIrP4Info().DebugString();
  EXPECT_EQ(state.GetNumTableEntries(kSpamTableId), 2);
  EXPECT_EQ(state.GetNumTableEntries(kEggTableId), 1);
  EXPECT_EQ(state.GetNumTableEntries(), 3);

  EXPECT_OK(state.CheckConsistency());

  state.ClearTableEntries();
  EXPECT_EQ(state.GetNumTableEntries(kSpamTableId), 0);
  EXPECT_EQ(state.GetNumTableEntries(kEggTableId), 0);
  EXPECT_EQ(state.GetNumTableEntries(), 0);
  EXPECT_TRUE(state.AllTablesEmpty());

  EXPECT_OK(state.CheckConsistency());
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
