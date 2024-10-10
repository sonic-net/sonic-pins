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
#include <vector>

#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/substitute.h"
#include "absl/types/span.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/collections.h"
#include "gutil/proto_matchers.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/pd.h"
#include "p4_pdpi/testing/main_p4_pd.pb.h"
#include "p4_pdpi/testing/test_p4info.h"

namespace p4_fuzzer {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::p4::config::v1::Action;
using ::p4::config::v1::ActionProfile;
using ::p4::config::v1::ActionRef;
using ::p4::config::v1::P4Info;
using ::p4::config::v1::Preamble;
using ::p4::config::v1::Table;
using ::p4::v1::ActionProfileAction;
using ::p4::v1::TableEntry;
using ::p4::v1::Update;
using ::pdpi::CreateIrP4Info;
using ::pdpi::IrP4Info;
using ::testing::AllOf;
using ::testing::ElementsAre;
using ::testing::FieldsAre;
using ::testing::HasSubstr;
using ::testing::IsEmpty;
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
  // Ensure that canonical entry is stored in canonical table.
  ASSERT_THAT(state.GetTableEntry(entry_in_update),
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

TEST(SwitchStateTest, OnlyInsertAffectsMaxResourceStatisticsForDirectTables) {
  SwitchState state(GetIrP4Info());
  ASSERT_THAT(state.GetPeakResourceStatistics(kBareTable1),
              IsOkAndHolds(FieldsAre(
                  /*entries=*/0,
                  /*total_weight=*/0,
                  /*total_members=*/0,
                  /*max_group_weight=*/0,
                  /*max_members_per_group=*/0)));

  // Insert entry and expect update to max resource statistics.
  Update update;
  update.set_type(Update::INSERT);
  TableEntry* entry = update.mutable_entity()->mutable_table_entry();
  entry->set_table_id(kBareTable1);
  ASSERT_OK(state.ApplyUpdate(update));
  EXPECT_THAT(state.GetPeakResourceStatistics(kBareTable1),
              IsOkAndHolds(FieldsAre(
                  /*entries=*/1,
                  /*total_weight=*/0,
                  /*total_members=*/0,
                  /*max_group_weight=*/0,
                  /*max_members_per_group=*/0)));
  EXPECT_EQ(state.GetMaxEntriesSeen(), 1);
  ASSERT_OK(state.CheckConsistency());

  // Modify entry and expect no change in max resource statistics.
  Update modify_update;
  modify_update.set_type(Update::MODIFY);
  entry->set_metadata("chocolate_chip_cookie");
  *modify_update.mutable_entity()->mutable_table_entry() = *entry;
  ASSERT_OK(state.ApplyUpdate(modify_update));
  EXPECT_THAT(state.GetPeakResourceStatistics(kBareTable1),
              IsOkAndHolds(FieldsAre(
                  /*entries=*/1,
                  /*total_weight=*/0,
                  /*total_members=*/0,
                  /*max_group_weight=*/0,
                  /*max_members_per_group=*/0)));
  EXPECT_EQ(state.GetMaxEntriesSeen(), 1);
  ASSERT_OK(state.CheckConsistency());

  // Delete entry and expect no change in max resource statistics.
  Update delete_update;
  delete_update.set_type(Update::DELETE);
  *delete_update.mutable_entity()->mutable_table_entry() = *entry;
  ASSERT_OK(state.ApplyUpdate(delete_update));
  EXPECT_THAT(state.GetPeakResourceStatistics(kBareTable1),
              IsOkAndHolds(FieldsAre(
                  /*entries=*/1,
                  /*total_weight=*/0,
                  /*total_members=*/0,
                  /*max_group_weight=*/0,
                  /*max_members_per_group=*/0)));
  EXPECT_EQ(state.GetMaxEntriesSeen(), 1);
  ASSERT_OK(state.CheckConsistency());
}

TEST(SwitchStateTest,
     OnlyInsertAndModifyEffectMaxResourceStatisticsForIndirectTables) {
  constexpr int kWcmpId = 33554438;
  const IrP4Info& info = pdpi::GetTestIrP4Info();
  SwitchState state(info);
  EXPECT_THAT(state.GetPeakResourceStatistics(kWcmpId),
              IsOkAndHolds(FieldsAre(
                  /*entries=*/0,
                  /*total_weight=*/0,
                  /*total_members=*/0,
                  /*max_group_weight=*/0,
                  /*max_members_per_group=*/0)));

  // Insert entry and expect update to max resource statistics.
  pdpi::TableEntry wcmp_entry = gutil::ParseProtoOrDie<pdpi::TableEntry>(
      R"pb(
        wcmp_table_entry {
          match { ipv4 { value: "0.0.255.0" prefix_length: 24 } }
          wcmp_actions {
            action { do_thing_1 { arg2: "0x01234567" arg1: "0x01234568" } }
            weight: 1
          }
          wcmp_actions {
            action { do_thing_1 { arg2: "0x01234569" arg1: "0x01234560" } }
            weight: 2
          }
        }
      )pb");
  ASSERT_OK(state.ApplyUpdate(MakePiUpdate(info, Update::INSERT, wcmp_entry)));
  EXPECT_THAT(state.GetPeakResourceStatistics(kWcmpId),
              IsOkAndHolds(FieldsAre(
                  /*entries=*/1,
                  /*total_weight=*/3,
                  /*total_members=*/2,
                  /*max_group_weight=*/3,
                  /*max_members_per_group=*/2)));
  EXPECT_EQ(state.GetMaxEntriesSeen(), 1);
  ASSERT_OK(state.CheckConsistency());

  // Modify entry and expect update to max resource statistics.
  wcmp_entry = gutil::ParseProtoOrDie<pdpi::TableEntry>(
      R"pb(
        wcmp_table_entry {
          match { ipv4 { value: "0.0.255.0" prefix_length: 24 } }
          wcmp_actions {
            action { do_thing_1 { arg2: "0x01234567" arg1: "0x01234568" } }
            weight: 1
          }
          wcmp_actions {
            action { do_thing_1 { arg2: "0x01234569" arg1: "0x01234560" } }
            weight: 5
          }
        }
      )pb");
  ASSERT_OK(state.ApplyUpdate(MakePiUpdate(info, Update::MODIFY, wcmp_entry)));
  EXPECT_THAT(state.GetPeakResourceStatistics(kWcmpId),
              IsOkAndHolds(FieldsAre(
                  /*entries=*/1,
                  /*total_weight=*/6,
                  /*total_members=*/2,
                  /*max_group_weight=*/6,
                  /*max_members_per_group=*/2)));
  EXPECT_EQ(state.GetMaxEntriesSeen(), 1);
  ASSERT_OK(state.CheckConsistency());

  // Delete entry and expect no change in max resource statistics.
  ASSERT_OK(state.ApplyUpdate(MakePiUpdate(info, Update::DELETE, wcmp_entry)));
  EXPECT_THAT(state.GetPeakResourceStatistics(kWcmpId),
              IsOkAndHolds(FieldsAre(
                  /*entries=*/1,
                  /*total_weight=*/6,
                  /*total_members=*/2,
                  /*max_group_weight=*/6,
                  /*max_members_per_group=*/2)));
  EXPECT_EQ(state.GetMaxEntriesSeen(), 1);
  ASSERT_OK(state.CheckConsistency());
}

absl::StatusOr<ReferableEntry> MakePiReferableEntry(
    const IrP4Info& info, const pdpi::TableEntry& entry,
    absl::flat_hash_set<std::string> fields) {
  ASSIGN_OR_RETURN(TableEntry pi_entry,
                   pdpi::PartialPdTableEntryToPiTableEntry(info, entry));

  ASSIGN_OR_RETURN(
      pdpi::IrTableDefinition table_definition,
      gutil::FindOrStatus(info.tables_by_id(), pi_entry.table_id()));

  ReferableEntry result;
  for (const auto& match : pi_entry.match()) {
    ASSIGN_OR_RETURN(pdpi::IrMatchFieldDefinition match_field_definition,
                     gutil::FindOrStatus(table_definition.match_fields_by_id(),
                                         match.field_id()));
    std::string field_name = match_field_definition.match_field().name();
    if (fields.contains(field_name)) {
      switch (match.field_match_type_case()) {
        case p4::v1::FieldMatch::kExact:
          result.insert({field_name, match.exact().value()});
          break;
        case p4::v1::FieldMatch::kOptional:
          result.insert({field_name, match.optional().value()});
          break;
        default:
          return gutil::InvalidArgumentErrorBuilder()
                 << "Only match fields with type exact or optional can be "
                    "referred to. Referenced field "
                 << field_name << " has a different match type.";
          break;
      }
    }
  }

  for (const auto& field : fields) {
    if (!result.contains(field)) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Could not form referable entry. Entry is missing field "
             << field;
    }
  }

  return result;
}

TEST(SwitchStateTest, GetReferableEntriesWithNonExistentTableIsNotFound) {
  const IrP4Info& info = pdpi::GetTestIrP4Info();
  SwitchState state(info);

  const std::string kReferencedTable = "Not_A_Table";
  const absl::flat_hash_set<std::string> kReferencedFields = {"Not_A_Field"};

  // Return NotFoundError when referencing non-existent table.
  EXPECT_THAT(state.GetReferableEntries(kReferencedTable, kReferencedFields),
              StatusIs(absl::StatusCode::kNotFound));
}

TEST(SwitchStateTest, GetReferableEntriesWithNoFieldsIsInvalid) {
  const IrP4Info& info = pdpi::GetTestIrP4Info();
  SwitchState state(info);

  const std::string kReferencedTable = "id_test_table";

  // Return invalid argument when referencing no fields.
  EXPECT_THAT(state.GetReferableEntries(kReferencedTable, {}),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(SwitchStateTest, GetReferableEntriesWithNonExistentFieldIsNotFound) {
  const IrP4Info& info = pdpi::GetTestIrP4Info();
  SwitchState state(info);

  const std::string kReferencedTable = "id_test_table";
  const absl::flat_hash_set<std::string> kReferencedFields = {"Not_A_Field"};

  // Return NotFoundError when referencing non-existent field.
  EXPECT_THAT(state.GetReferableEntries(kReferencedTable, kReferencedFields),
              StatusIs(absl::StatusCode::kNotFound));
}

TEST(SwitchStateTest, GetReferableEntriesWithNonExactOrOptionalFieldIsInvalid) {
  const IrP4Info& info = pdpi::GetTestIrP4Info();
  SwitchState state(info);

  const std::string kReferencedTable = "ternary_table";
  const absl::flat_hash_set<std::string> kReferencedFields = {"ipv4"};

  // Return invalid argument when referencing ternary field.
  EXPECT_THAT(state.GetReferableEntries(kReferencedTable, kReferencedFields),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(SwitchStateTest, GetReferableEntriesWithExactFields) {
  const IrP4Info& info = pdpi::GetTestIrP4Info();
  SwitchState state(info);

  const std::string kReferencedTable = "id_test_table";
  const absl::flat_hash_set<std::string> kReferencedFields = {"ipv4", "ipv6"};

  pdpi::TableEntry entry1 = gutil::ParseProtoOrDie<pdpi::TableEntry>(
      R"pb(
        id_test_table_entry {
          match { ipv6: "::1" ipv4: "0.0.0.1" }
          action { do_thing_1 { arg2: "0x00000002" arg1: "0x00000001" } }
        }
      )pb");
  ASSERT_OK_AND_ASSIGN(ReferableEntry referable_entry1,
                       MakePiReferableEntry(info, entry1, kReferencedFields));
  pdpi::TableEntry entry2 = gutil::ParseProtoOrDie<pdpi::TableEntry>(
      R"pb(
        id_test_table_entry {
          match { ipv6: "::2" ipv4: "0.0.0.2" }
          action { do_thing_1 { arg2: "0x00000002" arg1: "0x00000001" } }
        }
      )pb");
  ASSERT_OK_AND_ASSIGN(ReferableEntry referable_entry2,
                       MakePiReferableEntry(info, entry2, kReferencedFields));

  // Return empty vector for table with no entries.
  EXPECT_THAT(state.GetReferableEntries(kReferencedTable, kReferencedFields),
              IsOkAndHolds(IsEmpty()));

  ASSERT_OK(state.ApplyUpdate(MakePiUpdate(info, Update::INSERT, entry1)));

  // Return a single referable entry for table with one entry.
  EXPECT_THAT(state.GetReferableEntries(kReferencedTable, kReferencedFields),
              IsOkAndHolds(ElementsAre(referable_entry1)));

  ASSERT_OK(state.ApplyUpdate(MakePiUpdate(info, Update::INSERT, entry2)));

  // Return two referable entries for table with two entries.
  EXPECT_THAT(state.GetReferableEntries(kReferencedTable, kReferencedFields),
              IsOkAndHolds(ElementsAre(referable_entry1, referable_entry2)));

  ASSERT_OK(state.ApplyUpdate(MakePiUpdate(info, Update::DELETE, entry1)));

  // Return one referable entry after entry is deleted.
  EXPECT_THAT(state.GetReferableEntries(kReferencedTable, kReferencedFields),
              IsOkAndHolds(ElementsAre(referable_entry2)));
}

TEST(SwitchStateTest, GetReferableEntriesWithOptionalFields) {
  const IrP4Info& info = pdpi::GetTestIrP4Info();
  SwitchState state(info);

  const std::string kReferencedTable = "optional_table";
  const absl::flat_hash_set<std::string> kReferencedFields = {"ipv4", "ipv6",
                                                              "str"};

  pdpi::TableEntry entry_with_2_optionals_omitted =
      gutil::ParseProtoOrDie<pdpi::TableEntry>(
          R"pb(
            optional_table_entry {
              match { ipv6 { value: "::1" } }
              action { do_thing_1 { arg2: "0x00000002" arg1: "0x00000001" } }
              priority: 10
            }
          )pb");

  pdpi::TableEntry entry_with_all_optionals_present =
      gutil::ParseProtoOrDie<pdpi::TableEntry>(
          R"pb(
            optional_table_entry {
              match {
                ipv6 { value: "::2" }
                ipv4 { value: "0.0.0.2" }
                str { value: "hi" }
              }
              action { do_thing_1 { arg2: "0x00000002" arg1: "0x00000001" } }
              priority: 20
            }
          )pb");
  ASSERT_OK_AND_ASSIGN(
      ReferableEntry referable_entry,
      MakePiReferableEntry(info, entry_with_all_optionals_present,
                           kReferencedFields));

  ASSERT_OK(state.ApplyUpdate(
      MakePiUpdate(info, Update::INSERT, entry_with_2_optionals_omitted)));

  // Return empty vector for table with entries where optional fields are
  // omitted.
  EXPECT_THAT(state.GetReferableEntries(kReferencedTable, kReferencedFields),
              IsOkAndHolds(IsEmpty()));

  ASSERT_OK(state.ApplyUpdate(
      MakePiUpdate(info, Update::INSERT, entry_with_all_optionals_present)));

  // Return referable entry only for entries where all optionals are present.
  EXPECT_THAT(state.GetReferableEntries(kReferencedTable, kReferencedFields),
              IsOkAndHolds(ElementsAre(referable_entry)));
}

TEST(SwitchStateTest, GetReferableEntriesWithOnlyOneOptionalField) {
  const IrP4Info& info = pdpi::GetTestIrP4Info();
  SwitchState state(info);

  const std::string kReferencedTable = "optional_table";
  const absl::flat_hash_set<std::string> kReferencedFields = {"str"};

  pdpi::TableEntry entry_without_referenced_field =
      gutil::ParseProtoOrDie<pdpi::TableEntry>(
          R"pb(
            optional_table_entry {
              match {
                ipv6 { value: "::1" }
                ipv4 { value: "0.0.0.1" }
              }
              action { do_thing_1 { arg2: "0x00000002" arg1: "0x00000001" } }
              priority: 10
            }
          )pb");

  pdpi::TableEntry entry_with_only_referenced_field =
      gutil::ParseProtoOrDie<pdpi::TableEntry>(
          R"pb(
            optional_table_entry {
              match { str { value: "hi" } }
              action { do_thing_1 { arg2: "0x00000002" arg1: "0x00000001" } }
              priority: 20
            }
          )pb");
  ASSERT_OK_AND_ASSIGN(
      ReferableEntry referable_entry_1,
      MakePiReferableEntry(info, entry_with_only_referenced_field,
                           kReferencedFields));

  pdpi::TableEntry entry_with_all_field_set =
      gutil::ParseProtoOrDie<pdpi::TableEntry>(
          R"pb(
            optional_table_entry {
              match {
                ipv6 { value: "::3" }
                ipv4 { value: "0.0.0.3" }
                str { value: "bye" }
              }
              action { do_thing_1 { arg2: "0x00000002" arg1: "0x00000001" } }
              priority: 30
            }
          )pb");
  ASSERT_OK_AND_ASSIGN(
      ReferableEntry referable_entry_2,
      MakePiReferableEntry(info, entry_with_all_field_set, kReferencedFields));

  ASSERT_OK(state.ApplyUpdate(
      MakePiUpdate(info, Update::INSERT, entry_without_referenced_field)));

  // Return empty vector for table with entries lacking referenced field.
  EXPECT_THAT(state.GetReferableEntries(kReferencedTable, kReferencedFields),
              IsOkAndHolds(IsEmpty()));

  ASSERT_OK(state.ApplyUpdate(
      MakePiUpdate(info, Update::INSERT, entry_with_only_referenced_field)));

  // Return referable entry only for entry with only referenced field.
  EXPECT_THAT(state.GetReferableEntries(kReferencedTable, kReferencedFields),
              IsOkAndHolds(ElementsAre(referable_entry_1)));

  ASSERT_OK(state.ApplyUpdate(
      MakePiUpdate(info, Update::INSERT, entry_with_all_field_set)));

  // Return referable entry only for entries with referenced field.
  EXPECT_THAT(state.GetReferableEntries(kReferencedTable, kReferencedFields),
              IsOkAndHolds(ElementsAre(referable_entry_1, referable_entry_2)));
}

TEST(SwitchStateTest, GetReferableEntriesWithExactAndOptionalFields) {
  const IrP4Info& info = pdpi::GetTestIrP4Info();
  SwitchState state(info);

  const std::string kReferencedTable = "exact_and_optional_table";
  const absl::flat_hash_set<std::string> kReferencedFields = {"ipv6", "str"};

  pdpi::TableEntry entry_with_optional_omitted =
      gutil::ParseProtoOrDie<pdpi::TableEntry>(
          R"pb(
            exact_and_optional_table_entry {
              match { ipv6: "::1" ipv4: "0.0.0.1" }
              action { do_thing_4 {} }
              priority: 10
            }
          )pb");

  pdpi::TableEntry entry_with_optional_present =
      gutil::ParseProtoOrDie<pdpi::TableEntry>(
          R"pb(
            exact_and_optional_table_entry {
              match {
                ipv6: "::2"
                ipv4: "0.0.0.2"
                str { value: "hi" }
              }
              action { do_thing_4 {} }
              priority: 20
            }
          )pb");
  ASSERT_OK_AND_ASSIGN(ReferableEntry referable_entry,
                       MakePiReferableEntry(info, entry_with_optional_present,
                                            kReferencedFields));

  ASSERT_OK(state.ApplyUpdate(
      MakePiUpdate(info, Update::INSERT, entry_with_optional_omitted)));

  // Return empty vector for table with entry where optional field is missing.
  EXPECT_THAT(state.GetReferableEntries(kReferencedTable, kReferencedFields),
              IsOkAndHolds(IsEmpty()));

  ASSERT_OK(state.ApplyUpdate(
      MakePiUpdate(info, Update::INSERT, entry_with_optional_present)));

  // Return referable entry where optional field is present.
  EXPECT_THAT(state.GetReferableEntries(kReferencedTable, kReferencedFields),
              IsOkAndHolds(ElementsAre(referable_entry)));
}

TEST(SwitchStateTest, GetReferableEntriesWithIdenticalValueOnField) {
  const IrP4Info& info = pdpi::GetTestIrP4Info();
  SwitchState state(info);

  const std::string kReferencedTable = "exact_and_optional_table";
  const absl::flat_hash_set<std::string> kReferencedFields = {"str"};

  pdpi::TableEntry entry_1 = gutil::ParseProtoOrDie<pdpi::TableEntry>(
      R"pb(
        exact_and_optional_table_entry {
          match {
            ipv6: "::1"
            ipv4: "0.0.0.1"
            str { value: "hi" }
          }
          action { do_thing_4 {} }
          priority: 10
        }
      )pb");
  ASSERT_OK_AND_ASSIGN(ReferableEntry referable_entry_1,
                       MakePiReferableEntry(info, entry_1, kReferencedFields));

  pdpi::TableEntry entry_2 = gutil::ParseProtoOrDie<pdpi::TableEntry>(
      R"pb(
        exact_and_optional_table_entry {
          match {
            ipv6: "::2"
            ipv4: "0.0.0.2"
            str { value: "hi" }
          }
          action { do_thing_4 {} }
          priority: 20
        }
      )pb");
  ASSERT_OK_AND_ASSIGN(ReferableEntry referable_entry_2,
                       MakePiReferableEntry(info, entry_2, kReferencedFields));

  ASSERT_OK(state.ApplyUpdate(MakePiUpdate(info, Update::INSERT, entry_1)));
  ASSERT_OK(state.ApplyUpdate(MakePiUpdate(info, Update::INSERT, entry_2)));

  ASSERT_OK_AND_ASSIGN(
      std::vector<ReferableEntry> referable_entries,
      state.GetReferableEntries(kReferencedTable, kReferencedFields));

  EXPECT_THAT(referable_entries,
              ElementsAre(referable_entry_1, referable_entry_2));

  // Both entries create the same referable entry.
  EXPECT_EQ(referable_entries[0], referable_entries[1]);
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

// Resource limits tests verify switch state behavior when tables and action
// profiles are at their capacities. The fixture can be used to create a custom
// P4Info with:
//   * 1 action profile
//   * 1 table which uses the action profile.
//   * 1 table which does not use the action profile.
class ResourceLimitsTest : public testing::Test {
 protected:
  // Tests should specify the P4Info values that are relevant. For example, when
  // verifying behavior around the table size the test should set '.table_size =
  // X'.
  struct P4InfoOptions {
    int64_t table_size = 0;
    int64_t action_profile_size = 0;
    int32_t action_profile_max_group_size = 0;
    // Determine whether selector_size_semantics is set or unset.
    bool set_selector_size_semantics = true;
    // If above is true, determines whether to use SumOfWeight (nullopt) or
    // SumOfMembers with max_member_weight set to the given value.
    std::optional<int> max_member_weight = std::nullopt;
  };

  uint64_t TableWithActionProfileId() const { return 101; }
  uint64_t TableWithoutActionProfileId() const { return 102; }
  uint64_t ActionId() const { return 201; }
  uint64_t ActionProfileId() const { return 301; }

  absl::StatusOr<pdpi::IrP4Info> GetIrP4Info(const P4InfoOptions& options) {
    P4Info info;

    ActionProfile* profile = info.add_action_profiles();
    profile->mutable_preamble()->set_id(ActionProfileId());
    profile->mutable_preamble()->set_alias("action_set_profile");
    profile->set_with_selector(true);
    profile->set_size(options.action_profile_size);
    profile->set_max_group_size(options.action_profile_max_group_size);
    if (options.set_selector_size_semantics) {
      if (options.max_member_weight.has_value()) {
        profile->mutable_sum_of_members()->set_max_member_weight(
            *options.max_member_weight);
      } else {
        profile->mutable_sum_of_weights();
      }
    }

    Action* action = info.add_actions();
    action->mutable_preamble()->set_id(ActionId());
    action->mutable_preamble()->set_alias("action_set_action");

    // Table with the action profile.
    Table* table = info.add_tables();
    table->mutable_preamble()->set_id(TableWithActionProfileId());
    table->mutable_preamble()->set_alias("action_set_table");
    table->mutable_preamble()->add_annotations("@oneshot");
    table->set_size(options.table_size);
    // The table needs to link to the action.
    ActionRef* action_ref = table->add_action_refs();
    action_ref->set_id(action->preamble().id());
    action_ref->add_annotations("@proto_id(1)");
    // The action profile and table need to be linked to each other.
    profile->add_table_ids(table->preamble().id());
    table->set_implementation_id(profile->preamble().id());

    // The table without an action profile.
    table = info.add_tables();
    table->mutable_preamble()->set_id(TableWithoutActionProfileId());
    table->mutable_preamble()->set_alias("non_action_set_table");
    table->set_size(options.table_size);
    // The table needs to link to the action.
    action_ref = table->add_action_refs();
    action_ref->set_id(action->preamble().id());
    action_ref->add_annotations("@proto_id(1)");

    return CreateIrP4Info(info);
  }

  Update GetUpdateWithWeights(absl::Span<const int32_t> weights) {
    Update update;
    update.set_type(Update::INSERT);

    TableEntry* entry = update.mutable_entity()->mutable_table_entry();
    entry->set_table_id(TableWithActionProfileId());
    for (int32_t weight : weights) {
      ActionProfileAction* profile = entry->mutable_action()
                                         ->mutable_action_profile_action_set()
                                         ->add_action_profile_actions();
      profile->set_weight(weight);
      profile->mutable_action()->set_action_id(ActionId());
    }

    return update;
  }
};

TEST_F(ResourceLimitsTest, ReturnsFailedPreconditionWhenEntryWillFit) {
  ASSERT_OK_AND_ASSIGN(IrP4Info ir_p4info,
                       GetIrP4Info(P4InfoOptions{
                           .table_size = 10,
                           .action_profile_size = 10,
                           .action_profile_max_group_size = 10,
                           .set_selector_size_semantics = true,
                       }));
  SwitchState state(ir_p4info);

  // Insert an entry to use up some space, then check for new space.
  ASSERT_OK(state.ApplyUpdate(GetUpdateWithWeights({1, 1, 1})));
  EXPECT_THAT(
      state.ResourceExhaustedIsAllowed(
          GetUpdateWithWeights({2}).entity().table_entry()),
      StatusIs(absl::StatusCode::kFailedPrecondition,
               AllOf(HasSubstr("1 entries"), HasSubstr("weight of 3"))));
}

TEST_F(ResourceLimitsTest,
       ReturnsFailedPreconditionWhenOnlyTableSizeIsChecked) {
  ASSERT_OK_AND_ASSIGN(IrP4Info ir_p4info,
                       GetIrP4Info(P4InfoOptions{
                           .table_size = 10,
                           .action_profile_size = 10,
                           .action_profile_max_group_size = 10,
                           .set_selector_size_semantics = true,
                       }));
  SwitchState state(ir_p4info);

  Update update;
  update.set_type(Update::INSERT);
  TableEntry* entry = update.mutable_entity()->mutable_table_entry();
  entry->set_table_id(TableWithoutActionProfileId());

  // Insert an entry to use up some space, then check for new space.
  EXPECT_THAT(state.ResourceExhaustedIsAllowed(update.entity().table_entry()),
              StatusIs(absl::StatusCode::kFailedPrecondition));
}

TEST_F(ResourceLimitsTest, ReturnsOkForTooManyTableResourcesUsed) {
  ASSERT_OK_AND_ASSIGN(IrP4Info ir_p4info,
                       GetIrP4Info(P4InfoOptions{
                           .table_size = 1,
                           .action_profile_size = 10,
                           .action_profile_max_group_size = 10,
                           .set_selector_size_semantics = true,
                       }));
  SwitchState state(ir_p4info);

  // Insert 1 table entry to use up the space.
  ASSERT_OK(state.ApplyUpdate(GetUpdateWithWeights({1})));
  EXPECT_OK(state.ResourceExhaustedIsAllowed(
      GetUpdateWithWeights({1}).entity().table_entry()));
}

TEST_F(ResourceLimitsTest, ReturnsOkForTooMuchWeightBeingUsed) {
  ASSERT_OK_AND_ASSIGN(IrP4Info ir_p4info,
                       GetIrP4Info(P4InfoOptions{
                           .table_size = 10,
                           .action_profile_size = 3,
                           .action_profile_max_group_size = 10,
                           .set_selector_size_semantics = true,
                       }));
  SwitchState state(ir_p4info);

  // We should expect a resource exhausted for one member using too much, or the
  // sum total of all members being too much.
  EXPECT_OK(state.ResourceExhaustedIsAllowed(
      GetUpdateWithWeights({4}).entity().table_entry()));
  EXPECT_OK(state.ResourceExhaustedIsAllowed(
      GetUpdateWithWeights({1, 1, 1, 1}).entity().table_entry()));
}

TEST_F(ResourceLimitsTest, ReturnsOkForTooManyActionsBeingUsed) {
  ASSERT_OK_AND_ASSIGN(IrP4Info ir_p4info,
                       GetIrP4Info(P4InfoOptions{
                           .table_size = 10,
                           .action_profile_size = 3,
                           .action_profile_max_group_size = 10,
                           .set_selector_size_semantics = true,
                           .max_member_weight = 4096,
                       }));
  SwitchState state(ir_p4info);

  EXPECT_OK(state.ResourceExhaustedIsAllowed(
      GetUpdateWithWeights({1, 10, 4, 2}).entity().table_entry()));
}

// If a group size is too large, the switch must return an InvalidArgumentError,
// so we do the same.
TEST_F(ResourceLimitsTest, ReturnsInvalidArgumentForGroupSizesBeingTooLarge) {
  ASSERT_OK_AND_ASSIGN(IrP4Info ir_p4info,
                       GetIrP4Info(P4InfoOptions{
                           .table_size = 10,
                           .action_profile_size = 10,
                           .action_profile_max_group_size = 3,
                           .set_selector_size_semantics = true,
                       }));
  SwitchState state(ir_p4info);

  EXPECT_THAT(state.ResourceExhaustedIsAllowed(
                  GetUpdateWithWeights({1, 1, 1, 1}).entity().table_entry()),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

}  // namespace
}  // namespace p4_fuzzer
