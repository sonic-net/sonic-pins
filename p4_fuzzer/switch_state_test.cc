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
#include "p4_fuzzer/switch_state.h"

#include <cstdint>
#include <optional>
#include <vector>

#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/types/span.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/pd.h"
#include "p4_infra/p4_pdpi/testing/main_p4_pd.pb.h"
#include "p4_infra/p4_pdpi/testing/test_p4info.h"

namespace p4_fuzzer {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::p4::config::v1::Action;
using ::p4::config::v1::ActionProfile;
using ::p4::config::v1::ActionRef;
using ::p4::config::v1::MatchField;
using ::p4::config::v1::P4Info;
using ::p4::config::v1::Preamble;
using ::p4::config::v1::Table;
using ::p4::v1::ActionProfileAction;
using ::p4::v1::Entity;
using ::p4::v1::FieldMatch;
using ::p4::v1::MulticastGroupEntry;
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

  EXPECT_TRUE(state.AllP4TablesEmpty());
}

TEST(SwitchStateTest, TableEmptyFromP4Info) {
  P4Info info;
  Table* ptable = info.add_tables();
  ptable->mutable_preamble()->set_id(42);

  IrP4Info ir_info = CreateIrP4Info(info).value();

  SwitchState state(ir_info);
  EXPECT_TRUE(state.AllP4TablesEmpty());
}

TEST(SwitchStateTest, GetEntityReturnsNullOptWhenMulticastEntryNotPresent) {
  SwitchState state(GetIrP4Info());
  Entity entity;
  entity.mutable_packet_replication_engine_entry()
      ->mutable_multicast_group_entry()
      ->set_multicast_group_id(42);

  EXPECT_EQ(state.GetEntity(entity), std::nullopt);
}

TEST(SwitchStateTest, GetEntityReturnsMulticastEntryWhenPresent) {
  SwitchState state(GetIrP4Info());

  Update update;
  update.set_type(Update::INSERT);
  update.mutable_entity()
      ->mutable_packet_replication_engine_entry()
      ->mutable_multicast_group_entry()
      ->set_multicast_group_id(42);

  Entity entity = update.entity();

  ASSERT_OK(state.ApplyUpdate(update));

  EXPECT_THAT(state.GetEntity(entity), Optional(EqualsProto(update.entity())));
}

TEST(SwitchStateTest, GetEntityReturnsNullOptWhenTableEntryNotPresent) {
  SwitchState state(GetIrP4Info());

  Entity entity;
  entity.mutable_table_entry()->set_table_id(kBareTable1);

  EXPECT_EQ(state.GetEntity(entity), std::nullopt);
}

TEST(SwitchStateTest, GetEntityReturnsTableEntryWhenPresent) {
  SwitchState state(GetIrP4Info());

  Update update;
  update.set_type(Update::INSERT);
  update.mutable_entity()->mutable_table_entry()->set_table_id(kBareTable1);

  Entity entity = update.entity();

  ASSERT_OK(state.ApplyUpdate(update));

  EXPECT_THAT(state.GetEntity(entity), Optional(EqualsProto(update.entity())));
}

TEST(SwitchStateTest, RuleInsert) {
  SwitchState state(GetIrP4Info());

  Update update;
  update.set_type(Update::INSERT);

  TableEntry* entry = update.mutable_entity()->mutable_table_entry();
  entry->set_table_id(kBareTable1);

  ASSERT_OK(state.ApplyUpdate(update));

  EXPECT_FALSE(state.AllP4TablesEmpty());
  EXPECT_FALSE(state.IsTableEmpty(kBareTable1));
  EXPECT_TRUE(state.IsTableEmpty(kBareTable2));

  EXPECT_EQ(state.GetNumTableEntries(kBareTable1), 1);
  EXPECT_EQ(state.GetNumTableEntries(kBareTable2), 0);

  EXPECT_EQ(state.GetTableEntries(kBareTable1).size(), 1);
  EXPECT_EQ(state.GetTableEntries(kBareTable2).size(), 0);

  EXPECT_OK(state.CheckConsistency());

  state.ClearTableEntries();
  EXPECT_TRUE(state.AllP4TablesEmpty());
}

TEST(SwitchStateTest, MulticastInsertWorks) {
  SwitchState state(GetIrP4Info());

  Update update = gutil::ParseProtoOrDie<Update>(R"pb(
    type: INSERT
    entity {
      packet_replication_engine_entry {
        multicast_group_entry {
          multicast_group_id: 1
          replicas { port: "some-port" }
        }
      }
    }
  )pb");
  ASSERT_OK(state.ApplyUpdate(update));

  // TODO: b/316926338 - Uncomment once multicast is treated as just another
  // table in switch state.
  // EXPECT_FALSE(state.AllTablesEmpty());

  EXPECT_EQ(state.GetMulticastGroupEntries().size(), 1);

  MulticastGroupEntry& entry = *update.mutable_entity()
                                    ->mutable_packet_replication_engine_entry()
                                    ->mutable_multicast_group_entry();
  ASSERT_TRUE(state.GetMulticastGroupEntry(entry) != std::nullopt);
  EXPECT_THAT(*state.GetMulticastGroupEntry(entry), EqualsProto(entry));

  EXPECT_OK(state.CheckConsistency());

  state.ClearTableEntries();
  EXPECT_TRUE(state.AllP4TablesEmpty());
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

  EXPECT_TRUE(state.AllP4TablesEmpty());

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
                  /*total_members=*/0,
                  /*max_members_per_group=*/0,
                  /*total_weight=*/0,
                  /*max_group_weight=*/0)));

  // Insert entry and expect update to max resource statistics.
  Update update;
  update.set_type(Update::INSERT);
  TableEntry* entry = update.mutable_entity()->mutable_table_entry();
  entry->set_table_id(kBareTable1);
  ASSERT_OK(state.ApplyUpdate(update));
  EXPECT_THAT(state.GetPeakResourceStatistics(kBareTable1),
              IsOkAndHolds(FieldsAre(
                  /*entries=*/1,
                  /*total_members=*/0,
                  /*max_members_per_group=*/0,
                  /*total_weight=*/0,
                  /*max_group_weight=*/0)));
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
                  /*total_members=*/0,
                  /*max_members_per_group=*/0,
                  /*total_weight=*/0,
                  /*max_group_weight=*/0)));
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
                  /*total_members=*/0,
                  /*max_members_per_group=*/0,
                  /*total_weight=*/0,
                  /*max_group_weight=*/0)));
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
                  /*total_members=*/0,
                  /*max_members_per_group=*/0,
                  /*total_weight=*/0,
                  /*max_group_weight=*/0)));

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
                  /*total_members=*/2,
                  /*max_members_per_group=*/2,
                  /*total_weight=*/3,
                  /*max_group_weight=*/3)));
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
                  /*total_members=*/2,
                  /*max_members_per_group=*/2,
                  /*total_weight=*/6,
                  /*max_group_weight=*/6)));
  EXPECT_EQ(state.GetMaxEntriesSeen(), 1);
  ASSERT_OK(state.CheckConsistency());

  // Delete entry and expect no change in max resource statistics.
  ASSERT_OK(state.ApplyUpdate(MakePiUpdate(info, Update::DELETE, wcmp_entry)));
  EXPECT_THAT(state.GetPeakResourceStatistics(kWcmpId),
              IsOkAndHolds(FieldsAre(
                  /*entries=*/1,
                  /*total_members=*/2,
                  /*max_members_per_group=*/2,
                  /*total_weight=*/6,
                  /*max_group_weight=*/6)));
  EXPECT_EQ(state.GetMaxEntriesSeen(), 1);
  ASSERT_OK(state.CheckConsistency());
}

TEST(SwitchStateTest,
     OnlyInsertAndModifyAffectMaxResourceStatisticsForMulticastGroupTable) {
  const IrP4Info& info = pdpi::GetTestIrP4Info();
  SwitchState state(info);
  EXPECT_THAT(state.GetPeakMulticastResourceStatistics(),
              FieldsAre(
                  /*entries=*/0,
                  /*total_members=*/0,
                  /*max_members_per_group=*/0,
                  /*total_weight=*/0,
                  /*max_group_weight=*/0));

  // Insert entry and expect update to max resource statistics.
  Update multicast_update = gutil::ParseProtoOrDie<Update>(
      R"pb(
        type: INSERT
        entity {
          packet_replication_engine_entry {
            multicast_group_entry {
              multicast_group_id: 1
              replicas { instance: 1 port: "1" }
            }
          }
        }
      )pb");
  ASSERT_OK(state.ApplyUpdate(multicast_update));
  EXPECT_THAT(state.GetPeakMulticastResourceStatistics(),
              FieldsAre(
                  /*entries=*/1,
                  /*total_members=*/1,
                  /*max_members_per_group=*/1,
                  /*total_weight=*/0,
                  /*max_group_weight=*/0));
  EXPECT_EQ(state.GetMaxEntriesSeen(), 1);
  ASSERT_OK(state.CheckConsistency());

  // Modify entry and expect update to max resource statistics.
  multicast_update = gutil::ParseProtoOrDie<Update>(
      R"pb(
        type: MODIFY
        entity {
          packet_replication_engine_entry {
            multicast_group_entry {
              multicast_group_id: 1
              replicas { instance: 1 port: "1" }
              replicas { instance: 2 port: "2" }
              replicas { instance: 3 port: "3" }
            }
          }
        }
      )pb");
  ASSERT_OK(state.ApplyUpdate(multicast_update));
  EXPECT_THAT(state.GetPeakMulticastResourceStatistics(),
              FieldsAre(
                  /*entries=*/1,
                  /*total_members=*/3,
                  /*max_members_per_group=*/3,
                  /*total_weight=*/0,
                  /*max_group_weight=*/0));
  EXPECT_EQ(state.GetMaxEntriesSeen(), 1);
  ASSERT_OK(state.CheckConsistency());

  // Modify entry and expect no update to max resource statistics.
  multicast_update = gutil::ParseProtoOrDie<Update>(
      R"pb(
        type: DELETE
        entity {
          packet_replication_engine_entry {
            multicast_group_entry { multicast_group_id: 1 }
          }
        }
      )pb");
  ASSERT_OK(state.ApplyUpdate(multicast_update));
  EXPECT_THAT(state.GetPeakMulticastResourceStatistics(),
              FieldsAre(
                  /*entries=*/1,
                  /*total_members=*/3,
                  /*max_members_per_group=*/3,
                  /*total_weight=*/0,
                  /*max_group_weight=*/0));
  EXPECT_EQ(state.GetMaxEntriesSeen(), 1);
  ASSERT_OK(state.CheckConsistency());
}

TEST(SwitchStateTest, SetEntitiesSetsEntities) {
  SwitchState state(GetIrP4Info());

  EXPECT_TRUE(state.AllP4TablesEmpty());

  // Call SetTableEntries and ensure it indeed populates the correct tables.
  std::vector<p4::v1::Entity> entities;

  entities.emplace_back() =  // Entry #1 in multicast table.
      gutil::ParseProtoOrDie<p4::v1::Entity>(
          R"pb(
            packet_replication_engine_entry {
              multicast_group_entry {
                multicast_group_id: 7
                replicas { instance: 1 port: "some_port" }
                replicas { instance: 2 port: "some_port" }
                replicas { instance: 1 port: "some_other_port" }
              }
            }
          )pb");
  entities.emplace_back() =  // Entry #1 in table 1.
      gutil::ParseProtoOrDie<p4::v1::Entity>(
          absl::Substitute(R"pb(
                             table_entry {
                               table_id: $0
                               match {
                                 field_id: 1
                                 exact { value: "\378\"" }
                               }
                             }
                           )pb",
                           kSpamTableId));
  entities.emplace_back().mutable_table_entry()->set_table_id(
      kEggTableId);          // Entry #1 in table 2.
  entities.emplace_back() =  // Entry #2 in table 1.
      gutil::ParseProtoOrDie<p4::v1::Entity>(
          absl::Substitute(R"pb(
                             table_entry {
                               table_id: $0
                               match {
                                 field_id: 1
                                 exact { value: "\377\"" }
                               }
                             }
                           )pb",
                           kSpamTableId));
  ASSERT_OK(state.SetEntities(entities))
      << " with the following P4Info:\n " << state.GetIrP4Info().DebugString();
  EXPECT_EQ(state.GetNumTableEntries(kSpamTableId), 2);
  EXPECT_EQ(state.GetNumTableEntries(kEggTableId), 1);
  EXPECT_EQ(state.GetNumTableEntries(), 4);

  EXPECT_OK(state.CheckConsistency());

  state.ClearTableEntries();
  EXPECT_EQ(state.GetNumTableEntries(kSpamTableId), 0);
  EXPECT_EQ(state.GetNumTableEntries(kEggTableId), 0);
  EXPECT_EQ(state.GetNumTableEntries(), 0);
  EXPECT_TRUE(state.AllP4TablesEmpty());

  EXPECT_OK(state.CheckConsistency());
}

// Resource limits tests verify switch state behavior when tables and action
// profiles are at their capacities. The fixture can be used to create a custom
// P4Info with:
//   * 1 action profile
//   * 1 table which uses the action profile.
//   * 1 table which does not use the action profile.
class ResourceExhaustionAllowedTest : public testing::Test {
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
    // The table needs a simple match field to create unique entries.
    MatchField* match_field = table->add_match_fields();
    match_field->set_id(kActionProfileTableMatchFieldId);
    match_field->set_match_type(MatchField::EXACT);
    // Set excessively large to hold arbitrary key strings used in testing.
    match_field->set_bitwidth(1024);
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

  Update GetUpdateWithWeights(absl::string_view key,
                              absl::Span<const int32_t> weights,
                              p4::v1::Update::Type type) {
    Update update;
    update.set_type(type);

    TableEntry* entry = update.mutable_entity()->mutable_table_entry();
    entry->set_table_id(TableWithActionProfileId());
    FieldMatch* match_field = entry->add_match();
    match_field->set_field_id(kActionProfileTableMatchFieldId);
    match_field->mutable_exact()->set_value(key);
    for (int32_t weight : weights) {
      ActionProfileAction* profile = entry->mutable_action()
                                         ->mutable_action_profile_action_set()
                                         ->add_action_profile_actions();
      profile->set_weight(weight);
      profile->mutable_action()->set_action_id(ActionId());
    }

    return update;
  }

 private:
  const uint32_t kActionProfileTableMatchFieldId = 1;
};

TEST_F(ResourceExhaustionAllowedTest,
       ReturnsFailedPreconditionForDeleteUpdate) {
  ASSERT_OK_AND_ASSIGN(IrP4Info ir_p4info,
                       GetIrP4Info(P4InfoOptions{
                           .table_size = 1,
                           .action_profile_size = 10,
                           .action_profile_max_group_size = 10,
                           .set_selector_size_semantics = true,
                       }));
  SwitchState state(ir_p4info);

  p4::v1::Update update;
  update.set_type(Update::DELETE);
  EXPECT_THAT(state.ResourceExhaustedIsAllowed(update),
              StatusIs(absl::StatusCode::kFailedPrecondition));
}

TEST_F(ResourceExhaustionAllowedTest,
       ReturnsUnimplementedErrorForMulticastUpdate) {
  ASSERT_OK_AND_ASSIGN(IrP4Info ir_p4info,
                       GetIrP4Info(P4InfoOptions{
                           .table_size = 1,
                           .action_profile_size = 10,
                           .action_profile_max_group_size = 10,
                           .set_selector_size_semantics = true,
                       }));
  SwitchState state(ir_p4info);

  p4::v1::Update update;
  update.set_type(Update::INSERT);
  update.mutable_entity()
      ->mutable_packet_replication_engine_entry()
      ->mutable_multicast_group_entry();
  EXPECT_THAT(state.ResourceExhaustedIsAllowed(update),
              StatusIs(absl::StatusCode::kUnimplemented));
}

TEST_F(ResourceExhaustionAllowedTest,
       ReturnsInvalidArgumentWhenModifyingNonExistentActionSelectorEntry) {
  ASSERT_OK_AND_ASSIGN(IrP4Info ir_p4info,
                       GetIrP4Info(P4InfoOptions{
                           .table_size = 1,
                           .action_profile_size = 10,
                           .action_profile_max_group_size = 10,
                           .set_selector_size_semantics = true,
                       }));
  SwitchState state(ir_p4info);

  EXPECT_THAT(state.ResourceExhaustedIsAllowed(GetUpdateWithWeights(
                  /*key=*/"non_existent_entry", {2}, Update::MODIFY)),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(ResourceExhaustionAllowedTest,
       ReturnsOkOnUpdateThatWontFitTableSizeOtherwiseError) {
  ASSERT_OK_AND_ASSIGN(IrP4Info ir_p4info, GetIrP4Info(P4InfoOptions{
                                               .table_size = 1,
                                           }));
  SwitchState state(ir_p4info);

  Update update;
  update.set_type(Update::INSERT);
  TableEntry* entry = update.mutable_entity()->mutable_table_entry();
  entry->set_table_id(TableWithoutActionProfileId());
  entry->mutable_action()->mutable_action()->set_action_id(ActionId());

  // Initial insert does not cause resource exhaustion.
  EXPECT_THAT(state.ResourceExhaustedIsAllowed(update),
              StatusIs(absl::StatusCode::kFailedPrecondition));
  ASSERT_OK(state.ApplyUpdate(update));

  // Resource exhaustion allowed on second insert.
  EXPECT_OK(state.ResourceExhaustedIsAllowed(update));

  update.set_type(Update::MODIFY);
  // Resource exhaustion not allowed on modify.
  EXPECT_THAT(state.ResourceExhaustedIsAllowed(update),
              StatusIs(absl::StatusCode::kFailedPrecondition));
}

TEST_F(ResourceExhaustionAllowedTest,
       ReturnsErrorOnMaxGroupSizeWeightViolation) {
  ASSERT_OK_AND_ASSIGN(IrP4Info ir_p4info,
                       GetIrP4Info(P4InfoOptions{
                           .table_size = 10,
                           .action_profile_size = 10,
                           .action_profile_max_group_size = 10,
                           .set_selector_size_semantics = true,
                       }));
  SwitchState state(ir_p4info);

  // Error due to violating max_group_size on INSERT.
  EXPECT_THAT(state.ResourceExhaustedIsAllowed(GetUpdateWithWeights(
                  /*key=*/"entry", {25}, Update::INSERT)),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_THAT(state.ResourceExhaustedIsAllowed(GetUpdateWithWeights(
                  /*key=*/"entry", {5, 10, 10}, Update::INSERT)),
              StatusIs(absl::StatusCode::kInvalidArgument));

  // Insert entry for modifies.
  ASSERT_OK(state.ApplyUpdate(
      GetUpdateWithWeights(/*key=*/"entry", {5}, Update::INSERT)));

  // Error due to violating max_group_size on MODIFY.
  EXPECT_THAT(state.ResourceExhaustedIsAllowed(GetUpdateWithWeights(
                  /*key=*/"entry", {25}, Update::MODIFY)),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_THAT(state.ResourceExhaustedIsAllowed(GetUpdateWithWeights(
                  /*key=*/"entry", {5, 10, 10}, Update::MODIFY)),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(
    ResourceExhaustionAllowedTest,
    ReturnsOkOnUpdateThatWontFitUsingSumOfWeightsOtherwiseReturnsErrorWithReason) {
  ASSERT_OK_AND_ASSIGN(IrP4Info ir_p4info,
                       GetIrP4Info(P4InfoOptions{
                           .table_size = 10,
                           .action_profile_size = 10,
                           .action_profile_max_group_size = 10,
                           .set_selector_size_semantics = true,
                       }));
  SwitchState state(ir_p4info);

  // Insert an entry to use up some space.
  ASSERT_OK(state.ApplyUpdate(
      GetUpdateWithWeights(/*key=*/"entry", {5}, Update::INSERT)));

  // Inserts that DO NOT exhaust weight resources.
  EXPECT_THAT(
      state.ResourceExhaustedIsAllowed(
          GetUpdateWithWeights(/*key=*/"other_entry", {5}, Update::INSERT)),
      StatusIs(absl::StatusCode::kFailedPrecondition,
               AllOf(HasSubstr("1 entries"), HasSubstr("total weight of 5"),
                     HasSubstr("needs 5"))));
  EXPECT_THAT(
      state.ResourceExhaustedIsAllowed(GetUpdateWithWeights(
          /*key=*/"other_entry", {1, 2, 2}, Update::INSERT)),
      StatusIs(absl::StatusCode::kFailedPrecondition,
               AllOf(HasSubstr("1 entries"), HasSubstr("total weight of 5"),
                     HasSubstr("needs 5"))));

  // Inserts that DO exhaust weight resources.
  EXPECT_OK(state.ResourceExhaustedIsAllowed(
      GetUpdateWithWeights(/*key=*/"other_entry", {10}, Update::INSERT)));
  EXPECT_OK(state.ResourceExhaustedIsAllowed(GetUpdateWithWeights(
      /*key=*/"other_entry", {2, 4, 4}, Update::INSERT)));

  // Modifies that DO NOT exhaust weight resources. Note that these entries are
  // the same as the ones that caused resource exhaustion on insert.
  EXPECT_THAT(
      state.ResourceExhaustedIsAllowed(
          GetUpdateWithWeights(/*key=*/"entry", {10}, Update::MODIFY)),
      StatusIs(absl::StatusCode::kFailedPrecondition,
               AllOf(HasSubstr("1 entries"), HasSubstr("total weight of 5"),
                     HasSubstr("needs 10"), HasSubstr("had weight 5"))));
  EXPECT_THAT(
      state.ResourceExhaustedIsAllowed(
          GetUpdateWithWeights(/*key=*/"entry", {2, 4, 4}, Update::MODIFY)),
      StatusIs(absl::StatusCode::kFailedPrecondition,
               AllOf(HasSubstr("1 entries"), HasSubstr("total weight of 5"),
                     HasSubstr("needs 10"), HasSubstr("had weight 5"))));

  // For modifies that exhaust resource exhaustion, see
  // `ReturnsOkOnModifyUpdateThatWontFitUsingSumOfWeightsOtherwiseReturnsErrorWithReason`.
}

TEST_F(
    ResourceExhaustionAllowedTest,
    ReturnsOkOnModifyUpdateThatWontFitUsingSumOfWeightsOtherwiseReturnsErrorWithReason) {
  ASSERT_OK_AND_ASSIGN(IrP4Info ir_p4info,
                       GetIrP4Info(P4InfoOptions{
                           .table_size = 10,
                           .action_profile_size = 10,
                           .action_profile_max_group_size = 10,
                           .set_selector_size_semantics = true,
                       }));
  SwitchState state(ir_p4info);

  // Insert an entry to use up some space.
  ASSERT_OK(state.ApplyUpdate(
      GetUpdateWithWeights(/*key=*/"other_entry", {5}, Update::INSERT)));
  // Insert another entry that will be modified.
  ASSERT_OK(state.ApplyUpdate(
      GetUpdateWithWeights(/*key=*/"mod_entry", {2}, Update::INSERT)));

  // Modifies that DO NOT exhaust weight resources.
  EXPECT_THAT(
      state.ResourceExhaustedIsAllowed(
          GetUpdateWithWeights(/*key=*/"mod_entry", {5}, Update::MODIFY)),
      StatusIs(absl::StatusCode::kFailedPrecondition,
               AllOf(HasSubstr("2 entries"), HasSubstr("total weight of 7"),
                     HasSubstr("needs 5"), HasSubstr("had weight 2"))));
  EXPECT_THAT(
      state.ResourceExhaustedIsAllowed(
          GetUpdateWithWeights(/*key=*/"mod_entry", {1, 2, 2}, Update::MODIFY)),
      StatusIs(absl::StatusCode::kFailedPrecondition,
               AllOf(HasSubstr("2 entries"), HasSubstr("total weight of 7"),
                     HasSubstr("needs 5"), HasSubstr("had weight 2"))));

  // Modifies that DO exhaust weight resources.
  EXPECT_OK(state.ResourceExhaustedIsAllowed(
      GetUpdateWithWeights(/*key=*/"mod_entry", {10}, Update::MODIFY)));
  EXPECT_OK(state.ResourceExhaustedIsAllowed(
      GetUpdateWithWeights(/*key=*/"mod_entry", {2, 4, 4}, Update::MODIFY)));
}

TEST_F(ResourceExhaustionAllowedTest,
       ReturnsErrorOnMaxGroupSizeMemberViolation) {
  ASSERT_OK_AND_ASSIGN(IrP4Info ir_p4info,
                       GetIrP4Info(P4InfoOptions{
                           .table_size = 10,
                           .action_profile_size = 10,
                           .action_profile_max_group_size = 3,
                           .set_selector_size_semantics = true,
                           .max_member_weight = 128,
                       }));
  SwitchState state(ir_p4info);

  // Error due to violating max_group_size on INSERT.
  EXPECT_THAT(state.ResourceExhaustedIsAllowed(GetUpdateWithWeights(
                  /*key=*/"entry", {5, 5, 5, 5}, Update::INSERT)),
              StatusIs(absl::StatusCode::kInvalidArgument));

  // Error due to violating max_member_weight on INSERT.
  EXPECT_THAT(state.ResourceExhaustedIsAllowed(GetUpdateWithWeights(
                  /*key=*/"entry", {200}, Update::INSERT)),
              StatusIs(absl::StatusCode::kInvalidArgument));

  // Insert entry for modifies.
  ASSERT_OK(state.ApplyUpdate(
      GetUpdateWithWeights(/*key=*/"entry", {5}, Update::INSERT)));

  // Error due to violating max_group_size on MODIFY.
  EXPECT_THAT(state.ResourceExhaustedIsAllowed(GetUpdateWithWeights(
                  /*key=*/"entry", {5, 5, 5, 5}, Update::MODIFY)),
              StatusIs(absl::StatusCode::kInvalidArgument));

  // Error due to violating max_member_weight on MODIFY.
  EXPECT_THAT(state.ResourceExhaustedIsAllowed(GetUpdateWithWeights(
                  /*key=*/"entry", {200}, Update::MODIFY)),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(
    ResourceExhaustionAllowedTest,
    ReturnsOkOnUpdateThatWontFitUsingSumOfMembersOtherwiseReturnsErrorWithReason) {
  ASSERT_OK_AND_ASSIGN(IrP4Info ir_p4info,
                       GetIrP4Info(P4InfoOptions{
                           .table_size = 10,
                           .action_profile_size = 5,
                           .action_profile_max_group_size = 5,
                           .set_selector_size_semantics = true,
                           .max_member_weight = 128,
                       }));
  SwitchState state(ir_p4info);

  // Insert an entry to use up some space.
  ASSERT_OK(state.ApplyUpdate(
      GetUpdateWithWeights(/*key=*/"entry", {10, 20, 30}, Update::INSERT)));

  // Insert that DOES NOT exhaust weight resources.
  EXPECT_THAT(state.ResourceExhaustedIsAllowed(GetUpdateWithWeights(
                  /*key=*/"other_entry", {40, 50}, Update::INSERT)),
              StatusIs(absl::StatusCode::kFailedPrecondition,
                       AllOf(HasSubstr("1 entries"), HasSubstr("3 members"),
                             HasSubstr("needs 2"))));

  // Insert that DOES exhaust member resources.
  EXPECT_OK(state.ResourceExhaustedIsAllowed(GetUpdateWithWeights(
      /*key=*/"other_entry", {40, 50, 60}, Update::INSERT)));

  // Modify that DOES NOT exhaust member resources. Note that this entry is
  // the same as the one that caused resource exhaustion on insert.
  EXPECT_THAT(
      state.ResourceExhaustedIsAllowed(
          GetUpdateWithWeights(/*key=*/"entry", {40, 50, 60}, Update::MODIFY)),
      StatusIs(absl::StatusCode::kFailedPrecondition,
               AllOf(HasSubstr("1 entries"), HasSubstr("3 members"),
                     HasSubstr("needs 3"), HasSubstr("had 3 members"))));

  // For modifies that exhaust resource exhaustion, see
  // `ReturnsOkOnModifyUpdateThatWontFitUsingSumOfMembersOtherwiseReturnsErrorWithReason`.
}

TEST_F(
    ResourceExhaustionAllowedTest,
    ReturnsOkOnModifyUpdateThatWontFitUsingSumOfMembersOtherwiseReturnsErrorWithReason) {
  ASSERT_OK_AND_ASSIGN(IrP4Info ir_p4info,
                       GetIrP4Info(P4InfoOptions{
                           .table_size = 10,
                           .action_profile_size = 5,
                           .action_profile_max_group_size = 5,
                           .set_selector_size_semantics = true,
                           .max_member_weight = 128,
                       }));
  SwitchState state(ir_p4info);

  // Insert an entry to use up some space.
  ASSERT_OK(state.ApplyUpdate(GetUpdateWithWeights(
      /*key=*/"other_entry", {10, 20, 30}, Update::INSERT)));
  // Insert another entry that will be modified.
  ASSERT_OK(state.ApplyUpdate(
      GetUpdateWithWeights(/*key=*/"mod_entry", {40, 50}, Update::INSERT)));

  // Modifies that DO NOT exhaust member resources.
  EXPECT_THAT(
      state.ResourceExhaustedIsAllowed(GetUpdateWithWeights(
          /*key=*/"mod_entry", {60, 70}, Update::MODIFY)),
      StatusIs(absl::StatusCode::kFailedPrecondition,
               AllOf(HasSubstr("2 entries"), HasSubstr("5 members"),
                     HasSubstr("needs 2"), HasSubstr("had 2 members"))));

  // Modifies that DO exhaust member resources.
  EXPECT_OK(state.ResourceExhaustedIsAllowed(
      GetUpdateWithWeights(/*key=*/"mod_entry", {60, 70, 80}, Update::MODIFY)));
}

}  // namespace
}  // namespace p4_fuzzer
