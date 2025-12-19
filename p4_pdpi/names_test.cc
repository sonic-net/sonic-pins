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

#include "p4_pdpi/names.h"

#include <string>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/built_ins.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/testing/test_p4info.h"

namespace pdpi {
namespace {

using ::gutil::IsOk;
using ::gutil::IsOkAndHolds;
using ::testing::Eq;
using ::testing::Not;

TEST(EntityToTableNameTest, StandardTableSupported) {
  IrP4Info kInfo = GetTestIrP4Info();
  IrTableDefinition kTestTable = kInfo.tables_by_id().begin()->second;

  // PI.
  {
    p4::v1::Entity entity;
    entity.mutable_table_entry()->set_table_id(kTestTable.preamble().id());
    EXPECT_THAT(EntityToTableName(kInfo, entity),
                IsOkAndHolds(kTestTable.preamble().alias()));
  }

  // IR.
  EXPECT_THAT(EntityToTableName(gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                table_entry { table_name: "foo" }
              )pb")),
              IsOkAndHolds(Eq("foo")));
}

TEST(EntityToTableNameTest, MulticastTableSupported) {
  ASSERT_OK_AND_ASSIGN(
      std::string multicast_group_table_name,
      IrBuiltInTableToString(BUILT_IN_TABLE_MULTICAST_GROUP_TABLE));

  // PI.
  EXPECT_THAT(
      EntityToTableName(
          GetTestIrP4Info(), gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
            packet_replication_engine_entry { multicast_group_entry {} }
          )pb")),
      IsOkAndHolds(Eq(multicast_group_table_name)));

  // IR.
  EXPECT_THAT(EntityToTableName(gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                packet_replication_engine_entry { multicast_group_entry {} }
              )pb")),
              IsOkAndHolds(Eq(multicast_group_table_name)));
}

TEST(EntityToTableNameTest, CloneSessionTableSupported) {
  ASSERT_OK_AND_ASSIGN(
      std::string clone_session_table_name,
      IrBuiltInTableToString(BUILT_IN_TABLE_CLONE_SESSION_TABLE));

  // PI.
  EXPECT_THAT(
      EntityToTableName(
          GetTestIrP4Info(), gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
            packet_replication_engine_entry { clone_session_entry {} }
          )pb")),
      IsOkAndHolds(Eq(clone_session_table_name)));

  // IR: does not exist in proto at this time.
}

TEST(EntityToTableNameTest, EmptyPacketReplicationEngineUnsupported) {
  // PI.
  EXPECT_THAT(EntityToTableName(GetTestIrP4Info(),
                                gutil::ParseProtoOrDie<p4::v1::Entity>(R"pb(
                                  packet_replication_engine_entry {}
                                )pb")),
              Not(IsOk()));
  // IR.
  EXPECT_THAT(EntityToTableName(gutil::ParseProtoOrDie<pdpi::IrEntity>(R"pb(
                packet_replication_engine_entry {}
              )pb")),
              Not(IsOk()));
}

TEST(EntityToTableNameTest, OtherEntitiesUnsupported) {
  // PI: direct counter entry.
  {
    p4::v1::Entity entity;
    entity.mutable_direct_counter_entry();
    EXPECT_THAT(EntityToTableName(GetTestIrP4Info(), entity), Not(IsOk()));
  }

  // IR: unset entity.
  {
    pdpi::IrEntity entity;
    EXPECT_THAT(EntityToTableName(entity), Not(IsOk()));
  }
}

}  // namespace
}  // namespace pdpi
