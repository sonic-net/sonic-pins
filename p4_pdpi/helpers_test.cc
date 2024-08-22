#include "p4_pdpi/helpers.h"

#include <string>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/built_ins.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/testing/test_p4info.h"

namespace pdpi {
namespace {

using gutil::IsOk;
using gutil::IsOkAndHolds;
using testing::Not;

TEST(EntityToTableNameTest, StandardTableSupported) {
  IrP4Info kInfo = GetTestIrP4Info();
  IrTableDefinition kTestTable = kInfo.tables_by_id().begin()->second;
  p4::v1::Entity entity;
  entity.mutable_table_entry()->set_table_id(kTestTable.preamble().id());

  EXPECT_THAT(EntityToTableName(kInfo, entity),
              IsOkAndHolds(kTestTable.preamble().alias()));
}

TEST(EntityToTableNameTest, MulticastTableSupported) {
  p4::v1::Entity entity;
  entity.mutable_packet_replication_engine_entry()
      ->mutable_multicast_group_entry();

  ASSERT_OK_AND_ASSIGN(
      std::string multicast_group_table_name,
      IrBuiltInTableToString(BUILT_IN_TABLE_MULTICAST_GROUP_TABLE));

  EXPECT_THAT(EntityToTableName(GetTestIrP4Info(), entity),
              IsOkAndHolds(multicast_group_table_name));
}

TEST(EntityToTableNameTest, OtherPacketReplicationEngineUnsupported) {
  p4::v1::Entity entity;
  entity.mutable_packet_replication_engine_entry()
      ->mutable_clone_session_entry();

  EXPECT_THAT(EntityToTableName(GetTestIrP4Info(), entity), Not(IsOk()));
}

TEST(EntityToTableNameTest, OtherEntitiesUnsupported) {
  p4::v1::Entity entity;
  entity.mutable_direct_counter_entry();

  EXPECT_THAT(EntityToTableName(GetTestIrP4Info(), entity), Not(IsOk()));
}

}  // namespace
}  // namespace pdpi
