#include "p4_pdpi/ir.h"

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"

using gutil::EqualsProto;
using gutil::IsOk;
using gutil::IsOkAndHolds;
using testing::Not;

namespace pdpi {

namespace {

TEST(IrEntitiesToTableEntriesTest, CorrectlyConvertIrEntities) {
  // Ensure that we do not throw an error with empty inputs.
  EXPECT_THAT(IrEntitiesToTableEntries(pdpi::IrEntities()),
              IsOkAndHolds(EqualsProto(pdpi::IrTableEntries())));

  const auto kIrEntities = gutil::ParseProtoOrDie<pdpi::IrEntities>(R"pb(
    entities {
      table_entry {
        table_name: "test_table",
      }
    }
  )pb");

  const auto kIrTableEntries =
      gutil::ParseProtoOrDie<pdpi::IrTableEntries>(R"pb(
        entries {
          table_name: "test_table",
        }
      )pb");

  EXPECT_THAT(IrEntitiesToTableEntries(kIrEntities),
              IsOkAndHolds(EqualsProto(kIrTableEntries)));
}

TEST(IrEntitiesToTableEntriesTest, CircularConversionTest) {
  const auto kIrTableEntries =
      gutil::ParseProtoOrDie<pdpi::IrTableEntries>(R"pb(
        entries {
          table_name: "test_table",
        }
      )pb");

  // Convert the table entries to entities and immediately convert them back to
  // IrEntities.
  EXPECT_THAT(
      IrEntitiesToTableEntries(IrTableEntriesToEntities(kIrTableEntries)),
      IsOkAndHolds(EqualsProto(kIrTableEntries)));
}

TEST(IrEntitiesToTableEntriesTest, IrEntitiesConversionError) {
  pdpi::IrEntities ir_entities;
  *ir_entities.add_entities()->mutable_packet_replication_engine_entry() =
      IrPacketReplicationEngineEntry();

  EXPECT_THAT(IrEntitiesToTableEntries(ir_entities), Not(IsOk()));
}
}  // namespace
}  // namespace pdpi
