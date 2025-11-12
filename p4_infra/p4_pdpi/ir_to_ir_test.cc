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

#include "p4_infra/p4_pdpi/ir.h"

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"

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
