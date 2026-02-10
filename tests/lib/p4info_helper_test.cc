// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
#include "tests/lib/p4info_helper.h"

#include <memory>

#include "absl/memory/memory.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4/v1/p4runtime_mock.grpc.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/p4_pdpi/p4_runtime_session_mocking.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "thinkit/mock_switch.h"

namespace pins {
namespace {

using ::testing::Return;

TEST(P4InfoHelperTest, TableHasMatchField) {
  // Add a 'good' match field to a table definition.
  pdpi::IrTableDefinition table_def;
  table_def.mutable_match_fields_by_name()->insert(
      {"good_match", pdpi::IrMatchFieldDefinition{}});

  // Then add that table definition to an IrP4Info.
  pdpi::IrP4Info ir_p4info;
  ir_p4info.mutable_tables_by_name()->insert({"good_table", table_def});

  EXPECT_TRUE(pins::TableHasMatchField(ir_p4info, "good_table", "good_match"));
  EXPECT_FALSE(pins::TableHasMatchField(ir_p4info, "bad_table", "good_match"));
  EXPECT_FALSE(pins::TableHasMatchField(ir_p4info, "good_table", "bad_match"));
}

TEST(P4InfoHelperTest, TestGetP4InfoFromSUT) {
  thinkit::MockSwitch mock_switch;
  const pdpi::P4RuntimeSessionOptionalArgs metadata;
  ON_CALL(mock_switch, DeviceId).WillByDefault(Return(100));
  EXPECT_CALL(mock_switch, CreateP4RuntimeStub).WillOnce([=] {
    auto stub = absl::make_unique<p4::v1::MockP4RuntimeStub>();
    MockP4RuntimeSessionCreate(*stub, metadata);
    return stub;
  });
  EXPECT_OK(GetP4InfoFromSUT(mock_switch));
}
}  // namespace
}  // namespace pins
