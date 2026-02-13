// Copyright 2020 Google LLC
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

#include "p4_pdpi/p4_runtime_session.h"

#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/memory/memory.h"
#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "grpcpp/support/status.h"
#include "gtest/gtest.h"
#include "gutil/proto.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/p4_runtime_session_mocking.h"
#include "p4_pdpi/testing/test_p4info.h"

namespace pdpi {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOk;
using ::gutil::IsOkAndHolds;
using ::gutil::Partially;
using ::gutil::StatusIs;
using ::testing::_;
using ::testing::ByMove;
using ::testing::Eq;
using ::testing::InSequence;
using ::testing::Return;

// This is the only action that will work everywhere.
constexpr p4::v1::SetForwardingPipelineConfigRequest::Action
    kForwardingPipelineAction =
        p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT;

// Tests that CreateWithP4InfoAndClearTables creates a P4RuntimeSession,
// clears all entities currently on the switch (mocked to be two), and
// pushes a new p4info.
TEST(P4RuntimeSessionTest, CreateWithP4InfoAndClearTables) {
  p4::config::v1::P4Info p4info = GetTestP4Info();
  const P4RuntimeSessionOptionalArgs metadata;
  thinkit::MockSwitch mock_switch;

  // The stub that will be returned when CreateP4RuntimeStub is called on
  // mock_switch.
  auto stub = absl::make_unique<p4::v1::MockP4RuntimeStub>();
  ASSERT_NE(stub, nullptr);
  {
    InSequence s;
    // Mocks a P4RuntimeSession `Create` call.
    // Constructs a ReaderWriter mock stream and completes an arbitration
    // handshake.
    MockP4RuntimeSessionCreate(*stub, metadata);

    // Mocks a `ClearEntities` call.
    // Pulls the p4info from the switch, then reads a table entry and a
    // multicast entity, deletes them, and reads again ensuring that there are
    // no entities remaining.
    MockClearEntities(*stub, p4info, metadata);

    // Mocks a `SetForwardingPipelineConfig` call.
    EXPECT_CALL(*stub, SetForwardingPipelineConfig(
                           _,
                           EqualsProto(ConstructForwardingPipelineConfigRequest(
                               metadata, p4info, kForwardingPipelineAction)),
                           _))
        .Times(1);

    // Mocks a `CheckNoEntities` call.
    MockCheckNoEntities(*stub, p4info);
  }

  // Mocks the first part of a P4RuntimeSession `Create` call.
  EXPECT_CALL(mock_switch, CreateP4RuntimeStub())
      .WillOnce(Return(ByMove(std::move(stub))));
  EXPECT_CALL(mock_switch, DeviceId).WillOnce(Return(kDeviceId));

  // The main function call through which everything else should happen.
  ASSERT_OK_AND_ASSIGN(auto session,
                       P4RuntimeSession::CreateWithP4InfoAndClearTables(
                           mock_switch, p4info, metadata));
}

TEST(ReadPiCounterDataTest, ReturnsNotFoundWhenNoEntriesPresent) {
  const P4RuntimeSessionOptionalArgs metadata;

  // Get mock.
  ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                       MakeP4SessionWithMockStub(metadata));

  // Mock that no table entries are installed on the switch.
  SetDefaultReadResponse(mock_p4rt_stub, std::vector<p4::v1::TableEntry>());

  // Actual test: without table entries, expect reading counter to fail.
  p4::v1::TableEntry target_entry_signature;
  target_entry_signature.set_table_id(1);
  EXPECT_THAT(ReadPiCounterData(p4rt_session.get(), target_entry_signature),
              StatusIs(absl::StatusCode::kNotFound));
}

TEST(ReadPiCounterDataTest, ReturnsNotFoundWhenNoMatchingEntryPresent) {
  const P4RuntimeSessionOptionalArgs metadata;

  // Get mock.
  ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                       MakeP4SessionWithMockStub(metadata));

  // Mock that a table entry is installed on the switch.
  const p4::v1::TableEntry entry = ConstructTableEntry();
  SetDefaultReadResponse(mock_p4rt_stub, {entry});

  // Actual test: expect reading counter to fail when there are no matching
  // table entries.
  {
    p4::v1::TableEntry target_entry_signature = entry;
    target_entry_signature.set_table_id(entry.table_id() + 1);
    EXPECT_THAT(ReadPiCounterData(p4rt_session.get(), target_entry_signature),
                StatusIs(absl::StatusCode::kNotFound));
  }
  {
    p4::v1::TableEntry target_entry_signature = entry;
    target_entry_signature.set_priority(entry.priority() + 1);
    EXPECT_THAT(ReadPiCounterData(p4rt_session.get(), target_entry_signature),
                StatusIs(absl::StatusCode::kNotFound));
  }
  {
    p4::v1::TableEntry target_entry_signature = entry;
    target_entry_signature.add_match()->mutable_exact()->set_value("random");
    EXPECT_THAT(ReadPiCounterData(p4rt_session.get(), target_entry_signature),
                StatusIs(absl::StatusCode::kNotFound));
  }
}

TEST(ReadPiCounterDataTest, ReturnsCorrectCounterForSignature) {
  const P4RuntimeSessionOptionalArgs metadata;

  // Get mock.
  ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                       MakeP4SessionWithMockStub(metadata));

  // Mock that two table entries in the same table are installed on the switch.
  ASSERT_OK_AND_ASSIGN(const auto counter_data1,
                       gutil::ParseTextProto<p4::v1::CounterData>(R"pb(
                         byte_count: 42
                         packet_count: 10
                       )pb"));
  ASSERT_OK_AND_ASSIGN(const auto meter_counter_data1,
                       gutil::ParseTextProto<p4::v1::MeterCounterData>(R"pb(
                         green { byte_count: 42 packet_count: 10 }
                         yellow { byte_count: 0 packet_count: 0 }
                         red { byte_count: 300 packet_count: 100 }
                       )pb"));
  ASSERT_OK_AND_ASSIGN(const auto counter_data2,
                       gutil::ParseTextProto<p4::v1::CounterData>(R"pb(
                         byte_count: 420
                         packet_count: 100
                       )pb"));
  ASSERT_OK_AND_ASSIGN(const auto meter_counter_data2,
                       gutil::ParseTextProto<p4::v1::MeterCounterData>(R"pb(
                         green { byte_count: 32 packet_count: 12 }
                         yellow { byte_count: 0 packet_count: 0 }
                         red { byte_count: 400 packet_count: 150 }
                       )pb"));
  p4::v1::TableEntry entry1 = ConstructTableEntry();
  *entry1.mutable_counter_data() = counter_data1;
  *entry1.mutable_meter_counter_data() = meter_counter_data1;
  p4::v1::TableEntry entry2 = ConstructTableEntry();
  // Change the signature of entry2 compared to entry1 in some arbitrary way.
  entry2.add_match()->mutable_exact()->set_value("123");
  *entry2.mutable_counter_data() = counter_data2;
  *entry2.mutable_meter_counter_data() = meter_counter_data2;
  SetDefaultReadResponse(mock_p4rt_stub, {entry1, entry2});

  // Actual test: counters are read back correctly.
  p4::v1::TableEntry target_entry_signature1 = entry1;
  p4::v1::TableEntry target_entry_signature2 = entry2;
  EXPECT_THAT(ReadPiCounterData(p4rt_session.get(), target_entry_signature1),
              IsOkAndHolds(EqualsProto(counter_data1)));
  EXPECT_THAT(
      ReadPiMeterCounterData(p4rt_session.get(), target_entry_signature1),
      IsOkAndHolds(EqualsProto(meter_counter_data1)));
  EXPECT_THAT(ReadPiCounterData(p4rt_session.get(), target_entry_signature2),
              IsOkAndHolds(EqualsProto(counter_data2)));
  EXPECT_THAT(
      ReadPiMeterCounterData(p4rt_session.get(), target_entry_signature2),
      IsOkAndHolds(EqualsProto(meter_counter_data2)));
  // Clearing the action & counter data in the signature should not matter, as
  // these fields are ignored.
  target_entry_signature1.clear_action();
  target_entry_signature2.clear_action();
  target_entry_signature1.clear_counter_data();
  target_entry_signature2.clear_counter_data();
  target_entry_signature1.clear_meter_counter_data();
  target_entry_signature2.clear_meter_counter_data();
  EXPECT_THAT(ReadPiCounterData(p4rt_session.get(), target_entry_signature1),
              gutil::IsOkAndHolds(EqualsProto(counter_data1)));
  EXPECT_THAT(ReadPiCounterData(p4rt_session.get(), target_entry_signature2),
              gutil::IsOkAndHolds(EqualsProto(counter_data2)));
  EXPECT_THAT(
      ReadPiMeterCounterData(p4rt_session.get(), target_entry_signature1),
      IsOkAndHolds(EqualsProto(meter_counter_data1)));
  EXPECT_THAT(
      ReadPiMeterCounterData(p4rt_session.get(), target_entry_signature2),
      IsOkAndHolds(EqualsProto(meter_counter_data2)));
}

TEST(SetForwardingPipelineConfigTest, BothVersionsProduceSameRequest) {
  const p4::config::v1::P4Info& p4info = GetTestP4Info();
  const P4RuntimeSessionOptionalArgs metadata;

  // Get mock.
  ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                       MakeP4SessionWithMockStub(metadata));

  // Mocks two `SetForwardingPipelineConfig` calls without a `p4_device_config`.
  EXPECT_CALL(mock_p4rt_stub,
              SetForwardingPipelineConfig(
                  _,
                  EqualsProto(ConstructForwardingPipelineConfigRequest(
                      metadata, p4info, kForwardingPipelineAction)),
                  _))
      .Times(2);

  // Ensures that both versions of the function send the same proto.
  ASSERT_OK(SetMetadataAndSetForwardingPipelineConfig(
      p4rt_session.get(), kForwardingPipelineAction, p4info));
  p4::v1::ForwardingPipelineConfig config;
  *config.mutable_p4info() = p4info;
  ASSERT_OK(SetMetadataAndSetForwardingPipelineConfig(
      p4rt_session.get(), kForwardingPipelineAction, config));

  std::string p4_device_config = "some_json_device_config";
  // Mocks two `SetForwardingPipelineConfig` calls with a `p4_device_config`.
  EXPECT_CALL(
      mock_p4rt_stub,
      SetForwardingPipelineConfig(
          _,
          EqualsProto(ConstructForwardingPipelineConfigRequest(
              metadata, p4info, kForwardingPipelineAction, p4_device_config)),
          _))
      .Times(2);

  // Ensures that both versions of the function send the same proto.
  ASSERT_OK(SetMetadataAndSetForwardingPipelineConfig(
      p4rt_session.get(), kForwardingPipelineAction, p4info, p4_device_config));
  *config.mutable_p4_device_config() = p4_device_config;
  ASSERT_OK(SetMetadataAndSetForwardingPipelineConfig(
      p4rt_session.get(), kForwardingPipelineAction, config));
}

TEST(ClearTableEntryCountersTest, SendsNoWriteRequestWhenNoCountersAreNonZero) {
  const P4RuntimeSessionOptionalArgs metadata;

  // Get mock.
  ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                       MakeP4SessionWithMockStub(metadata));

  // Mock table entry with no non-zero counters in read response.
  p4::v1::TableEntry entry = ConstructTableEntry();
  entry.clear_counter_data();
  entry.clear_meter_counter_data();
  SetDefaultReadResponse(mock_p4rt_stub, {entry});

  // Expect no write request.
  EXPECT_CALL(mock_p4rt_stub, Write).Times(0);
  EXPECT_THAT(ClearTableEntryCounters(*p4rt_session), IsOk());
}

TEST(ClearTableEntryCountersTest,
     SendsModifyRequestsWhenUncoloredOrColoredCountersAreNonZero) {
  const P4RuntimeSessionOptionalArgs metadata;

  // Get mock.
  ASSERT_OK_AND_ASSIGN((auto [p4rt_session, mock_p4rt_stub]),
                       MakeP4SessionWithMockStub(metadata));

  // Mock 5 table entries with different non-zero counters.
  p4::v1::TableEntry entry1 = ConstructTableEntry();
  p4::v1::TableEntry entry2 = ConstructTableEntry();
  p4::v1::TableEntry entry3 = ConstructTableEntry();
  p4::v1::TableEntry entry4 = ConstructTableEntry();
  p4::v1::TableEntry entry5 = ConstructTableEntry();
  p4::v1::TableEntry entry6 = ConstructTableEntry();
  // Entry 1: uncolored byte count non-zero.
  entry1.mutable_counter_data()->set_byte_count(42);
  entry1.clear_meter_counter_data();
  // Entry 2: uncolored packet count non-zero.
  entry2.mutable_counter_data()->set_packet_count(42);
  entry2.clear_meter_counter_data();
  // Entry 3: green byte count non-zero.
  entry3.clear_counter_data();
  entry3.mutable_meter_counter_data()->mutable_green()->set_byte_count(42);
  // Entry 4: yellow packet count non-zero.
  entry4.clear_counter_data();
  entry4.mutable_meter_counter_data()->mutable_yellow()->set_packet_count(42);
  // Entry 5: red byte count non-zero.
  entry5.clear_counter_data();
  entry5.mutable_meter_counter_data()->mutable_red()->set_packet_count(42);
  // Entry 6: uncolored + colored counters non-zero.
  entry6.clear_counter_data();
  entry6.mutable_counter_data()->set_byte_count(42);
  entry6.mutable_meter_counter_data()->mutable_red()->set_packet_count(24);
  SetNextReadResponse(mock_p4rt_stub,
                      {entry1, entry2, entry3, entry4, entry5, entry6});

  // Expect MODIFY clearing `counter_data` fields.
  EXPECT_CALL(
      mock_p4rt_stub,
      Write(
          _, Partially(EqualsProto(R"pb(
            updates {
              type: MODIFY
              entity {
                table_entry { counter_data { byte_count: 0 packet_count: 0 } }
              }
            }
            updates {
              type: MODIFY
              entity {
                table_entry { counter_data { byte_count: 0 packet_count: 0 } }
              }
            }
            updates {
              type: MODIFY
              entity {
                table_entry {
                  meter_counter_data { green { byte_count: 0 packet_count: 0 } }
                }
              }
            }
            updates {
              type: MODIFY
              entity {
                table_entry {
                  meter_counter_data {
                    yellow { byte_count: 0 packet_count: 0 }
                  }
                }
              }
            }
            updates {
              type: MODIFY
              entity {
                table_entry {
                  meter_counter_data { red { byte_count: 0 packet_count: 0 } }
                }
              }
            }
            updates {
              type: MODIFY
              entity {
                table_entry {
                  counter_data { byte_count: 0 packet_count: 0 }
                  meter_counter_data { red { byte_count: 0 packet_count: 0 } }
                }
              }
            }
          )pb")),
          _))
      .Times(1)
      .WillOnce([&](const auto*, const p4::v1::WriteRequest& request,
                    const auto*) {
        EXPECT_THAT(request.updates_size(), Eq(6));
        EXPECT_THAT(
            gutil::ProtoDiff(entry1, request.updates(0).entity().table_entry()),
            IsOkAndHolds(Eq("deleted: counter_data.byte_count: 42\n")));
        EXPECT_THAT(
            gutil::ProtoDiff(entry2, request.updates(1).entity().table_entry()),
            IsOkAndHolds(Eq("deleted: counter_data.packet_count: 42\n")));
        EXPECT_THAT(
            gutil::ProtoDiff(entry3, request.updates(2).entity().table_entry()),
            IsOkAndHolds(
                Eq("deleted: meter_counter_data.green.byte_count: 42\n")));
        EXPECT_THAT(
            gutil::ProtoDiff(entry4, request.updates(3).entity().table_entry()),
            IsOkAndHolds(
                Eq("deleted: meter_counter_data.yellow.packet_count: 42\n")));
        EXPECT_THAT(
            gutil::ProtoDiff(entry5, request.updates(4).entity().table_entry()),
            IsOkAndHolds(
                Eq("deleted: meter_counter_data.red.packet_count: 42\n")));
        EXPECT_THAT(
            gutil::ProtoDiff(entry6, request.updates(5).entity().table_entry()),
            IsOkAndHolds(
                Eq("deleted: counter_data.byte_count: 42\n"
                   "deleted: meter_counter_data.red.packet_count: 24\n")));
        return grpc::Status::OK;
      });
  EXPECT_THAT(ClearTableEntryCounters(*p4rt_session), IsOk());
}

}  // namespace
}  // namespace pdpi
