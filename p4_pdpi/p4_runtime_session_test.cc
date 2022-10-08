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

#include <cstdint>
#include <memory>
#include <string>
#include <utility>

#include "absl/memory/memory.h"
#include "absl/numeric/int128.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/types/span.h"
#include "gmock/gmock.h"
#include "google/protobuf/repeated_field.h"
#include "grpcpp/test/mock_stream.h"
#include "gtest/gtest.h"
#include "gutil/proto.h"
#include "gutil/proto_matchers.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/p4_runtime_session_mocking.h"
#include "p4_pdpi/testing/test_p4info.h"

namespace pdpi {
namespace {

using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::_;
using ::testing::ByMove;
using ::testing::EqualsProto;
using ::testing::InSequence;
using ::testing::Return;

// This is the only action that will work everywhere.
constexpr p4::v1::SetForwardingPipelineConfigRequest::Action
    kForwardingPipelineAction =
        p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT;

// Tests that CreateWithP4InfoAndClearTables creates a P4RuntimeSession,
// clears all table entries currently on the switch (mocked to be one), and
// pushes a new p4info.
TEST(P4RuntimeSessionTest, CreateWithP4InfoAndClearTables) {
  const p4::config::v1::P4Info& p4info = GetTestP4Info();
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

    // Mocks a `ClearTableEntries` call.
    // Pulls the p4info from the switch, then reads a table entry, deletes it,
    // and reads again ensuring that there are no table entries remaining.
    MockClearTableEntries(*stub, p4info, metadata);

    // Mocks a `SetForwardingPipelineConfig` call.
    EXPECT_CALL(*stub, SetForwardingPipelineConfig(
                           _,
                           EqualsProto(ConstructForwardingPipelineConfigRequest(
                               metadata, p4info, kForwardingPipelineAction)),
                           _))
        .Times(1);

    // Mocks a `CheckNoEntries` call.
    MockCheckNoEntries(*stub, p4info);
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
  SetDefaultReadResponse(mock_p4rt_stub, {});

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
  ASSERT_OK_AND_ASSIGN(const auto counter_data2,
                       gutil::ParseTextProto<p4::v1::CounterData>(R"pb(
                         byte_count: 420
                         packet_count: 100
                       )pb"));
  p4::v1::TableEntry entry1 = ConstructTableEntry();
  *entry1.mutable_counter_data() = counter_data1;
  p4::v1::TableEntry entry2 = ConstructTableEntry();
  // Change the signature of entry2 compared to entry1 in some arbitrary way.
  entry2.add_match()->mutable_exact()->set_value("123");
  *entry2.mutable_counter_data() = counter_data2;
  SetDefaultReadResponse(mock_p4rt_stub, {entry1, entry2});

  // Actual test: counters are read back correctly.
  p4::v1::TableEntry target_entry_signature1 = entry1;
  p4::v1::TableEntry target_entry_signature2 = entry2;
  EXPECT_THAT(ReadPiCounterData(p4rt_session.get(), target_entry_signature1),
              IsOkAndHolds(EqualsProto(counter_data1)));
  EXPECT_THAT(ReadPiCounterData(p4rt_session.get(), target_entry_signature2),
              IsOkAndHolds(EqualsProto(counter_data2)));
  // Clearing the action & counter data in the signature should not matter, as
  // these fields are ignored.
  target_entry_signature1.clear_action();
  target_entry_signature2.clear_action();
  target_entry_signature1.clear_counter_data();
  target_entry_signature2.clear_counter_data();
  EXPECT_THAT(ReadPiCounterData(p4rt_session.get(), target_entry_signature1),
              gutil::IsOkAndHolds(EqualsProto(counter_data1)));
  EXPECT_THAT(ReadPiCounterData(p4rt_session.get(), target_entry_signature2),
              gutil::IsOkAndHolds(EqualsProto(counter_data2)));
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
  ASSERT_OK(SetForwardingPipelineConfig(p4rt_session.get(),
                                        kForwardingPipelineAction, p4info));
  p4::v1::ForwardingPipelineConfig config;
  *config.mutable_p4info() = p4info;
  ASSERT_OK(SetForwardingPipelineConfig(p4rt_session.get(),
                                        kForwardingPipelineAction, config));

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
  ASSERT_OK(SetForwardingPipelineConfig(
      p4rt_session.get(), kForwardingPipelineAction, p4info, p4_device_config));
  *config.mutable_p4_device_config() = p4_device_config;
  ASSERT_OK(SetForwardingPipelineConfig(p4rt_session.get(),
                                        kForwardingPipelineAction, config));
}

}  // namespace
}  // namespace pdpi
