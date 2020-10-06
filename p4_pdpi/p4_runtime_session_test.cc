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
#include "p4/v1/p4runtime_mock.grpc.pb.h"
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

// One of the tables and actions from
// http://google3/blaze-out/genfiles/third_party/pins_infra/p4_pdpi/testing/test_p4info_embed.cc?l=13
// These need to correspond to the values in our p4info because it is checked
// when sequencing updates to clear tables on the switch.
constexpr uint32_t kTableId = 33554433;
constexpr uint32_t kActionId = 16777217;

// Any constant is fine here.
constexpr uint32_t kDeviceId = 100;

// This is the only action that will work everywhere.
constexpr p4::v1::SetForwardingPipelineConfigRequest::Action
    kForwardingPipelineAction =
        p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT;

p4::v1::Uint128 ConstructElectionId(
    const P4RuntimeSessionOptionalArgs& metadata) {
  p4::v1::Uint128 election_id;
  election_id.set_high(absl::Uint128High64(metadata.election_id));
  election_id.set_low(absl::Uint128Low64(metadata.election_id));
  return election_id;
}

p4::v1::MasterArbitrationUpdate ConstructMasterArbitrationUpdate(
    const P4RuntimeSessionOptionalArgs& metadata) {
  p4::v1::MasterArbitrationUpdate master_arbitration_update;
  *master_arbitration_update.mutable_election_id() =
      ConstructElectionId(metadata);
  master_arbitration_update.set_device_id(kDeviceId);
  master_arbitration_update.mutable_role()->set_name(metadata.role);
  return master_arbitration_update;
}

// Configures the given `MockP4RuntimeStub` such that the given sequence of
// table entries will be returned for the next P4RT Read request.
void SetNextReadResponse(p4::v1::MockP4RuntimeStub& mock_p4rt_stub,
                         std::vector<p4::v1::TableEntry> read_entries) {
  EXPECT_CALL(mock_p4rt_stub, ReadRaw)
      .WillOnce([read_entries = std::move(read_entries)](auto*, auto&) {
        auto* reader =
            new grpc::testing::MockClientReader<p4::v1::ReadResponse>();
        InSequence s;
        for (const auto& entry : read_entries) {
          EXPECT_CALL(*reader, Read)
              .WillOnce([=](p4::v1::ReadResponse* response) -> bool {
                *response->add_entities()->mutable_table_entry() = entry;
                return true;
              });
        }
        EXPECT_CALL(*reader, Read).WillOnce(Return(false));
        EXPECT_CALL(*reader, Finish).WillOnce(Return(grpc::Status::OK));
        return reader;
      });
}

// Configures the given `MockP4RuntimeStub` such that the given sequence of
// table entries will be returned for any P4RT Read request by default.
void SetDefaultReadResponse(p4::v1::MockP4RuntimeStub& mock_p4rt_stub,
                            std::vector<p4::v1::TableEntry> read_entries) {
  ON_CALL(mock_p4rt_stub, ReadRaw)
      .WillByDefault([read_entries = std::move(read_entries)](auto*, auto&) {
        auto* reader =
            new grpc::testing::MockClientReader<p4::v1::ReadResponse>();
        InSequence s;
        for (const auto& entry : read_entries) {
          EXPECT_CALL(*reader, Read)
              .WillOnce([&](p4::v1::ReadResponse* response) -> bool {
                *response->add_entities()->mutable_table_entry() = entry;
                return true;
              });
        }
        EXPECT_CALL(*reader, Read).WillOnce(Return(false));
        EXPECT_CALL(*reader, Finish).WillOnce(Return(grpc::Status::OK));
        return reader;
      });
}

// Mocks a P4RuntimeSession::Create call with a stub by constructing a
// ReaderWriter mock stream and mocking an arbitration handshake. This function
// does not perform any of these operations, it only sets up expectations.
void MockP4RuntimeSessionCreate(p4::v1::MockP4RuntimeStub& stub,
                                const P4RuntimeSessionOptionalArgs& metadata) {
  // The ReaderWriter stream constructed from the stub. This needs to be
  // malloced as it is automatically freed when the unique pointer that it will
  // be wrapped in is freed. The stream is wrapped in StreamChannel, which is
  // the method of the stub that calls StreamChannelRaw, but is not itself
  // mocked.
  auto* stream = new grpc::testing::MockClientReaderWriter<
      p4::v1::StreamMessageRequest, p4::v1::StreamMessageResponse>();
  EXPECT_CALL(stub, StreamChannelRaw).WillOnce(Return(stream));

  // A valid MasterArbitrationUpdate sent as request and response.
  auto master_arbitration_update = ConstructMasterArbitrationUpdate(metadata);

  // Ensures that we write some sort of arbitration request...
  p4::v1::StreamMessageRequest arbitration_request;
  *arbitration_request.mutable_arbitration() = master_arbitration_update;
  EXPECT_CALL(*stream, Write(EqualsProto(arbitration_request), _))
      .WillOnce(Return(true));

  // ... and return a valid response.
  EXPECT_CALL(*stream, Read(_))
      .WillOnce([=](p4::v1::StreamMessageResponse* arbitration_response) {
        *arbitration_response->mutable_arbitration() =
            master_arbitration_update;
        return true;
      });
}

// Constructs a table entry using the predefined table id, kTableId, and action
// id, kActionId.
p4::v1::TableEntry ConstructTableEntry() {
  p4::v1::TableEntry table_entry;
  table_entry.set_table_id(kTableId);
  table_entry.mutable_action()->mutable_action()->set_action_id(kActionId);
  return table_entry;
}

// Sets up a write request to delete the given table entry.
p4::v1::WriteRequest ConstructDeleteRequest(
    const P4RuntimeSessionOptionalArgs& metadata,
    const p4::v1::TableEntry& table_entry) {
  p4::v1::Update delete_update;
  delete_update.set_type(p4::v1::Update::DELETE);
  *delete_update.mutable_entity()->mutable_table_entry() = table_entry;

  p4::v1::WriteRequest delete_request;
  *delete_request.add_updates() = delete_update;
  delete_request.set_device_id(kDeviceId);
  delete_request.set_role(metadata.role);
  *delete_request.mutable_election_id() = ConstructElectionId(metadata);
  return delete_request;
}

// Mocks a `CheckNoEntries` call using the stub in a previously
// mocked P4RuntimeSession.
// Ensures that there are no table entries remaining.
void MockCheckNoEntries(p4::v1::MockP4RuntimeStub& stub,
                        const p4::config::v1::P4Info& p4info) {
  // We need to return a valid p4info to get to the stage where we read tables.
  EXPECT_CALL(stub, GetForwardingPipelineConfig)
      .WillOnce([&](auto, auto,
                    p4::v1::GetForwardingPipelineConfigResponse*
                        get_pipeline_response) {
        *get_pipeline_response->mutable_config()->mutable_p4info() = p4info;
        return grpc::Status::OK;
      });

  SetNextReadResponse(stub, {});
}

// Mocks a ClearTableEntries call using the stub and p4info in a previously
// mocked P4RuntimeSession.
// Pulls the p4info from the switch, then reads a table entry, deletes it, and
// reads again ensuring that there are no table entries remaining.
void MockClearTableEntries(p4::v1::MockP4RuntimeStub& stub,
                           const p4::config::v1::P4Info& p4info,
                           const P4RuntimeSessionOptionalArgs& metadata) {
  // We need to return a valid p4info to get to the stage where we read tables.
  EXPECT_CALL(stub, GetForwardingPipelineConfig)
      .WillOnce([&](auto, auto,
                    p4::v1::GetForwardingPipelineConfigResponse*
                        get_pipeline_response) {
        *get_pipeline_response->mutable_config()->mutable_p4info() = p4info;
        return grpc::Status::OK;
      });

  {
    InSequence s;
    p4::v1::TableEntry table_entry = ConstructTableEntry();

    // We return a table entry so that the function exercises the deletion
    // portion of clearing table entries.
    SetNextReadResponse(stub, {table_entry});

    // Mocks the call to delete table entry that we have created.
    EXPECT_CALL(
        stub,
        Write(_, EqualsProto(ConstructDeleteRequest(metadata, table_entry)), _))
        .Times(1);

    // Mocks a `CheckNoEntries` call, ensuring that the tables are really
    // cleared.
    MockCheckNoEntries(stub, p4info);
  }
}

// Constructs a valid forwarding pipeline config request with the given p4info
// and metadata.
p4::v1::SetForwardingPipelineConfigRequest
ConstructForwardingPipelineConfigRequest(
    const P4RuntimeSessionOptionalArgs& metadata,
    const p4::config::v1::P4Info& p4info,
    absl::optional<absl::string_view> p4_device_config = absl::nullopt) {
  p4::v1::SetForwardingPipelineConfigRequest request;
  request.set_device_id(kDeviceId);
  request.set_role(metadata.role);
  *request.mutable_election_id() = ConstructElectionId(metadata);
  request.set_action(kForwardingPipelineAction);
  *request.mutable_config()->mutable_p4info() = p4info;
  if (p4_device_config.has_value()) {
    *request.mutable_config()->mutable_p4_device_config() = *p4_device_config;
  }
  return request;
}

// An initialized `P4RuntimeSession` together with a `MockP4RuntimeStub` that
// the session is connected to. Useful for testing methods/free functions
// of/on `P4RuntimeSession`.
struct P4SessionWithMockStub {
  std::unique_ptr<P4RuntimeSession> p4rt_session;
  // Owned by the `p4rt_session`.
  p4::v1::MockP4RuntimeStub& mock_p4rt_stub;
};

// Creates a `P4RuntimeSession` based on a mocked `P4RuntimeStub`. Useful for
// testing methods/free functions of/on `P4RuntimeSession`.
absl::StatusOr<P4SessionWithMockStub> MakeP4SessionWithMockStub(
    P4RuntimeSessionOptionalArgs metadata) {
  // No leak: P4RuntimeSession will take ownerhsip.
  auto* mock_p4rt_stub = new testing::NiceMock<p4::v1::MockP4RuntimeStub>();
  MockP4RuntimeSessionCreate(*mock_p4rt_stub, metadata);
  ASSIGN_OR_RETURN(std::unique_ptr<P4RuntimeSession> p4rt_session,
                   P4RuntimeSession::Create(absl::WrapUnique(mock_p4rt_stub),
                                            kDeviceId, metadata));
  testing::Mock::VerifyAndClearExpectations(mock_p4rt_stub);
  return P4SessionWithMockStub{
      .p4rt_session = std::move(p4rt_session),
      .mock_p4rt_stub = *mock_p4rt_stub,
  };
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
                  EqualsProto(ConstructForwardingPipelineConfigRequest(metadata,
                                                                       p4info)),
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
  EXPECT_CALL(mock_p4rt_stub,
              SetForwardingPipelineConfig(
                  _,
                  EqualsProto(ConstructForwardingPipelineConfigRequest(
                      metadata, p4info, p4_device_config)),
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
