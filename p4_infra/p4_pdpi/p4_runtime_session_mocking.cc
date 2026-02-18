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

#include "p4_infra/p4_pdpi/p4_runtime_session_mocking.h"

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "absl/numeric/int128.h"
#include "absl/strings/string_view.h"
#include "absl/synchronization/notification.h"
#include "absl/time/time.h"
#include "absl/types/optional.h"
#include "gmock/gmock.h"
#include "grpcpp/support/status.h"
#include "grpcpp/test/mock_stream.h"
#include "gtest/gtest.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4/v1/p4runtime_mock.grpc.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
// TODO: Remove version setting once the version check in
// `p4_runtime_session.cc` is removed.
#include "sai_p4/instantiations/google/versions.h"

namespace pdpi {

namespace {

using ::p4::config::v1::P4Info;
using ::testing::_;
using ::testing::EqualsProto;
using ::testing::InSequence;
using ::testing::Return;

// One of the tables and actions from
// http://google3/blaze-out/genfiles/third_party/pins_infra/p4_infra/p4_infra/p4_infra/p4_infra/p4_pdpi/testing/test_p4info_embed.cc?l=13
// These need to correspond to the values in our p4info because it is checked
// when sequencing updates to clear tables on the switch.
constexpr uint32_t kTableId = 33554433;
constexpr uint32_t kActionId = 16777217;

// Arbitrarily chosen.
constexpr uint32_t kMulticastGroupId = 1;
constexpr uint32_t kMulticastGroupReplicaInstance = 2;
constexpr absl::string_view kMulticastGroupReplicaPort = "3";

}  // namespace

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

void SetNextReadResponse(p4::v1::MockP4RuntimeStub& mock_p4rt_stub,
                         std::vector<p4::v1::Entity> read_entities) {
  EXPECT_CALL(mock_p4rt_stub, ReadRaw)
      .WillOnce([read_entities = std::move(read_entities)](auto*, auto&) {
        auto* reader =
            new grpc::testing::MockClientReader<p4::v1::ReadResponse>();
        InSequence s;
        EXPECT_CALL(*reader, Read)
            .WillOnce([=](p4::v1::ReadResponse* response) -> bool {
              for (const auto& entity : read_entities) {
                *response->add_entities() = entity;
              }
              return true;
            });
        EXPECT_CALL(*reader, Read).WillOnce(Return(false));
        EXPECT_CALL(*reader, Finish).WillOnce(Return(grpc::Status::OK));
        return reader;
      });
}

void SetDefaultReadResponse(p4::v1::MockP4RuntimeStub& mock_p4rt_stub,
                            std::vector<p4::v1::Entity> read_entities) {
  ON_CALL(mock_p4rt_stub, ReadRaw)
      .WillByDefault([read_entities = std::move(read_entities)](auto*, auto&) {
        auto* reader =
            new grpc::testing::MockClientReader<p4::v1::ReadResponse>();
        InSequence s;
        for (const auto& entity : read_entities) {
          EXPECT_CALL(*reader, Read)
              .WillOnce([&](p4::v1::ReadResponse* response) -> bool {
                *response->add_entities() = entity;
                return true;
              });
        }
        EXPECT_CALL(*reader, Read).WillOnce(Return(false));
        EXPECT_CALL(*reader, Finish).WillOnce(Return(grpc::Status::OK));
        return reader;
      });
}

void SetNextReadResponse(p4::v1::MockP4RuntimeStub& mock_p4rt_stub,
                         std::vector<p4::v1::TableEntry> read_entries) {
  std::vector<p4::v1::Entity> read_entities;
  read_entities.reserve(read_entries.size());
  for (const auto& entry : read_entries) {
    *read_entities.emplace_back().mutable_table_entry() = entry;
  }
  SetNextReadResponse(mock_p4rt_stub, read_entities);
}

void SetDefaultReadResponse(p4::v1::MockP4RuntimeStub& mock_p4rt_stub,
                            std::vector<p4::v1::TableEntry> read_entries) {
  std::vector<p4::v1::Entity> read_entities;
  read_entities.reserve(read_entries.size());
  for (const auto& entry : read_entries) {
    *read_entities.emplace_back().mutable_table_entry() = entry;
  }
  SetDefaultReadResponse(mock_p4rt_stub, read_entities);
}

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

  // To ensure "causality", i.e. that the switch's arbitration response is only
  // sent after receiving an arbitration request, we need to synchronize the
  // following `Write`/`Read` EXPECT_CALL/ON_CALL expectations.
  // We do so via thread-safe notifications wrapped in shared pointers, which
  // the expectations capture by value, to ensure the expectations will not
  // outlive the notifications.
  auto sent_arbitration = std::make_shared<absl::Notification>();
  auto sent_arbitration_response = std::make_shared<absl::Notification>();

  // A valid MasterArbitrationUpdate sent as request and response.
  auto master_arbitration_update = ConstructMasterArbitrationUpdate(metadata);

  // Ensures that we write some sort of arbitration request...
  p4::v1::StreamMessageRequest arbitration_request;
  *arbitration_request.mutable_arbitration() = master_arbitration_update;
  EXPECT_CALL(*stream, Write(EqualsProto(arbitration_request), _))
      .WillOnce([=](auto, auto) {
        sent_arbitration->Notify();
        return true;
      });

  // ... and return a valid response.
  ON_CALL(*stream, Read(_))
      .WillByDefault([=](p4::v1::StreamMessageResponse* arbitration_response) {
        // Send arbitration reponse exactly once...
        if (sent_arbitration_response->HasBeenNotified()) return false;
        sent_arbitration_response->Notify();
        // ... and only after the arbitration request has been received.
        EXPECT_TRUE(
            sent_arbitration->WaitForNotificationWithTimeout(absl::Seconds(15)))
            << "expected arbitration request did not occur within 15 seconds";
        *arbitration_response->mutable_arbitration() =
            master_arbitration_update;
        return true;
      });
}

p4::v1::TableEntry ConstructTableEntry() {
  p4::v1::TableEntry table_entry;
  table_entry.set_table_id(kTableId);
  table_entry.mutable_action()->mutable_action()->set_action_id(kActionId);
  return table_entry;
}

p4::v1::Entity ConstructMulticastEntity() {
  p4::v1::Entity entity;
  p4::v1::MulticastGroupEntry* multicast_entry =
      entity.mutable_packet_replication_engine_entry()
          ->mutable_multicast_group_entry();
  multicast_entry->set_multicast_group_id(kMulticastGroupId);
  multicast_entry->add_replicas()->set_instance(kMulticastGroupReplicaInstance);
  multicast_entry->mutable_replicas(0)->set_port(kMulticastGroupReplicaPort);
  return entity;
}

p4::v1::WriteRequest ConstructDeleteRequest(
    const P4RuntimeSessionOptionalArgs& metadata,
    const std::vector<p4::v1::Entity>& entities) {
  p4::v1::WriteRequest delete_request;
  delete_request.set_device_id(kDeviceId);
  delete_request.set_role(metadata.role);
  *delete_request.mutable_election_id() = ConstructElectionId(metadata);

  for (const p4::v1::Entity& entity : entities) {
    p4::v1::Update* delete_update = delete_request.add_updates();
    delete_update->set_type(p4::v1::Update::DELETE);
    *delete_update->mutable_entity() = entity;
  }

  return delete_request;
}

void MockCheckNoEntities(p4::v1::MockP4RuntimeStub& stub,
                         std::optional<P4Info> p4info) {
  // We need to return a valid p4info to get to the stage where we read
  // entities.
  EXPECT_CALL(stub, GetForwardingPipelineConfig)
      .WillOnce([=](auto, auto,
                    p4::v1::GetForwardingPipelineConfigResponse*
                        get_pipeline_response) {
        *get_pipeline_response->mutable_config()->mutable_p4info() =
            p4info.value_or(P4Info());
        return grpc::Status::OK;
      });

  SetNextReadResponse(stub, std::vector<p4::v1::Entity>());
}

void MockClearEntities(p4::v1::MockP4RuntimeStub& stub, const P4Info& p4info,
                       const P4RuntimeSessionOptionalArgs& metadata) {
  // We need to return a valid p4info to get to the stage where we read
  // entities.
  EXPECT_CALL(stub, GetForwardingPipelineConfig)
      .WillOnce([&](auto, auto,
                    p4::v1::GetForwardingPipelineConfigResponse*
                        get_pipeline_response) {
        *get_pipeline_response->mutable_config()->mutable_p4info() = p4info;
        // TODO: Remove version setting once the version check in
        // `p4_runtime_session.cc` is removed.
        get_pipeline_response->mutable_config()
            ->mutable_p4info()
            ->mutable_pkg_info()
            ->set_version(SAI_P4_PKGINFO_VERSION_USES_FAIL_ON_FIRST);
        return grpc::Status::OK;
      });

  {
    InSequence s;
    p4::v1::Entity table_entity;
    *table_entity.mutable_table_entry() = ConstructTableEntry();
    p4::v1::Entity multicast_entity = ConstructMulticastEntity();

    // We return two entities so that the function exercises the deletion
    // portion of clearing entities.
    SetNextReadResponse(stub, {table_entity, multicast_entity});

    // Mocks the call to delete the entities that we have created, in reverse
    // dependency order.
    EXPECT_CALL(stub, Write(_,
                            EqualsProto(ConstructDeleteRequest(
                                metadata, {multicast_entity, table_entity})),
                            _))
        .Times(1);

    // Mocks a `CheckNoEntities` call, ensuring that the entities are really
    // cleared.
    MockCheckNoEntities(stub, p4info);
  }
}

void MockCheckNoEntries(p4::v1::MockP4RuntimeStub& stub,
                        std::optional<P4Info> p4info) {
  // We need to return a valid p4info to get to the stage where we read tables.
  EXPECT_CALL(stub, GetForwardingPipelineConfig)
      .WillOnce([=](auto, auto,
                    p4::v1::GetForwardingPipelineConfigResponse*
                        get_pipeline_response) {
        *get_pipeline_response->mutable_config()->mutable_p4info() =
            p4info.value_or(P4Info());
        return grpc::Status::OK;
      });

  SetNextReadResponse(stub, std::vector<p4::v1::TableEntry>());
}

void MockClearTableEntries(p4::v1::MockP4RuntimeStub& stub,
                           const P4Info& p4info,
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
    p4::v1::Entity table_entity;
    *table_entity.mutable_table_entry() = ConstructTableEntry();

    // We return the table entity so that the function exercises the deletion
    // portion to clear it.
    SetNextReadResponse(stub, {table_entity});

    // Mocks the call to delete the table_entity that we have created.
    EXPECT_CALL(
        stub,
        Write(_, EqualsProto(ConstructDeleteRequest(metadata, {table_entity})),
              _))
        .Times(1);

    // Mocks a `CheckNoEntries` call, ensuring that the tables are really
    // cleared.
    MockCheckNoEntries(stub, p4info);
  }
}

p4::v1::SetForwardingPipelineConfigRequest
ConstructForwardingPipelineConfigRequest(
    const P4RuntimeSessionOptionalArgs& metadata, const P4Info& p4info,
    p4::v1::SetForwardingPipelineConfigRequest::Action action,
    absl::optional<absl::string_view> p4_device_config) {
  p4::v1::SetForwardingPipelineConfigRequest request;
  request.set_device_id(kDeviceId);
  request.set_role(metadata.role);
  *request.mutable_election_id() = ConstructElectionId(metadata);
  request.set_action(action);
  *request.mutable_config()->mutable_p4info() = p4info;
  if (p4_device_config.has_value()) {
    *request.mutable_config()->mutable_p4_device_config() = *p4_device_config;
  }
  return request;
}

absl::StatusOr<P4SessionWithMockStub> MakeP4SessionWithMockStub(
    const P4RuntimeSessionOptionalArgs& metadata) {
  // No leak: P4RuntimeSession will take ownership.
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

}  // namespace pdpi
