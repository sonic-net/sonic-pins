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
#include <memory>

#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4rt_app/tests/lib/p4runtime_component_test_fixture.h"
#include "p4rt_app/tests/lib/p4runtime_grpc_service.h"
#include "p4rt_app/tests/lib/p4runtime_request_helpers.h"
#include "sai_p4/instantiations/google/instantiations.h"

namespace p4rt_app {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOk;
using ::gutil::StatusIs;
using ::testing::HasSubstr;
using ::testing::IsEmpty;
using ::testing::Not;

class PacketReplicationTableTest
    : public test_lib::P4RuntimeComponentTestFixture {
 protected:
  PacketReplicationTableTest()
      : test_lib::P4RuntimeComponentTestFixture(
            sai::Instantiation::kMiddleblock) {}
};

TEST_F(PacketReplicationTableTest, InsertReadAndDeleteEntry) {
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet0", "1"));
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet1", "2"));

  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::IrWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               entity {
                                 packet_replication_engine_entry {
                                   multicast_group_entry {
                                     multicast_group_id: 1
                                     replicas { port: "1" instance: 0 }
                                     replicas { port: "2" instance: 0 }
                                   }
                                 }
                               }
                             })pb",
                           ir_p4_info_));

  // Create the packet replication entry, and check that it exists in the
  // REPLICATION_IP_MULTICAST_TABLE.
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));

  const auto expected_key1 = "REPLICATION_IP_MULTICAST_TABLE:0x0001";

  ASSERT_OK(p4rt_service_.GetP4rtAppDbTable().ReadTableEntry(expected_key1))
      << "Unable to read entry for " << expected_key1;

  // Read back the entry which should result in the same packet replication
  // entry.
  p4::v1::ReadRequest read_request;
  read_request.add_entities()
      ->mutable_packet_replication_engine_entry()
      ->mutable_multicast_group_entry();
  ASSERT_OK_AND_ASSIGN(
      p4::v1::ReadResponse read_response,
      pdpi::SetMetadataAndSendPiReadRequest(p4rt_session_.get(), read_request));
  ASSERT_EQ(read_response.entities_size(), 1);  // Only one entity.
  EXPECT_THAT(read_response.entities(0),
              EqualsProto(request.updates(0).entity()));

  // Delete the multicast group entry, and do a sanity check that it is gone.
  request.mutable_updates(0)->set_type(p4::v1::Update::DELETE);
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));
  ASSERT_THAT(p4rt_service_.GetP4rtAppDbTable().ReadTableEntry(expected_key1),
              StatusIs(absl::StatusCode::kNotFound))
      << "Multicast group was not deleted: " << expected_key1;
}

TEST_F(PacketReplicationTableTest, CannotInsertDuplicateEntries) {
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet0", "1"));
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet1", "2"));
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::IrWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               entity {
                                 packet_replication_engine_entry {
                                   multicast_group_entry {
                                     multicast_group_id: 1
                                     replicas { port: "1" instance: 0 }
                                     replicas { port: "2" instance: 0 }
                                   }
                                 }
                               }
                             })pb",
                           ir_p4_info_));
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kUnknown, HasSubstr("#1: ALREADY_EXISTS")));
}

TEST_F(PacketReplicationTableTest, InsertRequestFails) {
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet0", "1"));
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet1", "2"));
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::IrWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               entity {
                                 packet_replication_engine_entry {
                                   multicast_group_entry {
                                     multicast_group_id: 17
                                     replicas { port: "1" instance: 0 }
                                     replicas { port: "2" instance: 0 }
                                   }
                                 }
                               }
                             })pb",
                           ir_p4_info_));

  const auto expected_key1 = "REPLICATION_IP_MULTICAST_TABLE:0x0011";

  // Assume the Orchagent fails with an invalid parameter.
  p4rt_service_.GetP4rtAppDbTable().SetResponseForKey(
      expected_key1, "SWSS_RC_INVALID_PARAM", "my error message");

  // We expect the invalid argument error to be propagated all the way back to
  // the gRPC response.
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kUnknown,
               HasSubstr("#1: INVALID_ARGUMENT: my error message")));

  // Sanity check that the entry is not accidentally left in replication table.
  ASSERT_THAT(p4rt_service_.GetP4rtAppDbTable().ReadTableEntry(expected_key1),
              StatusIs(absl::StatusCode::kNotFound))
      << "Packet replication DB entry was not cleaned up after failure: "
      << expected_key1;
}

TEST_F(PacketReplicationTableTest, CannotDeleteMissingEntry) {
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet0", "1"));
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet1", "2"));
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::IrWriteRequestToPi(
                           R"pb(
                             updates {
                               type: DELETE
                               entity {
                                 packet_replication_engine_entry {
                                   multicast_group_entry {
                                     multicast_group_id: 1
                                     replicas { port: "1" instance: 0 }
                                     replicas { port: "2" instance: 0 }
                                   }
                                 }
                               }
                             })pb",
                           ir_p4_info_));
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kUnknown, HasSubstr("#1: NOT_FOUND")));
}

TEST_F(PacketReplicationTableTest, DeleteRequestFails) {
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet0", "1"));
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet1", "2"));
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::IrWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               entity {
                                 packet_replication_engine_entry {
                                   multicast_group_entry {
                                     multicast_group_id: 1
                                     replicas { port: "1" instance: 0 }
                                     replicas { port: "2" instance: 0 }
                                   }
                                 }
                               }
                             })pb",
                           ir_p4_info_));

  const auto expected_key1 = "REPLICATION_IP_MULTICAST_TABLE:0x0001";

  // First we insert the entry because a delete isn't allowed on non-existing
  // table entries.
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));

  // Then we can update the PI write request to delete the entry, and setup the
  // Orchagent to fail with an invalid parameter.
  request.mutable_updates(0)->set_type(p4::v1::Update::DELETE);
  p4rt_service_.GetP4rtAppDbTable().SetResponseForKey(
      expected_key1, "SWSS_RC_INVALID_PARAM", "my error message");

  // We expect the invalid argument error to be propagated all the way back to
  // the gRPC response.
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kUnknown,
               HasSubstr("#1: INVALID_ARGUMENT: my error message")));

  // Sanity check that the entries still exists in the
  // REPLICATION_IP_MULTICAST_TABLE.
  ASSERT_OK(p4rt_service_.GetP4rtAppDbTable().ReadTableEntry(expected_key1))
      << "Unable to read entry for " << expected_key1;
}

TEST_F(PacketReplicationTableTest, ModifySuccess) {
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet0", "1"));
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet1", "2"));
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet2", "3"));
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::IrWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               entity {
                                 packet_replication_engine_entry {
                                   multicast_group_entry {
                                     multicast_group_id: 1
                                     replicas { port: "1" instance: 0 }
                                     replicas { port: "2" instance: 0 }
                                   }
                                 }
                               }
                             })pb",
                           ir_p4_info_));

  const auto expected_key1 = "REPLICATION_IP_MULTICAST_TABLE:0x0001";

  // First, insert an entry.
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));

  // Read back the entry which should result in the same packet replication
  // entry.
  p4::v1::ReadRequest read_request;
  read_request.add_entities()
      ->mutable_packet_replication_engine_entry()
      ->mutable_multicast_group_entry();
  ASSERT_OK_AND_ASSIGN(
      p4::v1::ReadResponse read_response,
      pdpi::SetMetadataAndSendPiReadRequest(p4rt_session_.get(), read_request));
  ASSERT_EQ(read_response.entities_size(), 1);  // Only one entity.
  EXPECT_THAT(read_response.entities(0),
              EqualsProto(request.updates(0).entity()));

  // Next, try to modify the entry.
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request2,
                       test_lib::IrWriteRequestToPi(
                           R"pb(
                             updates {
                               type: MODIFY
                               entity {
                                 packet_replication_engine_entry {
                                   multicast_group_entry {
                                     multicast_group_id: 1
                                     replicas { port: "1" instance: 0 }
                                     replicas { port: "2" instance: 0 }
                                     replicas { port: "3" instance: 1 }
                                   }
                                 }
                               }
                             })pb",
                           ir_p4_info_));
  EXPECT_TRUE(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request2)
          .ok());

  // Sanity check that the correct entries exist in the
  // REPLICATION_IP_MULTICAST_TABLE.
  ASSERT_OK(p4rt_service_.GetP4rtAppDbTable().ReadTableEntry(expected_key1))
      << "Unable to read entry for " << expected_key1;

  // Read back the modified entry which should result in the updated packet
  // replication entry.
  p4::v1::ReadRequest read_request2;
  read_request2.add_entities()
      ->mutable_packet_replication_engine_entry()
      ->mutable_multicast_group_entry();
  ASSERT_OK_AND_ASSIGN(p4::v1::ReadResponse read_response2,
                       pdpi::SetMetadataAndSendPiReadRequest(
                           p4rt_session_.get(), read_request2));
  ASSERT_EQ(read_response2.entities_size(), 1);  // Only one entity.
  EXPECT_THAT(read_response2.entities(0),
              EqualsProto(request2.updates(0).entity()));
}

TEST_F(PacketReplicationTableTest, PopulatedReadRequestFails) {
  // Read back the entry which should result in the same packet replication
  // entry.
  p4::v1::ReadRequest read_request;
  read_request.add_entities()
      ->mutable_packet_replication_engine_entry()
      ->mutable_multicast_group_entry()
      ->set_multicast_group_id(1);

  auto read_response =
      pdpi::SetMetadataAndSendPiReadRequest(p4rt_session_.get(), read_request);
  EXPECT_FALSE(read_response.ok());
  EXPECT_THAT(read_response, StatusIs(absl::StatusCode::kUnknown,
                                      HasSubstr("multicast_group_id: 1")));
}

TEST_F(PacketReplicationTableTest, CloneSessionReadIsEmpty) {
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet0", "1"));
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet1", "2"));
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::IrWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               entity {
                                 packet_replication_engine_entry {
                                   multicast_group_entry {
                                     multicast_group_id: 1
                                     replicas { port: "1" instance: 0 }
                                     replicas { port: "2" instance: 0 }
                                   }
                                 }
                               }
                             })pb",
                           ir_p4_info_));

  // First, insert a multicast group entry.
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));

  // Attempt to read back a clone_session_entry.  The response should be empty.
  p4::v1::ReadRequest read_request;
  read_request.add_entities()
      ->mutable_packet_replication_engine_entry()
      ->mutable_clone_session_entry();
  ASSERT_OK_AND_ASSIGN(
      p4::v1::ReadResponse read_response,
      pdpi::SetMetadataAndSendPiReadRequest(p4rt_session_.get(), read_request));
  EXPECT_THAT(read_response.entities(), IsEmpty());
}

TEST_F(PacketReplicationTableTest, PopulatedCloneSessionReadRequestsFail) {
  p4::v1::ReadRequest read_request_with_session_id;
  read_request_with_session_id.add_entities()
      ->mutable_packet_replication_engine_entry()
      ->mutable_clone_session_entry()
      ->set_session_id(1);

  EXPECT_THAT(pdpi::SetMetadataAndSendPiReadRequest(
                  p4rt_session_.get(), read_request_with_session_id),
              StatusIs(absl::StatusCode::kUnknown, HasSubstr("session_id: 1")));

  p4::v1::ReadRequest read_request_with_clone_replica;
  auto* clone_with_replica = read_request_with_clone_replica.add_entities()
                                 ->mutable_packet_replication_engine_entry()
                                 ->mutable_clone_session_entry();
  auto* replica = clone_with_replica->add_replicas();
  replica->set_instance(2);

  EXPECT_THAT(pdpi::SetMetadataAndSendPiReadRequest(
                  p4rt_session_.get(), read_request_with_clone_replica),
              Not(IsOk()));
}

TEST_F(PacketReplicationTableTest,
       UnsetPacketReplicationEntryTypeReturnsMulticastGroupEntry) {
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet0", "1"));
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet1", "2"));
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::IrWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               entity {
                                 packet_replication_engine_entry {
                                   multicast_group_entry {
                                     multicast_group_id: 1
                                     replicas { port: "1" instance: 0 }
                                     replicas { port: "2" instance: 0 }
                                   }
                                 }
                               }
                             })pb",
                           ir_p4_info_));

  // First, insert a multicast group entry.
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));

  // Read back a packet replication engine entry.  Expect the multicast group
  // entry to be returned.
  p4::v1::ReadRequest read_request;
  read_request.add_entities()->mutable_packet_replication_engine_entry();
  ASSERT_OK_AND_ASSIGN(
      p4::v1::ReadResponse read_response,
      pdpi::SetMetadataAndSendPiReadRequest(p4rt_session_.get(), read_request));
  ASSERT_EQ(read_response.entities_size(), 1);  // Only one entity.
  EXPECT_THAT(read_response.entities(0),
              EqualsProto(request.updates(0).entity()));
}

TEST_F(PacketReplicationTableTest, CannotTranslatePortFailure) {
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::IrWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               entity {
                                 packet_replication_engine_entry {
                                   multicast_group_entry {
                                     multicast_group_id: 1
                                     replicas { port: "1" instance: 0 }
                                   }
                                 }
                               }
                             })pb",
                           ir_p4_info_));
  // Expect port translation failure.
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kUnknown, HasSubstr("Cannot translate port")));
}

}  // namespace
}  // namespace p4rt_app
