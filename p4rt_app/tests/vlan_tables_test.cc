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
#include <memory>
#include <string>

#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"
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
using ::gutil::StatusIs;
using ::testing::HasSubstr;
using ::testing::UnorderedPointwise;

class VlanTablesTest : public test_lib::P4RuntimeComponentTestFixture {
 protected:
  VlanTablesTest()
      : test_lib::P4RuntimeComponentTestFixture(
            sai::Instantiation::kMiddleblock) {}
};

TEST_F(VlanTablesTest, InsertReadAndDeleteVlanEntry) {
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::IrWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               entity {
                                 table_entry {
                                   table_name: "vlan_table"
                                   matches {
                                     name: "vlan_id"
                                     exact { hex_str: "0x0ff" }
                                   }
                                   action { name: "no_action" }
                                 }
                               }
                             })pb",
                           ir_p4_info_));

  // Create the VLAN entry, and do a sanity check that it exists in the
  // VLAN_TABLE.
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));
  ASSERT_OK(p4rt_service_.GetVlanAppDbTable().ReadTableEntry("Vlan255"))
      << "VLAN ID was never created.";

  // Read back the VLAN entry which should result in the same table entry.
  p4::v1::ReadRequest read_request;
  read_request.add_entities()->mutable_table_entry();
  ASSERT_OK_AND_ASSIGN(
      p4::v1::ReadResponse read_response,
      pdpi::SetMetadataAndSendPiReadRequest(p4rt_session_.get(), read_request));
  ASSERT_EQ(read_response.entities_size(), 1);  // Only one write.
  EXPECT_THAT(read_response.entities(0),
              EqualsProto(request.updates(0).entity()));

  // Delete the VLAN entry, and do a sanity check that it is gone.
  request.mutable_updates(0)->set_type(p4::v1::Update::DELETE);
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));
  ASSERT_THAT(p4rt_service_.GetVlanAppDbTable().ReadTableEntry("Vlan255"),
              StatusIs(absl::StatusCode::kNotFound))
      << "VLAN ID was not deleted.";
}

TEST_F(VlanTablesTest, CannotModifyVlanEntries) {
  // First insert the entry for modify.
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::IrWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               entity {
                                 table_entry {
                                   table_name: "vlan_table"
                                   matches {
                                     name: "vlan_id"
                                     exact { hex_str: "0x002" }
                                   }
                                   action { name: "no_action" }
                                 }
                               }
                             })pb",
                           ir_p4_info_));
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));

  // Now send the modify request and expect to fail.
  request.mutable_updates(0)->set_type(p4::v1::Update::MODIFY);
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kUnknown, HasSubstr("#1: INVALID_ARGUMENT")));
}

TEST_F(VlanTablesTest, CannotInsertDuplicateVlanEntries) {
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::IrWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               entity {
                                 table_entry {
                                   table_name: "vlan_table"
                                   matches {
                                     name: "vlan_id"
                                     exact { hex_str: "0x007" }
                                   }
                                   action { name: "no_action" }
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

TEST_F(VlanTablesTest, VlanInsertRequestFails) {
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::IrWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               entity {
                                 table_entry {
                                   table_name: "vlan_table"
                                   matches {
                                     name: "vlan_id"
                                     exact { hex_str: "0x00f" }
                                   }
                                   action { name: "no_action" }
                                 }
                               }
                             })pb",
                           ir_p4_info_));

  // Assume the Orchagent fails with an invalid parameter.
  p4rt_service_.GetVlanAppDbTable().SetResponseForKey(
      "Vlan15", "SWSS_RC_INVALID_PARAM", "my error message");

  // We expect the invalid argument error to be propagated all the way back
  // to the gRPC response.
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kUnknown,
               HasSubstr("#1: INVALID_ARGUMENT: my error message")));

  // Sanity check that the entry is not accidentally left in the VLAN_TABLE.
  EXPECT_EQ(p4rt_service_.GetVlanAppDbTable().GetAllKeys().size(), 0);
  ASSERT_THAT(p4rt_service_.GetVlanAppDbTable().ReadTableEntry("Vlan15"),
              StatusIs(absl::StatusCode::kNotFound))
      << "VLAN ID was not cleaned up after failure.";
}

TEST_F(VlanTablesTest, CannotDeleteNonexistentVlanEntry) {
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::IrWriteRequestToPi(
                           R"pb(
                             updates {
                               type: DELETE
                               entity {
                                 table_entry {
                                   table_name: "vlan_table"
                                   matches {
                                     name: "vlan_id"
                                     exact { hex_str: "0x003" }
                                   }
                                   action { name: "no_action" }
                                 }
                               }
                             })pb",
                           ir_p4_info_));
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kUnknown, HasSubstr("#1: NOT_FOUND")));
}

TEST_F(VlanTablesTest, VlanEntryDeleteRequestFails) {
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::IrWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               entity {
                                 table_entry {
                                   table_name: "vlan_table"
                                   matches {
                                     name: "vlan_id"
                                     exact { hex_str: "0x004" }
                                   }
                                   action { name: "no_action" }
                                 }
                               }
                             })pb",
                           ir_p4_info_));

  // First we insert the entry because a delete isn't allowed on non-existing
  // table entries.
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));

  // Then we can update the PI write request to delete the entry, and setup
  // the Orchagent to fail with an invalid parameter.
  request.mutable_updates(0)->set_type(p4::v1::Update::DELETE);
  p4rt_service_.GetVlanAppDbTable().SetResponseForKey(
      "Vlan4", "SWSS_RC_INVALID_PARAM", "my error message");

  // We expect the invalid argument error to be propagated all the way back
  // to the gRPC response.
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kUnknown,
               HasSubstr("#1: INVALID_ARGUMENT: my error message")));

  // Sanity check that the entry still exists in the VLAN_TABLE.
  EXPECT_EQ(p4rt_service_.GetVlanAppDbTable().GetAllKeys().size(), 1);
  ASSERT_OK(p4rt_service_.GetVlanAppDbTable().ReadTableEntry("Vlan4"))
      << "VLAN ID was not re-inserted after failure.";
}

TEST_F(VlanTablesTest, InsertReadAndDeleteVlanMemberEntry) {
  ASSERT_OK(
      p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet1/1/1", "1"));
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::IrWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               entity {
                                 table_entry {
                                   table_name: "vlan_membership_table"
                                   matches {
                                     name: "vlan_id"
                                     exact { hex_str: "0x0ff" }
                                   }
                                   matches {
                                     name: "port"
                                     exact { str: "1" }
                                   }
                                   action { name: "make_untagged_member" }
                                 }
                               }
                             })pb",
                           ir_p4_info_));

  // Create the VLAN entry, and do a sanity check that it exists in the
  // VLAN_MEMBER_TABLE.
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));
  ASSERT_OK(p4rt_service_.GetVlanMemberAppDbTable().ReadTableEntry(
      "Vlan255:Ethernet1/1/1"))
      << "VLAN member was never created.";

  // Read back the VLAN member entry which should result in the same table
  // entry.
  p4::v1::ReadRequest read_request;
  read_request.add_entities()->mutable_table_entry();
  ASSERT_OK_AND_ASSIGN(
      p4::v1::ReadResponse read_response,
      pdpi::SetMetadataAndSendPiReadRequest(p4rt_session_.get(), read_request));
  ASSERT_EQ(read_response.entities_size(), 1);  // Only one write.
  EXPECT_THAT(read_response.entities(0),
              EqualsProto(request.updates(0).entity()));

  // Delete the VLAN member entry, and do a sanity check that it is gone.
  request.mutable_updates(0)->set_type(p4::v1::Update::DELETE);
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));
  ASSERT_THAT(
      p4rt_service_.GetVlanAppDbTable().ReadTableEntry("Vlan255:Ethernet1/1/1"),
      StatusIs(absl::StatusCode::kNotFound))
      << "VLAN member was not deleted.";
}

TEST_F(VlanTablesTest, CannotTranslatePortInVlanMemberTableGivesFailure) {
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::IrWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               entity {
                                 table_entry {
                                   table_name: "vlan_membership_table"
                                   matches {
                                     name: "vlan_id"
                                     exact { hex_str: "0x0ff" }
                                   }
                                   matches {
                                     name: "port"
                                     exact { str: "1" }
                                   }
                                   action { name: "make_untagged_member" }
                                 }
                               }
                             })pb",
                           ir_p4_info_));
  // Expect port translation failure.
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kUnknown, HasSubstr("Cannot translate port")));
}

TEST_F(VlanTablesTest, ModifyVlanMemberEntries) {
  ASSERT_OK(
      p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet1/1/1", "1"));
  // First insert the entry for modify.
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::IrWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               entity {
                                 table_entry {
                                   table_name: "vlan_membership_table"
                                   matches {
                                     name: "vlan_id"
                                     exact { hex_str: "0x0ff" }
                                   }
                                   matches {
                                     name: "port"
                                     exact { str: "1" }
                                   }
                                   action { name: "make_untagged_member" }
                                 }
                               }
                             })pb",
                           ir_p4_info_));
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));

  // Read back the entry which should result in the same VLAN member entry.
  p4::v1::ReadRequest read_request;
  read_request.add_entities()->mutable_table_entry();
  ASSERT_OK_AND_ASSIGN(
      p4::v1::ReadResponse read_response,
      pdpi::SetMetadataAndSendPiReadRequest(p4rt_session_.get(), read_request));
  ASSERT_EQ(read_response.entities_size(), 1);  // Only one write.
  EXPECT_THAT(read_response.entities(0),
              EqualsProto(request.updates(0).entity()));

  // Next, try to modify the entry.
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request2,
                       test_lib::IrWriteRequestToPi(
                           R"pb(
                             updates {
                               type: MODIFY
                               entity {
                                 table_entry {
                                   table_name: "vlan_membership_table"
                                   matches {
                                     name: "vlan_id"
                                     exact { hex_str: "0x0ff" }
                                   }
                                   matches {
                                     name: "port"
                                     exact { str: "1" }
                                   }
                                   action { name: "make_untagged_member" }
                                 }
                               }
                             })pb",
                           ir_p4_info_));
  EXPECT_TRUE(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request2)
          .ok());

  // Read back the entry which should result in the same VLAN member entry.
  p4::v1::ReadRequest read_request2;
  read_request2.add_entities()->mutable_table_entry();
  ASSERT_OK_AND_ASSIGN(p4::v1::ReadResponse read_response2,
                       pdpi::SetMetadataAndSendPiReadRequest(
                           p4rt_session_.get(), read_request2));
  ASSERT_EQ(read_response2.entities_size(), 1);  // Only one write.
  EXPECT_THAT(read_response2.entities(0),
              EqualsProto(request2.updates(0).entity()));
}

TEST_F(VlanTablesTest, CannotInsertDuplicateVlanMemberEntries) {
  ASSERT_OK(
      p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet1/1/1", "1"));
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::IrWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               entity {
                                 table_entry {
                                   table_name: "vlan_membership_table"
                                   matches {
                                     name: "vlan_id"
                                     exact { hex_str: "0x007" }
                                   }
                                   matches {
                                     name: "port"
                                     exact { str: "1" }
                                   }
                                   action { name: "make_tagged_member" }
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

TEST_F(VlanTablesTest, VlanMemberInsertRequestFails) {
  ASSERT_OK(
      p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet1/1/1", "1"));
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::IrWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               entity {
                                 table_entry {
                                   table_name: "vlan_membership_table"
                                   matches {
                                     name: "vlan_id"
                                     exact { hex_str: "0x00f" }
                                   }
                                   matches {
                                     name: "port"
                                     exact { str: "1" }
                                   }
                                   action { name: "make_untagged_member" }
                                 }
                               }
                             })pb",
                           ir_p4_info_));

  // Assume the Orchagent fails with an invalid parameter.
  p4rt_service_.GetVlanMemberAppDbTable().SetResponseForKey(
      "Vlan15:Ethernet1/1/1", "SWSS_RC_INVALID_PARAM", "my error message");

  // We expect the invalid argument error to be propagated all the way back
  // to the gRPC response.
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kUnknown,
               HasSubstr("#1: INVALID_ARGUMENT: my error message")));

  // Sanity check that the entry is not accidentally left in the
  // VLAN_MEMBER_TABLE.
  EXPECT_EQ(p4rt_service_.GetVlanMemberAppDbTable().GetAllKeys().size(), 0);
  ASSERT_THAT(p4rt_service_.GetVlanMemberAppDbTable().ReadTableEntry(
                  "Vlan15:Ethernet1/1/1"),
              StatusIs(absl::StatusCode::kNotFound))
      << "VLAN member was not cleaned up after failure.";
}

TEST_F(VlanTablesTest, CannotDeleteNonexistentVlanMemberEntry) {
  ASSERT_OK(
      p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet1/1/1", "1"));
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::IrWriteRequestToPi(
                           R"pb(
                             updates {
                               type: DELETE
                               entity {
                                 table_entry {
                                   table_name: "vlan_membership_table"
                                   matches {
                                     name: "vlan_id"
                                     exact { hex_str: "0x003" }
                                   }
                                   matches {
                                     name: "port"
                                     exact { str: "1" }
                                   }
                                   action { name: "make_tagged_member" }
                                 }
                               }
                             })pb",
                           ir_p4_info_));
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kUnknown, HasSubstr("#1: NOT_FOUND")));
}

TEST_F(VlanTablesTest, VlanMemberEntryDeleteRequestFails) {
  ASSERT_OK(
      p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet1/1/1", "1"));
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::IrWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               entity {
                                 table_entry {
                                   table_name: "vlan_membership_table"
                                   matches {
                                     name: "vlan_id"
                                     exact { hex_str: "0x004" }
                                   }
                                   matches {
                                     name: "port"
                                     exact { str: "1" }
                                   }
                                   action { name: "make_untagged_member" }
                                 }
                               }
                             })pb",
                           ir_p4_info_));

  // First we insert the entry because a delete isn't allowed on non-existing
  // table entries.
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));

  // Then we can update the PI write request to delete the entry, and setup
  // the Orchagent to fail with an invalid parameter.
  p4rt_service_.GetVlanMemberAppDbTable().SetResponseForKey(
      "Vlan4:Ethernet1/1/1", "SWSS_RC_INVALID_PARAM", "my error message");

  // We expect the invalid argument error to be propagated all the way back
  // to the gRPC response.
  request.mutable_updates(0)->set_type(p4::v1::Update::DELETE);
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kUnknown,
               HasSubstr("#1: INVALID_ARGUMENT: my error message")));

  // Sanity check that the entry still exists in the VLAN_TABLE.
  EXPECT_EQ(p4rt_service_.GetVlanMemberAppDbTable().GetAllKeys().size(), 1);
  ASSERT_OK(p4rt_service_.GetVlanMemberAppDbTable().ReadTableEntry(
      "Vlan4:Ethernet1/1/1"))
      << "VLAN member was not re-inserted after failure.";
}

TEST_F(VlanTablesTest, VlanEntryWithMulticastRitfEntry) {
  ASSERT_OK(
      p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet1/1/1", "1"));
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest request,
      test_lib::IrWriteRequestToPi(
          R"pb(
            updates {
              type: INSERT
              entity {
                table_entry {
                  table_name: "vlan_table"
                  matches {
                    name: "vlan_id"
                    exact { hex_str: "0x0ff" }
                  }
                  action { name: "no_action" }
                }
              }
            }
            updates {
              type: INSERT
              entity {
                table_entry {
                  table_name: "vlan_membership_table"
                  matches {
                    name: "vlan_id"
                    exact { hex_str: "0x0ff" }
                  }
                  matches {
                    name: "port"
                    exact { str: "1" }
                  }
                  action { name: "make_untagged_member" }
                }
              }
            }
            updates {
              type: INSERT
              entity {
                table_entry {
                  table_name: "multicast_router_interface_table"
                  matches {
                    name: "multicast_replica_port"
                    exact { str: "1" }
                  }
                  matches {
                    name: "multicast_replica_instance"
                    exact { hex_str: "0x0001" }
                  }
                  action {
                    name: "multicast_set_src_mac_and_vlan_id"
                    params {
                      name: "src_mac"
                      value { mac: "02:2a:10:00:00:02" }
                    }
                    params {
                      name: "vlan_id"
                      value { hex_str: "0x0ff" }
                    }
                  }
                }
              }
            })pb",
          ir_p4_info_));

  // Do a sanity check that the entries exist in the table.
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));
  ASSERT_OK(p4rt_service_.GetVlanAppDbTable().ReadTableEntry("Vlan255"))
      << "VLAN ID was never created.";
  ASSERT_OK(p4rt_service_.GetVlanMemberAppDbTable().ReadTableEntry(
      "Vlan255:Ethernet1/1/1"))
      << "VLAN member was never created.";
  ASSERT_OK(p4rt_service_.GetP4rtAppDbTable().ReadTableEntry(
      "FIXED_MULTICAST_ROUTER_INTERFACE_TABLE:{\"match/"
      "multicast_replica_instance\":\"0x0001\",\"match/"
      "multicast_replica_port\":\"Ethernet1/1/1\"}"))
      << "Multicast router interface was never created.";

  // Read back the entries which should result in the same table entries.
  p4::v1::ReadRequest read_request;
  read_request.add_entities()->mutable_table_entry();
  ASSERT_OK_AND_ASSIGN(
      p4::v1::ReadResponse read_response,
      pdpi::SetMetadataAndSendPiReadRequest(p4rt_session_.get(), read_request));
  ASSERT_EQ(read_response.entities_size(), 3);
  EXPECT_THAT(read_response.entities(),
              UnorderedPointwise(EqualsProto(), {request.updates(0).entity(),
                                                 request.updates(1).entity(),
                                                 request.updates(2).entity()}));

  // Delete entries, and do a sanity check that they are gone.
  request.mutable_updates(0)->set_type(p4::v1::Update::DELETE);
  request.mutable_updates(1)->set_type(p4::v1::Update::DELETE);
  request.mutable_updates(2)->set_type(p4::v1::Update::DELETE);
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));
  ASSERT_THAT(p4rt_service_.GetVlanAppDbTable().ReadTableEntry("Vlan255"),
              StatusIs(absl::StatusCode::kNotFound))
      << "VLAN ID was not deleted.";
  ASSERT_THAT(
      p4rt_service_.GetVlanAppDbTable().ReadTableEntry("Vlan255:Ethernet1/1/1"),
      StatusIs(absl::StatusCode::kNotFound))
      << "VLAN member was not deleted.";
  ASSERT_THAT(p4rt_service_.GetVlanAppDbTable().ReadTableEntry(
                  "FIXED_MULTICAST_ROUTER_INTERFACE_TABLE:{\"match/"
                  "multicast_replica_instance\":\"0x0001\",\"match/"
                  "multicast_replica_port\":\"Ethernet1/1/1\"}"),
              StatusIs(absl::StatusCode::kNotFound))
      << "Multicast router interface was not deleted.";
}

}  // namespace
}  // namespace p4rt_app
