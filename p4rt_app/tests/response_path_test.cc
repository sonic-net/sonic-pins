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
#include <memory>
#include <ostream>
#include <string>
#include <type_traits>
#include <unordered_map>
#include <utility>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/sonic/adapters/fake_sonic_db_table.h"
#include "p4rt_app/tests/lib/app_db_entry_builder.h"
#include "p4rt_app/tests/lib/p4runtime_component_test_fixture.h"
#include "p4rt_app/tests/lib/p4runtime_grpc_service.h"
#include "p4rt_app/tests/lib/p4runtime_request_helpers.h"
#include "sai_p4/instantiations/google/instantiations.h"

namespace p4rt_app {

// Helper method to improve gTest matcher outputs. Try to keep the fields order
// matching the struct.
void PrintTo(const FlowProgrammingStatistics& stats, std::ostream* os) {
  *os << "write_batch_count:" << stats.write_batch_count
      << ", write_requests_count:" << stats.write_requests_count
      << ", write_time:" << stats.write_time
      << ", read_request_count:" << stats.read_request_count
      << ", read_time:" << stats.read_time;
}

namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOk;
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::_;
using ::testing::AllOf;
using ::testing::FieldsAre;
using ::testing::HasSubstr;
using ::testing::Not;
using ::testing::UnorderedElementsAre;
using ::testing::UnorderedElementsAreArray;

// Testing end-to-end features around the response path (e.g.
// insert/modify/delete, pass/fail, etc.)
class ResponsePathTest : public test_lib::P4RuntimeComponentTestFixture {
 protected:
  ResponsePathTest()
      : test_lib::P4RuntimeComponentTestFixture(
            sai::Instantiation::kMiddleblock) {}
};

TEST_F(ResponsePathTest, TableEntryInsertReadAndRemove) {
  // P4 write request.
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest write_request,
      test_lib::PdWriteRequestToPi(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                ipv6_table_entry {
                  match {
                    vrf_id: "80"
                    ipv6_dst { value: "2002:a17:506:c114::" prefix_length: 64 }
                  }
                  action { set_nexthop_id { nexthop_id: "20" } }
                }
              }
            }
          )pb",
          ir_p4_info_));

  // Expected P4RT AppDb entry.
  auto expected_entry = test_lib::AppDbEntryBuilder{}
                            .SetTableName("FIXED_IPV6_TABLE")
                            .AddMatchField("ipv6_dst", "2002:a17:506:c114::/64")
                            .AddMatchField("vrf_id", "80")
                            .SetAction("set_nexthop_id")
                            .AddActionParam("nexthop_id", "20");

  // The insert write request should not fail, and once complete the entry
  // should exist in the P4RT AppDb table.
  ASSERT_OK(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   write_request));
  EXPECT_THAT(
      p4rt_service_.GetP4rtAppDbTable().ReadTableEntry(expected_entry.GetKey()),
      IsOkAndHolds(UnorderedElementsAreArray(expected_entry.GetValueMap())));

  // Reading back the entry should result in the same table_entry.
  p4::v1::ReadRequest read_request;
  read_request.add_entities()->mutable_table_entry();
  ASSERT_OK_AND_ASSIGN(
      p4::v1::ReadResponse read_response,
      pdpi::SetMetadataAndSendPiReadRequest(p4rt_session_.get(), read_request));
  ASSERT_EQ(read_response.entities_size(), 1);  // Only one write.
  EXPECT_THAT(read_response.entities(0),
              EqualsProto(write_request.updates(0).entity()));

  // Modify the P4 write request to delete the entry. We should be able to
  // delete the entry with only the match key.
  write_request.mutable_updates(0)->set_type(p4::v1::Update::DELETE);
  write_request.mutable_updates(0)
      ->mutable_entity()
      ->mutable_table_entry()
      ->mutable_action()
      ->Clear();

  // The delete write request should not fail, and once complete the entry
  // should no longer exist in the P4RT AppDb table.
  ASSERT_OK(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   write_request));
  EXPECT_THAT(
      p4rt_service_.GetP4rtAppDbTable().ReadTableEntry(expected_entry.GetKey()),
      StatusIs(absl::StatusCode::kNotFound));

  // Reading back the entry should result in nothing being returned.
  ASSERT_OK_AND_ASSIGN(read_response, pdpi::SetMetadataAndSendPiReadRequest(
                                          p4rt_session_.get(), read_request));
  EXPECT_EQ(read_response.entities_size(), 0);
}

TEST_F(ResponsePathTest, TableEntryModify) {
  // P4 write request.
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest write_request,
      test_lib::PdWriteRequestToPi(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                ipv6_table_entry {
                  match {
                    vrf_id: "80"
                    ipv6_dst { value: "2002:a17:506:c114::" prefix_length: 64 }
                  }
                  action { set_nexthop_id { nexthop_id: "20" } }
                }
              }
            }
          )pb",
          ir_p4_info_));

  // Expected P4RT AppDb entry.
  auto expected_entry = test_lib::AppDbEntryBuilder{}
                            .SetTableName("FIXED_IPV6_TABLE")
                            .AddMatchField("ipv6_dst", "2002:a17:506:c114::/64")
                            .AddMatchField("vrf_id", "80");

  // The insert write request should not fail, and once complete the entry
  // should exist in the P4RT AppDb table.
  ASSERT_OK(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   write_request));
  ASSERT_THAT(
      p4rt_service_.GetP4rtAppDbTable().ReadTableEntry(expected_entry.GetKey()),
      IsOkAndHolds(
          UnorderedElementsAre(std::make_pair("action", "set_nexthop_id"),
                               std::make_pair("param/nexthop_id", "20"))));

  // Update the request with a new action.
  write_request.mutable_updates(0)->set_type(p4::v1::Update::MODIFY);
  ASSERT_OK(gutil::ReadProtoFromString(
      R"pb(action {
             action_id: 16777220
             params { param_id: 1 value: "30" }
           })pb",
      write_request.mutable_updates(0)
          ->mutable_entity()
          ->mutable_table_entry()
          ->mutable_action()));
  ASSERT_OK(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   write_request));
  EXPECT_THAT(
      p4rt_service_.GetP4rtAppDbTable().ReadTableEntry(expected_entry.GetKey()),
      IsOkAndHolds(
          UnorderedElementsAre(std::make_pair("action", "set_wcmp_group_id"),
                               std::make_pair("param/wcmp_group_id", "30"))));
}

TEST_F(ResponsePathTest, DuplicateTableEntryInsertFails) {
  // P4 write request.
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest write_request,
      test_lib::PdWriteRequestToPi(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                ipv6_table_entry {
                  match {
                    vrf_id: "80"
                    ipv6_dst { value: "2002:a17:506:c114::" prefix_length: 64 }
                  }
                  action { set_nexthop_id { nexthop_id: "20" } }
                }
              }
            }
          )pb",
          ir_p4_info_));

  // The first insert is expected to pass since the entry does not exist.
  EXPECT_OK(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   write_request));

  // The second insert is expected to fail since the entry already exists.
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                             write_request),
      StatusIs(absl::StatusCode::kUnknown, HasSubstr("ALREADY_EXISTS")));

  // Reading back we should only see one result.
  p4::v1::ReadRequest read_request;
  read_request.add_entities()->mutable_table_entry();
  ASSERT_OK_AND_ASSIGN(
      p4::v1::ReadResponse read_response,
      pdpi::SetMetadataAndSendPiReadRequest(p4rt_session_.get(), read_request));
  ASSERT_EQ(read_response.entities_size(), 1);
  EXPECT_THAT(read_response.entities(0),
              EqualsProto(write_request.updates(0).entity()));
}

TEST_F(ResponsePathTest, DuplicatePacketReplicationEngineEntryInsertFails) {
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet0", "1"));
  // P4 write request.
  p4::v1::WriteRequest write_request;
  ASSERT_OK(gutil::ReadProtoFromString(
      R"pb(updates {
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
      &write_request));

  // The first insert is expected to pass since the entry does not exist.
  EXPECT_OK(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   write_request));

  // The second insert is expected to fail since the entry already exists.
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                             write_request),
      StatusIs(absl::StatusCode::kUnknown, HasSubstr("ALREADY_EXISTS")));

  // Reading back we should only see one result.
  p4::v1::ReadRequest read_request;
  read_request.add_entities()
      ->mutable_packet_replication_engine_entry()
      ->mutable_multicast_group_entry();
  ASSERT_OK_AND_ASSIGN(
      p4::v1::ReadResponse read_response,
      pdpi::SetMetadataAndSendPiReadRequest(p4rt_session_.get(), read_request));
  ASSERT_EQ(read_response.entities_size(), 1);
  EXPECT_THAT(read_response.entities(0),
              EqualsProto(write_request.updates(0).entity()));
}

TEST_F(ResponsePathTest, TableEntryModifyFailsIfEntryDoesNotExist) {
  // P4 write request.
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest write_request,
      test_lib::PdWriteRequestToPi(
          R"pb(
            updates {
              type: MODIFY
              table_entry {
                ipv6_table_entry {
                  match {
                    vrf_id: "80"
                    ipv6_dst { value: "2002:a17:506:c114::" prefix_length: 64 }
                  }
                  action { set_nexthop_id { nexthop_id: "20" } }
                }
              }
            }
          )pb",
          ir_p4_info_));
  EXPECT_THAT(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                     write_request),
              StatusIs(absl::StatusCode::kUnknown, HasSubstr("NOT_FOUND")));
}

TEST_F(ResponsePathTest, TableEntryDeleteFailsIfEntryDoesNotExist) {
  // P4 write request.
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest write_request,
      test_lib::PdWriteRequestToPi(
          R"pb(
            updates {
              type: DELETE
              table_entry {
                ipv6_table_entry {
                  match {
                    vrf_id: "80"
                    ipv6_dst { value: "2002:a17:506:c114::" prefix_length: 64 }
                  }
                  action { set_nexthop_id { nexthop_id: "20" } }
                }
              }
            }
          )pb",
          ir_p4_info_));
  EXPECT_THAT(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                     write_request),
              StatusIs(absl::StatusCode::kUnknown, HasSubstr("NOT_FOUND")));
}

TEST_F(ResponsePathTest, InsertRequestFails) {
  p4::v1::WriteRequest request;
  ASSERT_OK(gutil::ReadProtoFromString(
      R"pb(updates {
             type: INSERT
             entity {
               table_entry {
                 table_id: 33554496
                 match {
                   field_id: 1
                   exact { value: "1" }
                 }
                 match {
                   field_id: 2
                   exact {
                     value: "\376\200\000\000\000\000\000\000\002\032\021\377\376\027\000\200"
                   }
                 }
                 action {
                   action {
                     action_id: 16777217
                     params { param_id: 1 value: "\000\032\021\027_\200" }
                   }
                 }
               }
             }
           })pb",
      &request));

  auto neighbor_entry =
      test_lib::AppDbEntryBuilder{}
          .SetTableName("FIXED_NEIGHBOR_TABLE")
          .AddMatchField("neighbor_id", "fe80::21a:11ff:fe17:80")
          .AddMatchField("router_interface_id", "1");

  // Assume the Orchagent fails with an invalid parameter.
  p4rt_service_.GetP4rtAppDbTable().SetResponseForKey(
      neighbor_entry.GetKey(), "SWSS_RC_INVALID_PARAM", "my error message");

  // We expect the invalid argument error to be propagated all the way back to
  // the gRPC response.
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kUnknown,
               HasSubstr("#1: INVALID_ARGUMENT: my error message")));

  // We expect to read back no entries because the request failed.
  p4::v1::ReadRequest read_request;
  read_request.add_entities()->mutable_table_entry();
  ASSERT_OK_AND_ASSIGN(
      p4::v1::ReadResponse read_response,
      pdpi::SetMetadataAndSendPiReadRequest(p4rt_session_.get(), read_request));
  ASSERT_EQ(read_response.entities_size(), 0);
}

TEST_F(ResponsePathTest, ErrorResponseHandlesNonPrintableCharacters) {
  // The P4RT spec's error message are encoded as a string. However, not all
  // P4RT objects are not required to be string (e.g. they can be arbitrary
  // bytes). This can cause issues if a non UTF-8 object fails, and we report
  // that value back as an error message. P4RT app should escape any bytes.

  // UTF-8 characters fall in the range of 0x00 to 0x7F, and non UTF-8
  // characters fall in the range of 0x80 to 0x8F.
  std::vector<char> non_utf8_error;
  for (int i = 0x00; i < 0x8F; ++i) non_utf8_error.emplace_back(i);

  p4::v1::WriteRequest request;
  ASSERT_OK(gutil::ReadProtoFromString(
      R"pb(updates {
             type: INSERT
             entity {
               table_entry {
                 table_id: 33554496
                 match {
                   field_id: 1
                   exact { value: "1" }
                 }
                 match {
                   field_id: 2
                   exact { value: "fe80::021a:11ff:fe17:5f80" }
                 }
                 action {
                   action {
                     action_id: 16777217
                     params { param_id: 1 value: "\000\032\021\027_\200" }
                   }
                 }
               }
             }
           })pb",
      &request));

  auto neighbor_entry =
      test_lib::AppDbEntryBuilder{}
          .SetTableName("FIXED_NEIGHBOR_TABLE")
          .AddMatchField("neighbor_id", "fe80::021a:11ff:fe17:5f80")
          .AddMatchField("router_interface_id", "1");

  // The Orchagent fails with an invalid parameter, and a message with non UTF-8
  // characters in it.
  p4rt_service_.GetP4rtAppDbTable().SetResponseForKey(
      neighbor_entry.GetKey(), "SWSS_RC_INVALID_PARAM",
      std::string(non_utf8_error.begin(), non_utf8_error.end()));

  // We expect the error message to be converted to some printable string. Today
  // it's done with absl::CHexEscape so we verify some of those characters exist
  // in the response.
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kUnknown, HasSubstr("\0x80\0x81\0x82")));
}

TEST_F(ResponsePathTest, ModifyRequestFails) {
  // Insert a request into the AppDb.
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest insert_request,
                       test_lib::PdWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               table_entry {
                                 acl_ingress_table_entry {
                                   match { is_ip { value: "0x1" } }
                                   priority: 10
                                   action { acl_forward {} }
                                 }
                               }
                             }
                           )pb",
                           ir_p4_info_));
  EXPECT_OK(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   insert_request));

  // Verify that the expected entry exists.
  auto expected_entry = test_lib::AppDbEntryBuilder{}
                            .SetTableName("ACL_ACL_INGRESS_TABLE")
                            .SetPriority(10)
                            .AddMatchField("is_ip", "0x1");
  ASSERT_OK_AND_ASSIGN(sonic::SonicDbEntryMap actual_entry,
                       p4rt_service_.GetP4rtAppDbTable().ReadTableEntry(
                           expected_entry.GetKey()));

  // Update the Fake AppDb table so the next request for this key fails.
  p4rt_service_.GetP4rtAppDbTable().SetResponseForKey(
      expected_entry.GetKey(), "SWSS_RC_INVALID_PARAM", "my error message");

  // Try to modify the existing request, and fail as intended..
  ASSERT_OK_AND_ASSIGN(p4 ::v1::WriteRequest modify_request,
                       test_lib::PdWriteRequestToPi(
                           R"pb(
                             updates {
                               type: MODIFY
                               table_entry {
                                 acl_ingress_table_entry {
                                   match { is_ip { value: "0x1" } }
                                   priority: 10
                                   action { acl_copy { qos_queue: "0x3" } }
                                 }
                               }
                             }
                           )pb",
                           ir_p4_info_));

  EXPECT_THAT(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                     modify_request),
              StatusIs(absl::StatusCode::kUnknown));

  // Verify that the original entry was not modified.
  EXPECT_THAT(
      p4rt_service_.GetP4rtAppDbTable().ReadTableEntry(expected_entry.GetKey()),
      gutil::IsOkAndHolds(testing::UnorderedElementsAreArray(actual_entry)));

  // Verify that we can still read back the original insert.
  p4::v1::ReadRequest read_request;
  read_request.add_entities()->mutable_table_entry();
  ASSERT_OK_AND_ASSIGN(
      p4::v1::ReadResponse read_response,
      pdpi::SetMetadataAndSendPiReadRequest(p4rt_session_.get(), read_request));
  ASSERT_EQ(read_response.entities_size(), 1);
  EXPECT_THAT(read_response.entities(0),
              EqualsProto(insert_request.updates(0).entity()));
}

TEST_F(ResponsePathTest, DeleteRequestFails) {
  // Insert a request into the AppDb.
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest insert_request,
                       test_lib::PdWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               table_entry {
                                 acl_ingress_table_entry {
                                   match { is_ip { value: "0x1" } }
                                   priority: 10
                                   action { acl_copy { qos_queue: "0x1" } }
                                 }
                               }
                             }
                           )pb",
                           ir_p4_info_));
  EXPECT_OK(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   insert_request));

  // Verify that the expected entry exists.
  auto expected_entry = test_lib::AppDbEntryBuilder{}
                            .SetTableName("ACL_ACL_INGRESS_TABLE")
                            .SetPriority(10)
                            .AddMatchField("is_ip", "0x1");

  ASSERT_OK_AND_ASSIGN(sonic::SonicDbEntryMap actual_entry,
                       p4rt_service_.GetP4rtAppDbTable().ReadTableEntry(
                           expected_entry.GetKey()));

  // Update the Fake AppDb table so the next request for this key fails.
  p4rt_service_.GetP4rtAppDbTable().SetResponseForKey(
      expected_entry.GetKey(), "SWSS_RC_INVALID_PARAM", "my error message");

  // Try to delete the existing request, and fail as intended..
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest delete_request,
                       test_lib::PdWriteRequestToPi(
                           R"pb(
                             updates {
                               type: DELETE
                               table_entry {
                                 acl_ingress_table_entry {
                                   match { is_ip { value: "0x1" } }
                                   priority: 10
                                   action { acl_copy { qos_queue: "0x1" } }
                                 }
                               }
                             }
                           )pb",
                           ir_p4_info_));

  EXPECT_THAT(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                     delete_request),
              StatusIs(absl::StatusCode::kUnknown));

  // Verify that the original entry was not modified.
  EXPECT_THAT(
      p4rt_service_.GetP4rtAppDbTable().ReadTableEntry(expected_entry.GetKey()),
      gutil::IsOkAndHolds(testing::UnorderedElementsAreArray(actual_entry)));

  // Verify that we can still read back the original insert.
  p4::v1::ReadRequest read_request;
  read_request.add_entities()->mutable_table_entry();
  ASSERT_OK_AND_ASSIGN(
      p4::v1::ReadResponse read_response,
      pdpi::SetMetadataAndSendPiReadRequest(p4rt_session_.get(), read_request));
  ASSERT_EQ(read_response.entities_size(), 1);
  EXPECT_THAT(read_response.entities(0),
              EqualsProto(insert_request.updates(0).entity()));
}

TEST_F(ResponsePathTest, OneOfManyInsertRequestFails) {
  p4::v1::WriteRequest request;
  ASSERT_OK(gutil::ReadProtoFromString(
      R"pb(updates {
             type: INSERT
             entity {
               table_entry {
                 table_id: 33554496
                 match {
                   field_id: 1
                   exact { value: "1" }
                 }
                 match {
                   field_id: 2
                   exact { value: "1" }
                 }
                 action {
                   action {
                     action_id: 16777217
                     params { param_id: 1 value: "\000\032\021\027_\200" }
                   }
                 }
               }
             }
           }
           updates {
             type: INSERT
             entity {
               table_entry {
                 table_id: 33554498
                 match {
                   field_id: 1
                   exact { value: "8" }
                 }
                 action {
                   action {
                     action_id: 16777236
                     params { param_id: 1 value: "8" }
                     params { param_id: 2 value: "1" }
                   }
                 }
               }
             }
           })pb",
      &request));

  auto nexthop_entry = test_lib::AppDbEntryBuilder{}
                           .SetTableName("FIXED_NEXTHOP_TABLE")
                           .AddMatchField("nexthop_id", "8");

  // Assume the Orchagent fails for one request with an invalid parameter.
  p4rt_service_.GetP4rtAppDbTable().SetResponseForKey(
      nexthop_entry.GetKey(), "SWSS_RC_INVALID_PARAM", "my error message");

  // When one of the requests fails, but the other succeeds we expect the
  // response to tell us the status both separately.
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kUnknown,
               AllOf(HasSubstr("#1: OK"),
                     HasSubstr("#2: INVALID_ARGUMENT: my error message"))));
}

TEST_F(ResponsePathTest, RequestWithDuplicateKeysFails) {
  p4::v1::WriteRequest request;
  ASSERT_OK(gutil::ReadProtoFromString(
      R"pb(updates {
             type: INSERT
             entity {
               table_entry {
                 table_id: 33554496
                 match {
                   field_id: 1
                   exact { value: "1" }
                 }
                 match {
                   field_id: 2
                   exact { value: "1" }
                 }
                 action {
                   action {
                     action_id: 16777217
                     params { param_id: 1 value: "\000\032\021\027_\200" }
                   }
                 }
               }
             }
           }
           updates {
             type: MODIFY
             entity {
               table_entry {
                 table_id: 33554496
                 match {
                   field_id: 1
                   exact { value: "1" }
                 }
                 match {
                   field_id: 2
                   exact { value: "1" }
                 }
                 action {
                   action {
                     action_id: 16777217
                     params { param_id: 1 value: "\000\032\021\027_\200" }
                   }
                 }
               }
             }
           })pb",
      &request));

  // We expect the invalid argument error to be propagated all the way back to
  // the gRPC response.
  // With the fail on first error behavior, P4RT App will detect the duplicate
  // in the first entry and mark that as the INVALID_ARGUMENT error but the
  // subsequent one is marked as ABORTED (not attempted).
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kUnknown,
               AllOf(HasSubstr("#1: INVALID_ARGUMENT:"),
                     HasSubstr("#2: ABORTED:"))));
}

TEST_F(ResponsePathTest, P4rtTableFailOnFirstErrorAffectsVrfTable) {
  // Although VRF table entries are written into VRF_TABLE and other P4 table
  // entries are written into the P4RT table, fail-on-first should still apply.
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest write_request,
      test_lib::PdWriteRequestToPi(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                vrf_table_entry {
                  match { vrf_id: "vrf-1" }
                  action { no_action {} }
                }
              }
            }
            updates {
              type: INSERT
              table_entry {
                ipv6_table_entry {
                  match {
                    vrf_id: "vrf-2"
                    ipv6_dst { value: "2002:a17:506:c114::" prefix_length: 64 }
                  }
                  action { set_nexthop_id { nexthop_id: "20" } }
                }
              }
            }
            updates {
              type: INSERT
              table_entry {
                vrf_table_entry {
                  match { vrf_id: "vrf-3" }
                  action { no_action {} }
                }
              }
            }
            updates {
              type: INSERT
              table_entry {
                vrf_table_entry {
                  match { vrf_id: "vrf-4" }
                  action { no_action {} }
                }
              }
            }
          )pb",
          ir_p4_info_));

  // Fake valid error (INVALID_ARG) for the middle entry.
  auto failed_ipv6_entry =
      test_lib::AppDbEntryBuilder{}
          .SetTableName("FIXED_IPV6_TABLE")
          .AddMatchField("ipv6_dst", "2002:a17:506:c114::/64")
          .AddMatchField("vrf_id", "vrf-2");
  p4rt_service_.GetP4rtAppDbTable().SetResponseForKey(
      failed_ipv6_entry.GetKey(), "SWSS_RC_INVALID_PARAM", "error with vrf-2");

  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                             write_request),
      StatusIs(absl::StatusCode::kUnknown,
               AllOf(HasSubstr("#1: OK"),
                     HasSubstr("#2: INVALID_ARGUMENT: error with vrf-2"),
                     HasSubstr("#3: ABORTED: Not attempted"),
                     HasSubstr("#4: ABORTED: Not attempted"))));
}

TEST_F(ResponsePathTest, FailOnFirstErrorInVrfTable) {
  // VRF entry failure will cause the subsequent entries not to be updated
  // to App Db and hence the status returned as ABORTED for those entries.
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest write_request,
      test_lib::PdWriteRequestToPi(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                vrf_table_entry {
                  match { vrf_id: "vrf-1" }
                  action { no_action {} }
                }
              }
            }
            updates {
              type: INSERT
              table_entry {
                ipv6_table_entry {
                  match {
                    vrf_id: "vrf-2"
                    ipv6_dst { value: "2002:a17:506:c114::" prefix_length: 64 }
                  }
                  action { set_nexthop_id { nexthop_id: "20" } }
                }
              }
            }
            updates {
              type: INSERT
              table_entry {
                vrf_table_entry {
                  match { vrf_id: "vrf-3" }
                  action { no_action {} }
                }
              }
            }
          )pb",
          ir_p4_info_));

  auto failed_vrf_entry =
      test_lib::AppDbEntryBuilder{}
          .SetTableName("FIXED_VRF_TABLE")
          .AddMatchField("vrf_id", "vrf-1");

  p4rt_service_.GetVrfAppDbTable().SetResponseForKey(
      "vrf-1", "SWSS_RC_INVALID_PARAM", "error with vrf-1");

  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                             write_request),
      StatusIs(absl::StatusCode::kUnknown,
               AllOf(HasSubstr("#1: INVALID_ARGUMENT: error with vrf-1"),
                     HasSubstr("#2: ABORTED: Not attempted"),
                     HasSubstr("#3: ABORTED: Not attempted"))));
}

TEST_F(ResponsePathTest, FailsOnFirstErrorInP4rtTable) {
  // Any P4RT error in write request translation should fail on first error,
  // with the first error having the actual failed code and the subsequent ones
  // with ABORTED and the error string as not attempted. Force a P4 contraint
  // violation in the PiToIr translation in the second request.
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest write_request,
      test_lib::PdWriteRequestToPi(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                acl_ingress_table_entry {
                  match {
                    is_ipv4 { value: "0x1" }
                    dst_ip { value: "11.32.15.4" mask: "11.32.15.5" }
                  }
                  priority: 10
                  action { acl_forward {} }
                }
              }
            }
            updates {
              type: INSERT
              table_entry {
                acl_ingress_table_entry {
                  match { dst_ip { value: "10.43.12.4" mask: "10.43.12.5" } }
                  priority: 10
                  action { acl_forward {} }
                }
              }
            }
            updates {
              type: INSERT
              table_entry {
                acl_ingress_table_entry {
                  match {
                    is_ipv4 { value: "0x1" }
                    dst_ip { value: "51.74.32.4" mask: "51.74.32.5" }
                  }
                  priority: 10
                  action { acl_forward {} }
                }
              }
            }
          )pb",
          ir_p4_info_));

  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                             write_request),
      StatusIs(
          absl::StatusCode::kUnknown,
          AllOf(HasSubstr("#1: OK"),
                HasSubstr("#2: INVALID_ARGUMENT: All entries must satisfy"),
                HasSubstr("#3: ABORTED: Not attempted"))));
}

TEST_F(ResponsePathTest, FailOnFirstErrorFromAppdbResponses) {
  // If write requests are written to APP_DB successfully, App db responses
  // should reflect fail on first error.
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest write_request,
      test_lib::PdWriteRequestToPi(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                ipv6_table_entry {
                  match {
                    vrf_id: "vrf-1"
                    ipv6_dst { value: "2002:a17:506:c111::" prefix_length: 64 }
                  }
                  action { set_nexthop_id { nexthop_id: "20" } }
                }
              }
            }
            updates {
              type: INSERT
              table_entry {
                ipv6_table_entry {
                  match {
                    vrf_id: "vrf-2"
                    ipv6_dst { value: "2002:a17:506:c112::" prefix_length: 64 }
                  }
                  action { set_nexthop_id { nexthop_id: "20" } }
                }
              }
            }
            updates {
              type: INSERT
              table_entry {
                ipv6_table_entry {
                  match {
                    vrf_id: "vrf-3"
                    ipv6_dst { value: "2002:a17:506:c113::" prefix_length: 64 }
                  }
                  action { set_nexthop_id { nexthop_id: "20" } }
                }
              }
            }
          )pb",
          ir_p4_info_));

  // Fake valid error (INVALID_ARG) for second and NOT_EXECUTED for subsequent
  // ones.
  auto failed_ipv6_entry2 =
      test_lib::AppDbEntryBuilder{}
          .SetTableName("FIXED_IPV6_TABLE")
          .AddMatchField("ipv6_dst", "2002:a17:506:c112::/64")
          .AddMatchField("vrf_id", "vrf-2");
  p4rt_service_.GetP4rtAppDbTable().SetResponseForKey(
      failed_ipv6_entry2.GetKey(), "SWSS_RC_INVALID_PARAM", "error with vrf-2");

  auto failed_ipv6_entry3 =
      test_lib::AppDbEntryBuilder{}
          .SetTableName("FIXED_IPV6_TABLE")
          .AddMatchField("ipv6_dst", "2002:a17:506:c113::/64")
          .AddMatchField("vrf_id", "vrf-3");
  p4rt_service_.GetP4rtAppDbTable().SetResponseForKey(
      failed_ipv6_entry3.GetKey(), "SWSS_RC_NOT_EXECUTED",
      "SWSS_RC_NOT_EXECUTED");

  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                             write_request),
      StatusIs(absl::StatusCode::kUnknown,
               AllOf(HasSubstr("#1: OK"),
                     HasSubstr("#2: INVALID_ARGUMENT: error with vrf-2"),
                     HasSubstr("#3: ABORTED: SWSS_RC_NOT_EXECUTED"))));
}

TEST_F(ResponsePathTest, ReadingIgnoresRedisDbValues) {
  // Install invalid P4RT table entries in the AppDb.
  p4rt_service_.GetP4rtAppDbTable().InsertTableEntry(
      /*key=*/"out_of_order", /*values=*/{{"action", "invalid_action_name"}});

  // The P4RT App should not read anything back, because it uses a cache on the
  // read path.
  p4::v1::ReadRequest read_request;
  read_request.add_entities()->mutable_table_entry();
  ASSERT_OK_AND_ASSIGN(
      p4::v1::ReadResponse read_response,
      pdpi::SetMetadataAndSendPiReadRequest(p4rt_session_.get(), read_request));
  EXPECT_EQ(read_response.entities_size(), 0);
}

TEST_F(ResponsePathTest, WriteRequestsUpdateStatistics) {
  // A sample P4 write request.
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest write_request,
      test_lib::PdWriteRequestToPi(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                ipv6_table_entry {
                  match {
                    vrf_id: "80"
                    ipv6_dst { value: "2002:a17:506:c114::" prefix_length: 64 }
                  }
                  action { set_nexthop_id { nexthop_id: "20" } }
                }
              }
            }
          )pb",
          ir_p4_info_));

  // Statistics should monitor INSERT, MODIFY, and DELETE requests. It should
  // not include the requests count that did not make it to APP_DB layer.
  EXPECT_OK(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   write_request));
  EXPECT_THAT(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                     write_request),
              Not(IsOk()));

  write_request.mutable_updates(0)->set_type(p4::v1::Update::MODIFY);
  EXPECT_OK(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   write_request));

  write_request.mutable_updates(0)->set_type(p4::v1::Update::DELETE);
  EXPECT_OK(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   write_request));

  // Runtime can be unpredictible so we simply verify that it is no longer 0s
  // for writes.
  ASSERT_OK_AND_ASSIGN(
      FlowProgrammingStatistics flow_stats,
      p4rt_service_.GetP4rtServer().GetFlowProgrammingStatistics());
  EXPECT_THAT(
      flow_stats,
      FieldsAre(/*write_batches=*/4, /*write_requests=*/3,
                /*write_time=*/Not(absl::ZeroDuration()),
                /*max_write_time=*/Not(absl::ZeroDuration()),
                /*read_requests=*/0, /*read_time=*/absl::ZeroDuration()));

  // Reading stats should reset values to zero.
  ASSERT_OK_AND_ASSIGN(
      flow_stats, p4rt_service_.GetP4rtServer().GetFlowProgrammingStatistics());
  EXPECT_THAT(flow_stats,
              FieldsAre(0, 0, absl::ZeroDuration(), absl::ZeroDuration(), 0,
                        absl::ZeroDuration()));
}

TEST_F(ResponsePathTest, ReadRequestsUpdateStatistics) {
  p4::v1::ReadRequest read_request;
  read_request.add_entities()->mutable_table_entry();
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiReadRequest(p4rt_session_.get(), read_request));
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiReadRequest(p4rt_session_.get(), read_request));

  // Runtime can be unpredictible so we simply verify that it is no longer 0s
  // for reads.
  ASSERT_OK_AND_ASSIGN(
      FlowProgrammingStatistics flow_stats,
      p4rt_service_.GetP4rtServer().GetFlowProgrammingStatistics());
  EXPECT_THAT(flow_stats, FieldsAre(/*write_batches=*/0, /*write_requests=*/0,
                                    /*write_time=*/absl::ZeroDuration(),
                                    /*max_write_time=*/absl::ZeroDuration(),
                                    /*read_requests=*/2,
                                    /*read_time=*/Not(absl::ZeroDuration())));

  // Reading stats should reset values to zero.
  ASSERT_OK_AND_ASSIGN(
      flow_stats, p4rt_service_.GetP4rtServer().GetFlowProgrammingStatistics());
  EXPECT_THAT(flow_stats,
              FieldsAre(0, 0, absl::ZeroDuration(), absl::ZeroDuration(), 0,
                        absl::ZeroDuration()));
}

TEST_F(ResponsePathTest, WriteRequestsStatisticsHandleBatchRequests) {
  // A sample P4 write request.
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest write_request,
      test_lib::PdWriteRequestToPi(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                ipv6_table_entry {
                  match {
                    vrf_id: "80"
                    ipv6_dst { value: "2002:a17:506:c114::" prefix_length: 64 }
                  }
                  action { set_nexthop_id { nexthop_id: "20" } }
                }
              }
            }
            updates {
              type: INSERT
              table_entry {
                ipv6_table_entry {
                  match {
                    vrf_id: "80"
                    ipv6_dst { value: "2002:a17:506:c115::" prefix_length: 64 }
                  }
                  action { set_nexthop_id { nexthop_id: "20" } }
                }
              }
            }
          )pb",
          ir_p4_info_));

  // Statistics should monitor INSERT, MODIFY, and DELETE requests. It should
  // also include time for requests that fail.
  EXPECT_OK(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   write_request));

  ASSERT_OK_AND_ASSIGN(
      FlowProgrammingStatistics flow_stats,
      p4rt_service_.GetP4rtServer().GetFlowProgrammingStatistics());
  EXPECT_THAT(flow_stats,
              FieldsAre(/*write_batches=*/1, /*write_requests=*/2,
                        /*write_time=*/Not(absl::ZeroDuration()),
                        /*max_write_time=*/Not(absl::ZeroDuration()), _, _));
}

TEST_F(ResponsePathTest, WriteRequestsStatisticsDoNotIncludeInvalidPiEntries) {
  // We start with 3 valud IPv6 table entries because the PD to PI libraries
  // will reject invalid requests.
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest write_request,
      test_lib::PdWriteRequestToPi(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                ipv6_table_entry {
                  match {
                    vrf_id: "80"
                    ipv6_dst { value: "2002:a17:506:c114::" prefix_length: 64 }
                  }
                  action { set_nexthop_id { nexthop_id: "20" } }
                }
              }
            }
            updates {
              type: INSERT
              table_entry {
                ipv6_table_entry {
                  match {
                    vrf_id: "80"
                    ipv6_dst { value: "2002:a17:506:c115::" prefix_length: 64 }
                  }
                  action { set_nexthop_id { nexthop_id: "20" } }
                }
              }
            }
            updates {
              type: INSERT
              table_entry {
                ipv6_table_entry {
                  match {
                    vrf_id: "80"
                    ipv6_dst { value: "2002:a17:506:c116::" prefix_length: 64 }
                  }
                  action { set_nexthop_id { nexthop_id: "20" } }
                }
              }
            }
          )pb",
          ir_p4_info_));

  // Manually modify the 2nd request so that it uses a ternary field. Because
  // VRF uses an exact match and IPv6 DST uses a LPM we know the ternary field
  // will be invalid.
  *write_request.mutable_updates(1)
       ->mutable_entity()
       ->mutable_table_entry()
       ->mutable_match(0)
       ->mutable_ternary()
       ->mutable_value() = "bad value.";

  // Because of the invalid input we expect the 2nd request to be invalid and
  // the 3rd request to get aborted.
  ASSERT_THAT(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                     write_request),
              StatusIs(absl::StatusCode::kUnknown));

  // Only the 1st request makes it through the translation step so we should
  // only see 1 write request total.
  ASSERT_OK_AND_ASSIGN(
      FlowProgrammingStatistics flow_stats,
      p4rt_service_.GetP4rtServer().GetFlowProgrammingStatistics());
  EXPECT_THAT(flow_stats,
              FieldsAre(/*write_batches=*/1, /*write_requests=*/1,
                        /*write_time=*/Not(absl::ZeroDuration()),
                        /*max_write_time=*/Not(absl::ZeroDuration()), _, _));
}

TEST_F(ResponsePathTest, ReadCacheUsesCanonicalFormToStoreTableEntries) {
  // The insert and modify requests will have the same logical IPv6 LPM value,
  // but the modify removes the preceeding zero bits to make the requests
  // syntactically different.
  p4::v1::WriteRequest insert_request;
  ASSERT_OK(gutil::ReadProtoFromString(
      R"pb(updates {
             type: INSERT
             entity {
               table_entry {
                 table_id: 33554501
                 match {
                   field_id: 1
                   exact { value: "80" }
                 }
                 match {
                   field_id: 2
                   lpm {
                     value: "\000\000\000\000\000\000\024\000\000\000\000\000\000\000\000"
                     prefix_len: 64
                   }
                 }
                 action {
                   action {
                     action_id: 16777221
                     params { param_id: 1 value: "20" }
                   }
                 }
               }
             }
           })pb",
      &insert_request));

  p4::v1::WriteRequest modify_request;
  ASSERT_OK(gutil::ReadProtoFromString(
      R"pb(updates {
             type: MODIFY
             entity {
               table_entry {
                 table_id: 33554501
                 match {
                   field_id: 1
                   exact { value: "80" }
                 }
                 match {
                   field_id: 2
                   lpm {
                     value: "\024\000\000\000\000\000\000\000\000"
                     prefix_len: 64
                   }
                 }
                 action {
                   action {
                     action_id: 16777221
                     params { param_id: 1 value: "20" }
                   }
                 }
               }
             }
           })pb",
      &modify_request));

  p4::v1::ReadRequest read_request;
  read_request.add_entities()->mutable_table_entry();

  EXPECT_OK(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   insert_request));
  EXPECT_OK(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                   modify_request));
  ASSERT_OK_AND_ASSIGN(
      p4::v1::ReadResponse read_response,
      pdpi::SetMetadataAndSendPiReadRequest(p4rt_session_.get(), read_request));

  // Because we only inserted and modified one entry we should only read back
  // that entry.
  EXPECT_EQ(read_response.entities_size(), 1);
}

TEST_F(ResponsePathTest, OnlyTheFirstErrorShouldNotBeMarkedAborted) {
  // P4 write request.
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest write_request,
      test_lib::PdWriteRequestToPi(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                ipv6_table_entry {
                  match {
                    vrf_id: "80"
                    ipv6_dst { value: "2002:a17:506:c114::" prefix_length: 64 }
                  }
                  action { set_nexthop_id { nexthop_id: "20" } }
                }
              }
            }
            updates {
              type: INSERT
              table_entry {
                ipv6_table_entry {
                  match {
                    vrf_id: "80"
                    ipv6_dst { value: "2002:a17:506:c115::" prefix_length: 64 }
                  }
                  action { set_nexthop_id { nexthop_id: "20" } }
                }
              }
            }
          )pb",
          ir_p4_info_));

  // Expected P4RT AppDb entry.
  auto table_entry1 = test_lib::AppDbEntryBuilder{}
                          .SetTableName("FIXED_IPV6_TABLE")
                          .AddMatchField("ipv6_dst", "2002:a17:506:c114::/64")
                          .AddMatchField("vrf_id", "80")
                          .SetAction("set_nexthop_id")
                          .AddActionParam("nexthop_id", "20");
  auto table_entry2 = test_lib::AppDbEntryBuilder{}
                          .SetTableName("FIXED_IPV6_TABLE")
                          .AddMatchField("ipv6_dst", "2002:a17:506:c115::/64")
                          .AddMatchField("vrf_id", "80")
                          .SetAction("set_nexthop_id")
                          .AddActionParam("nexthop_id", "20");

  // Simulate 2 errors from the lower layers.
  p4rt_service_.GetP4rtAppDbTable().SetResponseForKey(
      table_entry1.GetKey(), "SWSS_RC_INVALID_PARAM", "my error message");
  p4rt_service_.GetP4rtAppDbTable().SetResponseForKey(
      table_entry2.GetKey(), "SWSS_RC_INVALID_PARAM", "my error message");

  EXPECT_THAT(pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                     write_request),
              StatusIs(absl::StatusCode::kUnknown,
                       AllOf(HasSubstr("#1: INVALID_ARGUMENT"),
                             HasSubstr("#2: ABORTED"))));
}

}  // namespace
}  // namespace p4rt_app
