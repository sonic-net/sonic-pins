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
#include <string>
#include <type_traits>
#include <unordered_map>
#include <utility>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "grpcpp/security/credentials.h"
#include "gtest/gtest.h"
#include "gutil/proto.h"
#include "gutil/proto_matchers.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4rt_app/sonic/adapters/fake_sonic_db_table.h"
#include "p4rt_app/tests/lib/app_db_entry_builder.h"
#include "p4rt_app/tests/lib/p4runtime_component_test_fixture.h"
#include "p4rt_app/tests/lib/p4runtime_grpc_service.h"
#include "p4rt_app/tests/lib/p4runtime_request_helpers.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace p4rt_app {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::AllOf;
using ::testing::HasSubstr;
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
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kUnknown,
               AllOf(HasSubstr("#1: INVALID_ARGUMENT:"),
                     HasSubstr("#2: INVALID_ARGUMENT:"))));
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

}  // namespace
}  // namespace p4rt_app
