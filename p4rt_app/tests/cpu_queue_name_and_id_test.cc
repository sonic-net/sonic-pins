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

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_runtime/p4_runtime_session.h"
#include "p4rt_app/event_monitoring/config_db_queue_table_event.h"
#include "p4rt_app/sonic/adapters/fake_sonic_db_table.h"
#include "p4rt_app/tests/lib/app_db_entry_builder.h"
#include "p4rt_app/tests/lib/p4runtime_component_test_fixture.h"
#include "p4rt_app/tests/lib/p4runtime_request_helpers.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "swss/schema.h"

namespace p4rt_app {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::testing::UnorderedElementsAreArray;

class CpuQueueTest : public test_lib::P4RuntimeComponentTestFixture {
 protected:
  CpuQueueTest()
      : test_lib::P4RuntimeComponentTestFixture(
            sai::Instantiation::kMiddleblock) {}
};

TEST_F(CpuQueueTest, CpuQueueIdsResultInAppDbQueueIds) {
  ConfigDbQueueTableEventHandler db_handler(&p4rt_service_.GetP4rtServer());
  ASSERT_OK(db_handler.HandleEvent(SET_COMMAND, "CPU", {{"queue10", "10"}}));

  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::PdWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               table_entry {
                                 acl_ingress_table_entry {
                                   match { is_ip { value: "0x1" } }
                                   priority: 10
                                   action { acl_copy { qos_queue: "0xa" } }
                                 }
                               }
                             }
                           )pb",
                           ir_p4_info_));

  auto expected_entry = test_lib::AppDbEntryBuilder{}
                            .SetTableName("ACL_ACL_INGRESS_TABLE")
                            .AddMatchField("is_ip", "0x1")
                            .SetPriority(10)
                            .SetAction("acl_copy")
                            .AddActionParam("qos_queue", "0xa");
  EXPECT_OK(p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                         request));
  EXPECT_THAT(
      p4rt_service_.GetP4rtAppDbTable().ReadTableEntry(expected_entry.GetKey()),
      IsOkAndHolds(UnorderedElementsAreArray(expected_entry.GetValueMap())));
}

TEST_F(CpuQueueTest, CpuQueueNamesResultInAppDbQueueIds) {
  ConfigDbQueueTableEventHandler db_handler(&p4rt_service_.GetP4rtServer());
  ASSERT_OK(db_handler.HandleEvent(SET_COMMAND, "CPU", {{"queue10", "10"}}));

  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::PdWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               table_entry {
                                 acl_ingress_table_entry {
                                   match { is_ip { value: "0x1" } }
                                   priority: 10
                                   action { acl_copy { qos_queue: "queue10" } }
                                 }
                               }
                             }
                           )pb",
                           ir_p4_info_));

  auto expected_entry = test_lib::AppDbEntryBuilder{}
                            .SetTableName("ACL_ACL_INGRESS_TABLE")
                            .AddMatchField("is_ip", "0x1")
                            .SetPriority(10)
                            .SetAction("acl_copy")
                            .AddActionParam("qos_queue", "0xa");
  EXPECT_OK(p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                         request));
  EXPECT_THAT(
      p4rt_service_.GetP4rtAppDbTable().ReadTableEntry(expected_entry.GetKey()),
      IsOkAndHolds(UnorderedElementsAreArray(expected_entry.GetValueMap())));
}

TEST_F(CpuQueueTest, CpuQueueIdsReadBackAsIds) {
  ConfigDbQueueTableEventHandler db_handler(&p4rt_service_.GetP4rtServer());
  ASSERT_OK(db_handler.HandleEvent(SET_COMMAND, "CPU", {{"queue10", "10"}}));

  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::PdWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               table_entry {
                                 acl_ingress_table_entry {
                                   match { is_ip { value: "0x1" } }
                                   priority: 10
                                   action { acl_copy { qos_queue: "0xa" } }
                                 }
                               }
                             }
                           )pb",
                           ir_p4_info_));

  EXPECT_OK(p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                         request));

  // Reading back the entry should result in the same table_entry.
  p4::v1::ReadRequest read_request;
  read_request.add_entities()->mutable_table_entry();
  ASSERT_OK_AND_ASSIGN(p4::v1::ReadResponse read_response,
                       p4_runtime::SetMetadataAndSendPiReadRequest(
                           p4rt_session_.get(), read_request));
  ASSERT_EQ(read_response.entities_size(), 1);  // Only one write.
  EXPECT_THAT(read_response.entities(0),
              EqualsProto(request.updates(0).entity()));
}

TEST_F(CpuQueueTest, CpuQueueNamesReadBackAsNames) {
  ConfigDbQueueTableEventHandler db_handler(&p4rt_service_.GetP4rtServer());
  ASSERT_OK(db_handler.HandleEvent(SET_COMMAND, "CPU", {{"queue10", "10"}}));

  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::PdWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               table_entry {
                                 acl_ingress_table_entry {
                                   match { is_ip { value: "0x1" } }
                                   priority: 10
                                   action { acl_copy { qos_queue: "queue10" } }
                                 }
                               }
                             }
                           )pb",
                           ir_p4_info_));

  EXPECT_OK(p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                         request));

  // Reading back the entry should result in the same table_entry.
  p4::v1::ReadRequest read_request;
  read_request.add_entities()->mutable_table_entry();
  ASSERT_OK_AND_ASSIGN(p4::v1::ReadResponse read_response,
                       p4_runtime::SetMetadataAndSendPiReadRequest(
                           p4rt_session_.get(), read_request));
  ASSERT_EQ(read_response.entities_size(), 1);  // Only one write.
  EXPECT_THAT(read_response.entities(0),
              EqualsProto(request.updates(0).entity()));
}

TEST_F(CpuQueueTest, PreservesIdsIfCpuQueueTranslatorIsNeverSet) {
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::PdWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               table_entry {
                                 acl_ingress_table_entry {
                                   match { is_ip { value: "0x1" } }
                                   priority: 10
                                   action { acl_copy { qos_queue: "0xa" } }
                                 }
                               }
                             }
                           )pb",
                           ir_p4_info_));

  EXPECT_OK(p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                         request));

  auto expected_entry = test_lib::AppDbEntryBuilder{}
                            .SetTableName("ACL_ACL_INGRESS_TABLE")
                            .AddMatchField("is_ip", "0x1")
                            .SetPriority(10)
                            .SetAction("acl_copy")
                            .AddActionParam("qos_queue", "0xa");
  EXPECT_THAT(
      p4rt_service_.GetP4rtAppDbTable().ReadTableEntry(expected_entry.GetKey()),
      IsOkAndHolds(UnorderedElementsAreArray(expected_entry.GetValueMap())));

  // Reading back the entry should result in the same table_entry.
  p4::v1::ReadRequest read_request;
  read_request.add_entities()->mutable_table_entry();
  ASSERT_OK_AND_ASSIGN(p4::v1::ReadResponse read_response,
                       p4_runtime::SetMetadataAndSendPiReadRequest(
                           p4rt_session_.get(), read_request));
  ASSERT_EQ(read_response.entities_size(), 1);  // Only one write.
  EXPECT_THAT(read_response.entities(0),
              EqualsProto(request.updates(0).entity()));
}

TEST_F(CpuQueueTest, ForwardsUnknownQueueNamesToAppDb) {
  ConfigDbQueueTableEventHandler db_handler(&p4rt_service_.GetP4rtServer());
  ASSERT_OK(db_handler.HandleEvent(SET_COMMAND, "CPU", {{"queue10", "10"}}));

  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::PdWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               table_entry {
                                 acl_ingress_table_entry {
                                   match { is_ip { value: "0x1" } }
                                   priority: 10
                                   action { acl_copy { qos_queue: "whoami" } }
                                 }
                               }
                             }
                           )pb",
                           ir_p4_info_));

  EXPECT_OK(p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                         request));

  auto expected_entry = test_lib::AppDbEntryBuilder{}
                            .SetTableName("ACL_ACL_INGRESS_TABLE")
                            .AddMatchField("is_ip", "0x1")
                            .SetPriority(10)
                            .SetAction("acl_copy")
                            .AddActionParam("qos_queue", "whoami");
  EXPECT_THAT(
      p4rt_service_.GetP4rtAppDbTable().ReadTableEntry(expected_entry.GetKey()),
      IsOkAndHolds(UnorderedElementsAreArray(expected_entry.GetValueMap())));

  // Reading back the entry should result in the same table_entry.
  p4::v1::ReadRequest read_request;
  read_request.add_entities()->mutable_table_entry();
  ASSERT_OK_AND_ASSIGN(p4::v1::ReadResponse read_response,
                       p4_runtime::SetMetadataAndSendPiReadRequest(
                           p4rt_session_.get(), read_request));
  ASSERT_EQ(read_response.entities_size(), 1);  // Only one write.
  EXPECT_THAT(read_response.entities(0),
              EqualsProto(request.updates(0).entity()));
}

}  // namespace
}  // namespace p4rt_app
