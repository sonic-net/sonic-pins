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

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "p4/v1/p4runtime.pb.h"
// #include "gutil/gutil/proto_matchers.h"
// #include "gutil/gutil/status_matchers.h"
// #include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4rt_app/event_monitoring/config_db_queue_table_event.h"
#include "p4rt_app/tests/lib/p4runtime_component_test_fixture.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "swss/schema.h"

namespace p4rt_app {
namespace {

class FrontPanelQueueTest : public test_lib::P4RuntimeComponentTestFixture {
 protected:
  FrontPanelQueueTest()
      : test_lib::P4RuntimeComponentTestFixture(
            sai::Instantiation::kMiddleblock) {}
};

TEST_F(FrontPanelQueueTest, FrontPanelQueueIdsResultInAppDbQueueIds) {
  ConfigDbQueueTableEventHandler db_handler(&p4rt_service_.GetP4rtServer());
  ASSERT_OK(
      db_handler.HandleEvent(SET_COMMAND, "FRONT_PANEL", {{"queue15", "15"}}));

  // TODO: This requires unicast_queue_t and multicast_queue_t to
  // be in the P4 info before we can test entries this way.
  // ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
  //                      test_lib::PdWriteRequestToPi(
  //                          R"pb(
  //                            updates {
  //                              type: INSERT
  //                              table_entry {
  //                                acl_ingress_table_entry {
  //                                  match { is_ip { value: "0x1" } }
  //                                  priority: 10
  //                                  action { acl_copy { qos_queue: "0xa" } }
  //                                }
  //                              }
  //                            }
  //                          )pb",
  //                          ir_p4_info_));

  // auto expected_entry = test_lib::AppDbEntryBuilder{}
  //                           .SetTableName("ACL_ACL_INGRESS_TABLE")
  //                           .AddMatchField("is_ip", "0x1")
  //                           .SetPriority(10)
  //                           .SetAction("acl_copy")
  //                           .AddActionParam("qos_queue", "0xa");
  // EXPECT_OK(
  //     pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));
  // EXPECT_THAT(
  //     p4rt_service_.GetP4rtAppDbTable().ReadTableEntry(expected_entry.GetKey()),
  //     IsOkAndHolds(UnorderedElementsAreArray(expected_entry.GetValueMap())));
}

}  // namespace
}  // namespace p4rt_app
