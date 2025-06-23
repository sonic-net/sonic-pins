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
#include <string>

#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "gmock/gmock.h"
#include "grpcpp/support/status.h"
#include "gtest/gtest.h"
#include "gutil/gutil/io.h"
#include "p4_infra/p4_runtime/p4_runtime_session.h"
#include "p4rt_app/event_monitoring/config_db_queue_table_event.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/tests/lib/p4runtime_component_test_fixture.h"
#include "p4rt_app/tests/lib/p4runtime_grpc_service.h"
#include "p4rt_app/tests/lib/p4runtime_request_helpers.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "swss/schema.h"

namespace p4rt_app {
namespace {

using ::testing::HasSubstr;

class DebugDataDumpTest : public test_lib::P4RuntimeComponentTestFixture {
 protected:
  DebugDataDumpTest()
      : test_lib::P4RuntimeComponentTestFixture(
            sai::Instantiation::kMiddleblock) {}
};

TEST_F(DebugDataDumpTest, VerifyDebugDumpPacketIoCountersToCorrectFile) {
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet0", "1"));
  ConfigDbQueueTableEventHandler db_handler(&p4rt_service_.GetP4rtServer());
  ASSERT_OK(db_handler.HandleEvent(SET_COMMAND, "CPU", {{"queue10", "10"}}));
  ASSERT_OK(db_handler.HandleEvent(SET_COMMAND, "FRONT_PANEL",
                                   {{"fq_queue12", "12"}}));

  // Add entry so entity cache is populated.
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

  std::string temp_dir = testing::TempDir();
  EXPECT_OK(p4rt_service_.GetP4rtServer().DumpDebugData(temp_dir, "alert"));

  // Check if files exist and have values.
  ASSERT_OK_AND_ASSIGN(std::string packetio_debugs,
                       gutil::ReadFile(temp_dir + "/packet_io_counters"));
  ASSERT_FALSE(packetio_debugs.empty());

  ASSERT_OK_AND_ASSIGN(std::string port_translation_debugs,
                       gutil::ReadFile(temp_dir + "/port_translation_map"));
  EXPECT_THAT(port_translation_debugs, HasSubstr("Ethernet0 : 1\n"));

  ASSERT_OK_AND_ASSIGN(std::string queue_translation_debugs,
                       gutil::ReadFile(temp_dir + "/queue_translation_maps"));
  EXPECT_THAT(queue_translation_debugs, HasSubstr("queue10 : 10\n"));
  EXPECT_THAT(queue_translation_debugs, HasSubstr("fq_queue12 : 12\n"));

  ASSERT_OK_AND_ASSIGN(std::string entity_cache_debugs,
                       gutil::ReadFile(temp_dir + "/entity_cache"));
  ASSERT_FALSE(entity_cache_debugs.empty());
}

}  // namespace
}  // namespace p4rt_app
