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
#include "p4_pdpi/pd.h"
#include "p4rt_app/tests/lib/app_db_entry_builder.h"
#include "p4rt_app/tests/lib/p4runtime_component_test_fixture.h"
#include "p4rt_app/tests/lib/p4runtime_grpc_service.h"
#include "p4rt_app/tests/lib/p4runtime_request_helpers.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "swss/fakes/fake_sonic_db_table.h"

namespace p4rt_app {
namespace {

using ::gutil::EqualsProto;
using ::gutil::StatusIs;
using ::testing::HasSubstr;

// Testing end-to-end functionality unique to ACL entries (e.g. reading back
// port counters, or programming meters, etc.).
class AclTableTest : public test_lib::P4RuntimeComponentTestFixture {
 protected:
  AclTableTest()
      : test_lib::P4RuntimeComponentTestFixture(
            sai::Instantiation::kMiddleblock,
            /*gnmi_ports=*/{}) {}
};

TEST_F(AclTableTest, ReadCounters) {
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::PdWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               table_entry {
                                 acl_ingress_table_entry {
                                   match { is_ip { value: "0x1" } }
                                   priority: 10
                                   action { copy { qos_queue: "0x1" } }
                                 }
                               }
                             }
                           )pb",
                           ir_p4_info_));
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));

  // Fake OrchAgent updating the counters.
  auto counter_db_entry = test_lib::AppDbEntryBuilder{}
                              .SetTableName("P4RT:ACL_ACL_INGRESS_TABLE")
                              .SetPriority(10)
                              .AddMatchField("is_ip", "0x1");
  p4rt_service_.GetP4rtCountersDbTable().InsertTableEntry(
      counter_db_entry.GetKey(), {{"packets", "1"}, {"bytes", "128"}});

  // Verify the entry we read back has counter information.
  p4::v1::ReadRequest read_request;
  read_request.add_entities()->mutable_table_entry();
  ASSERT_OK_AND_ASSIGN(
      p4::v1::ReadResponse read_response,
      pdpi::SetMetadataAndSendPiReadRequest(p4rt_session_.get(), read_request));

  ASSERT_EQ(read_response.entities_size(), 1);  // Only one write.
  EXPECT_THAT(read_response.entities(0).table_entry().counter_data(),
              EqualsProto(R"pb(byte_count: 128 packet_count: 1)pb"));
}

TEST_F(AclTableTest, ReadMeters) {
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest request,
      test_lib::PdWriteRequestToPi(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                acl_ingress_table_entry {
                  match { is_ip { value: "0x1" } }
                  priority: 10
                  action { copy { qos_queue: "0x1" } }
                  meter_config { bytes_per_second: 123 burst_bytes: 456 }
                }
              }
            }
          )pb",
          ir_p4_info_));
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));

  // Verify we can read back the meter information.
  p4::v1::ReadRequest read_request;
  read_request.add_entities()->mutable_table_entry();
  ASSERT_OK_AND_ASSIGN(
      p4::v1::ReadResponse read_response,
      pdpi::SetMetadataAndSendPiReadRequest(p4rt_session_.get(), read_request));

  ASSERT_EQ(read_response.entities_size(), 1);  // Only one write.
  EXPECT_THAT(read_response.entities(0).table_entry().meter_config(),
              EqualsProto(
                  R"pb(
                    cir: 123 cburst: 456 pir: 123 pburst: 456
                  )pb"));
}

TEST_F(AclTableTest, CannotInsertEntryThatFailsAConstraintCheck) {
  // The ACL pre ingress table requires the is_ipv4 field to be set if we are
  // matching on a dst_ip.
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest request,
      test_lib::PdWriteRequestToPi(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                acl_pre_ingress_table_entry {
                  match { dst_ip { value: "10.0.0.1" mask: "255.255.255.255" } }
                  priority: 2000
                  action { set_vrf { vrf_id: "20" } }
                }
              }
            }
          )pb",
          ir_p4_info_));
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kUnknown, HasSubstr("#1: INVALID_ARGUMENT")));
}

}  // namespace
}  // namespace p4rt_app
