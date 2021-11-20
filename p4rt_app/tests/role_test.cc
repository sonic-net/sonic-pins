// Copyright 2021 Google LLC
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

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/types/optional.h"
#include "gmock/gmock.h"
#include "grpcpp/security/credentials.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4rt_app/tests/lib/p4runtime_grpc_service.h"
#include "p4rt_app/tests/lib/p4runtime_request_helpers.h"
#include "sai_p4/fixed/roles.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/roles.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace p4rt_app {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::HasSubstr;

class RoleTest : public testing::Test {
 protected:
  void SetUp() override {
    p4rt_grpc_address_ = absl::StrCat("localhost:", p4rt_service_.GrpcPort());
  }

  // Fake P4RT gRPC service.
  test_lib::P4RuntimeGrpcService p4rt_service_ =
      test_lib::P4RuntimeGrpcService(test_lib::P4RuntimeGrpcServiceOptions{});
  std::string p4rt_grpc_address_;
  int p4rt_device_id_ = 183807201;

  // RoleTests are written against the P4 middle block.
  const p4::config::v1::P4Info p4_info_ =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);
  const pdpi::IrP4Info ir_p4_info_ =
      sai::GetIrP4Info(sai::Instantiation::kMiddleblock);
};

TEST_F(RoleTest, PrimaryConnectionsPerRole) {
  EXPECT_OK(pdpi::P4RuntimeSession::Create(
      p4rt_grpc_address_, grpc::InsecureChannelCredentials(), p4rt_device_id_,
      pdpi::P4RuntimeSessionOptionalArgs{
          .election_id = 200,
          .role = P4RUNTIME_ROLE_SDN_CONTROLLER,
      }));

  EXPECT_OK(pdpi::P4RuntimeSession::Create(
      p4rt_grpc_address_, grpc::InsecureChannelCredentials(), p4rt_device_id_,
      pdpi::P4RuntimeSessionOptionalArgs{
          .election_id = 200,
          .role = P4RUNTIME_ROLE_PACKET_REPLICATION_ENGINE,
      }));
}

TEST_F(RoleTest, PrimaryAndBackupConnectionsPerRole) {
  const std::string kRole1 = "role1";
  const std::string kRole2 = "role2";

  // Primary 1.
  ASSERT_OK_AND_ASSIGN(auto primary_session1,
                       pdpi::P4RuntimeSession::Create(
                           p4rt_grpc_address_,
                           grpc::InsecureChannelCredentials(), p4rt_device_id_,
                           pdpi::P4RuntimeSessionOptionalArgs{
                               .election_id = 200,
                               .role = kRole1,
                           }));

  // Backup 1.
  EXPECT_THAT(pdpi::P4RuntimeSession::Create(p4rt_grpc_address_,
                                             grpc::InsecureChannelCredentials(),
                                             p4rt_device_id_,
                                             pdpi::P4RuntimeSessionOptionalArgs{
                                                 .election_id = 199,
                                                 .role = kRole1,
                                             }),
              StatusIs(absl::StatusCode::kInternal));

  // Primary 2.
  ASSERT_OK_AND_ASSIGN(auto primary_session2,
                       pdpi::P4RuntimeSession::Create(
                           p4rt_grpc_address_,
                           grpc::InsecureChannelCredentials(), p4rt_device_id_,
                           pdpi::P4RuntimeSessionOptionalArgs{
                               .election_id = 200,
                               .role = kRole2,
                           }));

  // Backup 2.
  EXPECT_THAT(pdpi::P4RuntimeSession::Create(p4rt_grpc_address_,
                                             grpc::InsecureChannelCredentials(),
                                             p4rt_device_id_,
                                             pdpi::P4RuntimeSessionOptionalArgs{
                                                 .election_id = 199,
                                                 .role = kRole2,
                                             }),
              StatusIs(absl::StatusCode::kInternal));
}

// TODO: Fix and re-enable this test -- it broke when
// we removed the linkqual app.
TEST_F(RoleTest, DISABLED_RolesEnforceReadWriteOnTables) {
  ASSERT_OK_AND_ASSIGN(auto controller,
                       pdpi::P4RuntimeSession::Create(
                           p4rt_grpc_address_,
                           grpc::InsecureChannelCredentials(), p4rt_device_id_,
                           pdpi::P4RuntimeSessionOptionalArgs{
                               .role = P4RUNTIME_ROLE_SDN_CONTROLLER}));

  ASSERT_OK_AND_ASSIGN(
      auto linkqual, pdpi::P4RuntimeSession::Create(
                         p4rt_grpc_address_, grpc::InsecureChannelCredentials(),
                         p4rt_device_id_,
                         pdpi::P4RuntimeSessionOptionalArgs{
                             // TODO: Since linkqual got removed,
                             // we need to find a viable replacement.
                             // .role = P4RUNTIME_ROLE_LINKQUAL_APP,
                         }));

  // Either primary connection can set the forwarding config.
  ASSERT_OK(pdpi::SetForwardingPipelineConfig(
      controller.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      p4_info_));

  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest ingress_write,
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
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest linkqual_write,
      test_lib::PdWriteRequestToPi(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                acl_linkqual_table_entry {
                  match { ether_type { value: "0x0800" mask: "0xffff" } }
                  priority: 10
                  action { linkqual_drop {} }
                }
              }
            }
          )pb",
          ir_p4_info_));

  // controller can write to the ingress ACL table, and linkqual can write to
  // the linkqual ACL table.
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(controller.get(), ingress_write));
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(linkqual.get(), linkqual_write));

  // controller can not write to the linkqual ACL table.
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(controller.get(), linkqual_write),
      StatusIs(absl::StatusCode::kUnknown, HasSubstr("PERMISSION_DENIED")));

  // linkqual can not write to the ingress ACL table.
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(linkqual.get(), ingress_write),
      StatusIs(absl::StatusCode::kUnknown, HasSubstr("PERMISSION_DENIED")));

  // controller does not read state from the linkqual ACL table.
  p4::v1::ReadResponse expected_controller_response;
  *expected_controller_response.add_entities()->mutable_table_entry() =
      ingress_write.updates(0).entity().table_entry();

  p4::v1::ReadRequest controller_read;
  controller_read.add_entities()->mutable_table_entry();
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiReadRequest(controller.get(), controller_read),
      IsOkAndHolds(EqualsProto(expected_controller_response)));

  // linkqual does not read state from the ingress ACL table.
  p4::v1::ReadResponse expected_linkqual_response;
  *expected_linkqual_response.add_entities()->mutable_table_entry() =
      linkqual_write.updates(0).entity().table_entry();

  p4::v1::ReadRequest linkqual_read;
  linkqual_read.add_entities()->mutable_table_entry();
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiReadRequest(linkqual.get(), linkqual_read),
      IsOkAndHolds(EqualsProto(expected_linkqual_response)));
}

TEST_F(RoleTest, DefaultRoleCanWriteAndReadAnyTable) {
  ASSERT_OK_AND_ASSIGN(
      auto default_role,
      pdpi::P4RuntimeSession::Create(
          p4rt_grpc_address_, grpc::InsecureChannelCredentials(),
          p4rt_device_id_, pdpi::P4RuntimeSessionOptionalArgs{.role = ""}));

  ASSERT_OK(pdpi::SetForwardingPipelineConfig(
      default_role.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      p4_info_));

  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest ingress_write,
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
  EXPECT_OK(pdpi::SetMetadataAndSendPiWriteRequest(default_role.get(),
                                                   ingress_write));
  // TODO: Install a second table entry using a different role here, once one is
  // avalable. This is to ensure tthat he default role reads back the table
  // entries installed with *any* role.
  p4::v1::ReadResponse expected_response;
  *expected_response.add_entities()->mutable_table_entry() =
      ingress_write.updates(0).entity().table_entry();

  p4::v1::ReadRequest read_request;
  read_request.add_entities()->mutable_table_entry();
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiReadRequest(default_role.get(), read_request),
      IsOkAndHolds(EqualsProto(expected_response)));
}

}  // namespace
}  // namespace p4rt_app
