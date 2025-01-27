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
#include "absl/strings/str_format.h"
#include "absl/types/optional.h"
#include "gmock/gmock.h"
#include "grpcpp/client_context.h"
#include "grpcpp/security/credentials.h"
#include "grpcpp/support/sync_stream.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
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

using P4RuntimeStream =
    ::grpc::ClientReaderWriter<p4::v1::StreamMessageRequest,
                               p4::v1::StreamMessageResponse>;

p4::v1::Uint128 ElectionId(int high, int low = 0) {
  p4::v1::Uint128 election_id;
  election_id.set_high(high);
  election_id.set_low(low);
  return election_id;
}

absl::Status AllResponsesWereHandled(P4RuntimeStream& stream) {
  // Let the server know that the test is done writing requests so that it can
  // close the stream.
  stream.WritesDone();

  // Collect any outstanding  responses that the test may have missed.
  int count = 0;
  p4::v1::StreamMessageResponse response;
  while (stream.Read(&response)) {
    LOG(ERROR) << "Unhandled response: " << response.DebugString();
    ++count;
  }

  // If any responses were missed report an error.
  if (count > 0) {
    return absl::UnknownError(
        absl::StrFormat("Found %d unhandled response(s).", count));
  }

  return gutil::GrpcStatusToAbslStatus(stream.Finish());
}

absl::StatusOr<p4::v1::StreamMessageResponse> ReadNextArbitrationResponse(
    P4RuntimeStream& stream) {
  p4::v1::StreamMessageResponse response;
  if (!stream.Read(&response)) {
    return gutil::InternalErrorBuilder() << "Did not receive stream response: "
                                         << stream.Finish().error_message();
  }
  return response;
}

class RoleTest : public testing::Test {
 protected:
  void SetUp() override {
    ASSERT_OK(p4rt_service_.GetP4rtServer().UpdateDeviceId(p4rt_device_id_));
    p4rt_grpc_address_ = absl::StrCat("localhost:", p4rt_service_.GrpcPort());
    p4rt_stub_ = p4::v1::P4Runtime::NewStub(grpc::CreateChannel(
        p4rt_grpc_address_, grpc::InsecureChannelCredentials()));
  }

  absl::StatusOr<p4::v1::StreamMessageResponse> SendArbitrationRequest(
      P4RuntimeStream& stream, const std::string& role,
      const p4::v1::Uint128& election_id) {
    p4::v1::StreamMessageRequest request;
    request.mutable_arbitration()->set_device_id(p4rt_device_id_);
    request.mutable_arbitration()->mutable_role()->set_name(role);
    *request.mutable_arbitration()->mutable_election_id() = election_id;

    stream.Write(request);
    return ReadNextArbitrationResponse(stream);
  }

  test_lib::P4RuntimeGrpcService p4rt_service_ =
      test_lib::P4RuntimeGrpcService(P4RuntimeImplOptions{});

  std::string p4rt_grpc_address_;
  int p4rt_device_id_ = 183807201;
  std::unique_ptr<p4::v1::P4Runtime::Stub> p4rt_stub_;

  // RoleTests are written against the P4 middle block.
  const p4::config::v1::P4Info p4_info_ =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);
  const pdpi::IrP4Info ir_p4_info_ =
      sai::GetIrP4Info(sai::Instantiation::kMiddleblock);
};

TEST_F(RoleTest, EachRoleCanHaveItsOwnPrimaryConnection) {
  // Use 2 separate streams to the p4rt server.
  grpc::ClientContext context0;
  std::unique_ptr<P4RuntimeStream> stream0 =
      p4rt_stub_->StreamChannel(&context0);
  grpc::ClientContext context1;
  std::unique_ptr<P4RuntimeStream> stream1 =
      p4rt_stub_->StreamChannel(&context1);

  // Each connection connects with the same election ID, but the roles are
  // different.
  ASSERT_OK_AND_ASSIGN(
      p4::v1::StreamMessageResponse response0,
      SendArbitrationRequest(*stream0, "role0", ElectionId(200)));
  ASSERT_OK_AND_ASSIGN(
      p4::v1::StreamMessageResponse response1,
      SendArbitrationRequest(*stream1, "role1", ElectionId(200)));

  // We expect both connections to be recognized as the primary.
  EXPECT_EQ(response0.arbitration().status().code(), grpc::StatusCode::OK);
  EXPECT_EQ(response1.arbitration().status().code(), grpc::StatusCode::OK);

  // Sanity check that all arbitration responses were handled.
  ASSERT_OK(AllResponsesWereHandled(*stream0));
  ASSERT_OK(AllResponsesWereHandled(*stream1));
}

TEST_F(RoleTest, EachRoleCanHaveAPrimaryAndBackupConnection) {
  // Use 4 separate streams to the p4rt server.
  grpc::ClientContext context0;
  std::unique_ptr<P4RuntimeStream> primary0 =
      p4rt_stub_->StreamChannel(&context0);
  grpc::ClientContext context1;
  std::unique_ptr<P4RuntimeStream> backup0 =
      p4rt_stub_->StreamChannel(&context1);
  grpc::ClientContext context2;
  std::unique_ptr<P4RuntimeStream> primary1 =
      p4rt_stub_->StreamChannel(&context2);
  grpc::ClientContext context3;
  std::unique_ptr<P4RuntimeStream> backup1 =
      p4rt_stub_->StreamChannel(&context3);

  // For role0 the primary connection will use election ID 200, and the backup
  // will use election ID 199.
  ASSERT_OK_AND_ASSIGN(
      p4::v1::StreamMessageResponse primary0_response,
      SendArbitrationRequest(*primary0, "role0", ElectionId(200)));
  ASSERT_OK_AND_ASSIGN(
      p4::v1::StreamMessageResponse backup0_response,
      SendArbitrationRequest(*backup0, "role0", ElectionId(199)));

  // For role1 the primary connection will use election ID 200 and the backup
  // will use election ID 199.
  ASSERT_OK_AND_ASSIGN(
      p4::v1::StreamMessageResponse primary1_response,
      SendArbitrationRequest(*primary1, "role1", ElectionId(200)));
  ASSERT_OK_AND_ASSIGN(
      p4::v1::StreamMessageResponse backup1_response,
      SendArbitrationRequest(*backup1, "role1", ElectionId(199)));

  // Verify the primary connections are recognized as such.
  EXPECT_EQ(primary0_response.arbitration().status().code(),
            grpc::StatusCode::OK);
  EXPECT_EQ(primary1_response.arbitration().status().code(),
            grpc::StatusCode::OK);

  // Verify the backup connections are recognized as such.
  EXPECT_EQ(backup0_response.arbitration().status().code(),
            grpc::StatusCode::ALREADY_EXISTS);
  EXPECT_EQ(backup1_response.arbitration().status().code(),
            grpc::StatusCode::ALREADY_EXISTS);

  // Sanity check that all arbitration responses were handled. Note we want to
  // verify the backup connections first because once the primary connection is
  // closed they will get notified.
  ASSERT_OK(AllResponsesWereHandled(*backup0));
  ASSERT_OK(AllResponsesWereHandled(*backup1));
  ASSERT_OK(AllResponsesWereHandled(*primary0));
  ASSERT_OK(AllResponsesWereHandled(*primary1));
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
  ASSERT_OK(pdpi::SetMetadataAndSetForwardingPipelineConfig(
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
                                   action { acl_copy { qos_queue: "0x1" } }
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

  ASSERT_OK(pdpi::SetMetadataAndSetForwardingPipelineConfig(
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
                                   action { acl_copy { qos_queue: "0x1" } }
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
