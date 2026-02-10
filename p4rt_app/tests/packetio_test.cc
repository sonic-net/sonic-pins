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
#include <cstdint>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "grpcpp/client_context.h"
#include "grpcpp/create_channel.h"
#include "grpcpp/security/credentials.h"
#include "grpcpp/support/status.h"
#include "grpcpp/support/sync_stream.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/p4_pdpi/pd.h"
#include "p4_infra/p4_pdpi/string_encodings/hex_string.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/sonic/fake_packetio_interface.h"
#include "p4rt_app/sonic/packetio_interface.h"
#include "p4rt_app/tests/lib/p4runtime_grpc_service.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

namespace p4rt_app {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::p4::v1::P4Runtime;
using ::testing::Eq;
using ::testing::HasSubstr;
using ::testing::UnorderedElementsAre;

// Test class for PacketIo component tests.
class FakePacketIoTest : public testing::Test {
 protected:
  void SetUp() override {
    ASSERT_OK(p4rt_service_.GetP4rtServer().UpdateDeviceId(device_id_));
    const std::string address =
        absl::StrCat("localhost:", p4rt_service_.GrpcPort());
    auto stub =
        pdpi::CreateP4RuntimeStub(address, grpc::InsecureChannelCredentials());
    ASSERT_OK_AND_ASSIGN(p4rt_session_, pdpi::P4RuntimeSession::Create(
                                            std::move(stub), device_id_));
  }

  // For PacketIO to work correctly it requires both creating a port, and adding
  // a port translation.
  absl::Status AddPacketIoPort(const std::string& port_name,
                               const std::string& port_id) {
    RETURN_IF_ERROR(p4rt_service_.GetP4rtServer().AddPacketIoPort(port_name));
    RETURN_IF_ERROR(
        p4rt_service_.GetP4rtServer().AddPortTranslation(port_name, port_id));
    return absl::OkStatus();
  }

  absl::Status RemovePacketIoPort(const std::string& port_name) {
    RETURN_IF_ERROR(
        p4rt_service_.GetP4rtServer().RemovePortTranslation(port_name));
    RETURN_IF_ERROR(
        p4rt_service_.GetP4rtServer().RemovePacketIoPort(port_name));
    return absl::OkStatus();
  }

  // Form PacketOut message and write to stream channel.
  absl::Status SendPacketOut(int port, absl::string_view data,
                             const pdpi::IrP4Info& p4info) {
    // Assemble PacketOut protobuf message.
    sai::PacketOut packet_out;
    packet_out.set_payload(std::string(data));
    sai::PacketOut::Metadata& metadata = *packet_out.mutable_metadata();
    metadata.set_egress_port(absl::StrCat(port));
    metadata.set_submit_to_ingress(pdpi::BitsetToHexString<1>(0));

    // Assemble PacketOut request and write to stream channel.
    p4::v1::StreamMessageRequest request;
    ASSIGN_OR_RETURN(*request.mutable_packet(),
                     pdpi::PdPacketOutToPi(p4info, packet_out));
    RET_CHECK(p4rt_session_->StreamChannelWrite(request));
    return absl::OkStatus();
  }

  test_lib::P4RuntimeGrpcService p4rt_service_ =
      test_lib::P4RuntimeGrpcService(P4RuntimeImplOptions{});
  std::unique_ptr<pdpi::P4RuntimeSession> p4rt_session_;
  uint64_t device_id_ = 100406;
};

TEST_F(FakePacketIoTest, VerifyPacketIn) {
  ASSERT_OK(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      p4rt_session_.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      sai::GetP4Info(sai::Instantiation::kMiddleblock)));
  ASSERT_OK(AddPacketIoPort("Ethernet1/1/0", "0"));
  ASSERT_OK(AddPacketIoPort("Ethernet1/1/1", "1"));

  // Push the expected PacketIn.
  EXPECT_OK(p4rt_service_.GetFakePacketIoInterface().PushPacketIn(
      "Ethernet1/1/0", "Ethernet1/1/1", "test packet1"));
  EXPECT_OK(p4rt_service_.GetFakePacketIoInterface().PushPacketIn(
      "Ethernet1/1/1", "Ethernet1/1/0", "test packet2"));

  // Close the session and verify responses.
  EXPECT_THAT(p4rt_session_->ReadStreamChannelResponsesAndFinish(),
              IsOkAndHolds(UnorderedElementsAre(
                  EqualsProto(R"pb(
                    packet {
                      payload: "test packet1"
                      metadata { metadata_id: 1 value: "0" }
                      metadata { metadata_id: 2 value: "1" }
                    }
                  )pb"),
                  EqualsProto(R"pb(
                    packet {
                      payload: "test packet2"
                      metadata { metadata_id: 1 value: "1" }
                      metadata { metadata_id: 2 value: "0" }
                    }
                  )pb"))));

  sonic::PacketIoCounters counters =
      p4rt_service_.GetP4rtServer().GetPacketIoCounters();
  EXPECT_EQ(counters.packet_in_received, 2);
  EXPECT_EQ(counters.packet_in_errors, 0);
}

TEST_F(FakePacketIoTest, VerifyPacketInFailAfterPortRemove) {
  ASSERT_OK(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      p4rt_session_.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      sai::GetP4Info(sai::Instantiation::kMiddleblock)));

  // Add and remove a port and verify packet In fails.
  ASSERT_OK(AddPacketIoPort("Ethernet1/1/0", "0"));
  ASSERT_OK(RemovePacketIoPort("Ethernet1/1/0"));
  EXPECT_THAT(p4rt_service_.GetFakePacketIoInterface().PushPacketIn(
                  "Ethernet1/1/0", "Ethernet1/1/0", "test packet1"),
              StatusIs(absl::StatusCode::kInvalidArgument));

  sonic::PacketIoCounters counters =
      p4rt_service_.GetP4rtServer().GetPacketIoCounters();
  EXPECT_EQ(counters.packet_in_received, 0);
  EXPECT_EQ(counters.packet_in_errors, 1);
}

TEST_F(FakePacketIoTest, PacketInFailsWithoutPortTranslation) {
  ASSERT_OK(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      p4rt_session_.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      sai::GetP4Info(sai::Instantiation::kMiddleblock)));

  // Only add the PacketIO port, but not the port translation for that port.
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPacketIoPort("Ethernet1/1/0"));
  EXPECT_THAT(p4rt_service_.GetFakePacketIoInterface().PushPacketIn(
                  "Ethernet1/1/0", "Ethernet1/1/0", "test packet1"),
              StatusIs(absl::StatusCode::kInvalidArgument));

  sonic::PacketIoCounters counters =
      p4rt_service_.GetP4rtServer().GetPacketIoCounters();
  EXPECT_EQ(counters.packet_in_received, 0);
  EXPECT_EQ(counters.packet_in_errors, 1);
}

TEST_F(FakePacketIoTest, PacketOutFailsWithoutPortTranslation) {
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPacketIoPort("Ethernet1/1/0"));
  EXPECT_OK(SendPacketOut(0, "test packet1",
                          sai::GetIrP4Info(sai::Instantiation::kMiddleblock)));

  // Close the session and verify responses.
  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::StreamMessageResponse> actual_responses,
      p4rt_session_->ReadStreamChannelResponsesAndFinish());
  ASSERT_EQ(actual_responses.size(), 1);
  ASSERT_TRUE(actual_responses[0].has_error());
  ASSERT_EQ(actual_responses[0].error().canonical_code(),
            grpc::StatusCode::FAILED_PRECONDITION);

  sonic::PacketIoCounters counters =
      p4rt_service_.GetP4rtServer().GetPacketIoCounters();
  EXPECT_EQ(counters.packet_out_sent, 0);
  EXPECT_EQ(counters.packet_out_errors, 1);
}

TEST_F(FakePacketIoTest, PacketOutFailBeforeP4InfoPush) {
  ASSERT_OK(AddPacketIoPort("Ethernet1/1/0", "0"));
  EXPECT_OK(SendPacketOut(0, "test packet1",
                          sai::GetIrP4Info(sai::Instantiation::kMiddleblock)));

  // Close the session and verify responses.
  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::StreamMessageResponse> actual_responses,
      p4rt_session_->ReadStreamChannelResponsesAndFinish());
  ASSERT_EQ(actual_responses.size(), 1);
  ASSERT_TRUE(actual_responses[0].has_error());
  ASSERT_EQ(actual_responses[0].error().canonical_code(),
            grpc::StatusCode::FAILED_PRECONDITION);

  sonic::PacketIoCounters counters =
      p4rt_service_.GetP4rtServer().GetPacketIoCounters();
  EXPECT_EQ(counters.packet_out_sent, 0);
  EXPECT_EQ(counters.packet_out_errors, 1);
}

TEST_F(FakePacketIoTest, PacketOutFailAfterPortRemoval) {
  ASSERT_OK(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      p4rt_session_.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      sai::GetP4Info(sai::Instantiation::kMiddleblock)));

  // Add and remove a port and verify packet out fails.
  ASSERT_OK(AddPacketIoPort("Ethernet1/1/0", "0"));
  ASSERT_OK(
      p4rt_service_.GetP4rtServer().RemovePortTranslation("Ethernet1/1/0"));

  EXPECT_OK(SendPacketOut(0, "test packet1",
                          sai::GetIrP4Info(sai::Instantiation::kMiddleblock)));

  // Close the session and verify responses.
  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::StreamMessageResponse> actual_responses,
      p4rt_session_->ReadStreamChannelResponsesAndFinish());
  ASSERT_EQ(actual_responses.size(), 1);
  ASSERT_TRUE(actual_responses[0].has_error());
  ASSERT_EQ(actual_responses[0].error().canonical_code(),
            grpc::StatusCode::INVALID_ARGUMENT);

  sonic::PacketIoCounters counters =
      p4rt_service_.GetP4rtServer().GetPacketIoCounters();
  EXPECT_EQ(counters.packet_out_sent, 0);
  EXPECT_EQ(counters.packet_out_errors, 1);
}

TEST_F(FakePacketIoTest, PacketOutFailForSecondary) {
  // Assemble PacketOut protobuf message.
  sai::PacketOut packet_out;
  packet_out.set_payload(std::string("test packet"));
  sai::PacketOut::Metadata& metadata = *packet_out.mutable_metadata();
  metadata.set_egress_port(pdpi::BitsetToHexString<9>(/*bitset=*/0));
  metadata.set_submit_to_ingress(pdpi::BitsetToHexString<1>(0));

  // Assemble PacketOut request and write to stream channel.
  p4::v1::StreamMessageRequest request;
  ASSERT_OK_AND_ASSIGN(
      *request.mutable_packet(),
      pdpi::PdPacketOutToPi(sai::GetIrP4Info(sai::Instantiation::kMiddleblock),
                            packet_out));
  std::string address = absl::StrCat("localhost:", p4rt_service_.GrpcPort());
  auto channel =
      grpc::CreateChannel(address, grpc::InsecureChannelCredentials());
  auto stub = P4Runtime::NewStub(channel);
  grpc::ClientContext context;
  std::unique_ptr<::grpc::ClientReaderWriter<p4::v1::StreamMessageRequest,
                                             p4::v1::StreamMessageResponse>>
      stream = stub->StreamChannel(&context);
  ASSERT_TRUE(stream->Write(request));
  // Wait for a response.
  p4::v1::StreamMessageResponse response;
  ASSERT_TRUE(stream->Read(&response)) << "Did not receive stream response: "
                                       << stream->Finish().error_message();

  ASSERT_TRUE(response.has_error());
  ASSERT_THAT(response.error().canonical_code(),
              Eq(grpc::StatusCode::PERMISSION_DENIED));

  sonic::PacketIoCounters counters =
      p4rt_service_.GetP4rtServer().GetPacketIoCounters();
  EXPECT_EQ(counters.packet_out_sent, 0);
  EXPECT_EQ(counters.packet_out_errors, 1);
}

TEST_F(FakePacketIoTest, VerifyPacketOut) {
  // Needed for PacketOut.
  ASSERT_OK(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      p4rt_session_.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      sai::GetP4Info(sai::Instantiation::kMiddleblock)));
  ASSERT_OK(AddPacketIoPort("Ethernet1/1/0", "0"));
  EXPECT_OK(SendPacketOut(0, "test packet1",
                          sai::GetIrP4Info(sai::Instantiation::kMiddleblock)));
  EXPECT_OK(SendPacketOut(0, "test packet2",
                          sai::GetIrP4Info(sai::Instantiation::kMiddleblock)));

  absl::StatusOr<std::vector<std::string>> packets_or;
  // Retry for a few times with delay since it takes a few msecs for Write
  // rpc call to reach the P4RT server and the write request processed.
  for (int i = 0; i < 10; i++) {
    packets_or = p4rt_service_.GetFakePacketIoInterface().VerifyPacketOut(
        "Ethernet1/1/0");
    if (!packets_or.ok() || (*packets_or).size() != 2) {
      absl::SleepFor(absl::Seconds(2));
    } else {
      break;
    }
  }
  ASSERT_OK(packets_or);
  EXPECT_EQ(*packets_or,
            std::vector<std::string>({"test packet1", "test packet2"}));

  sonic::PacketIoCounters counters =
      p4rt_service_.GetP4rtServer().GetPacketIoCounters();
  EXPECT_EQ(counters.packet_out_sent, 2);
  EXPECT_EQ(counters.packet_out_errors, 0);
}

TEST_F(FakePacketIoTest, VerifyPacketInWithPortNames) {
  ASSERT_OK(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      p4rt_session_.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      sai::GetP4Info(sai::Instantiation::kMiddleblock)));
  ASSERT_OK(AddPacketIoPort("Ethernet1/1/0", "0"));

  // Push the expected PacketIn.
  EXPECT_OK(p4rt_service_.GetFakePacketIoInterface().PushPacketIn(
      "Ethernet1/1/0", "Ethernet1/1/0", "test packet1"));

  // Close the session and verify responses.
  EXPECT_THAT(p4rt_session_->ReadStreamChannelResponsesAndFinish(),
              IsOkAndHolds(UnorderedElementsAre(EqualsProto(R"pb(
                packet {
                  payload: "test packet1"
                  metadata { metadata_id: 1 value: "0" }
                  metadata { metadata_id: 2 value: "0" }
                }
              )pb"))));

  sonic::PacketIoCounters counters =
      p4rt_service_.GetP4rtServer().GetPacketIoCounters();
  EXPECT_EQ(counters.packet_in_received, 1);
  EXPECT_EQ(counters.packet_in_errors, 0);
}

TEST_F(FakePacketIoTest, PacketInMessageFailsWhenNoPrimaryExists) {
  // Close the existing primary connection.
  ASSERT_OK(p4rt_session_->Finish());

  // Push a dummy PacketIn message.
  ASSERT_OK(AddPacketIoPort("Ethernet1/1/0", "0"));
  EXPECT_THAT(p4rt_service_.GetFakePacketIoInterface().PushPacketIn(
                  "Ethernet1/1/0", "Ethernet1/1/0", "test packet1"),
              StatusIs(absl::StatusCode::kFailedPrecondition,
                       HasSubstr("No active role has a primary connection")));

  sonic::PacketIoCounters counters =
      p4rt_service_.GetP4rtServer().GetPacketIoCounters();
  EXPECT_EQ(counters.packet_in_received, 0);
  EXPECT_EQ(counters.packet_in_errors, 1);
}

TEST_F(FakePacketIoTest, PacketInCanBeSentToMultiplePrimaries) {
  // p4rt_session_ is a primary client with role: "sdn_controller".
  // Use that client to push the pipeline config.
  ASSERT_OK(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      p4rt_session_.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      sai::GetP4Info(sai::Instantiation::kMiddleblock)));
  ASSERT_OK(AddPacketIoPort("Ethernet1/1/0", "0"));

  // Create a second primary client with the default role ("").
  const std::string address =
      absl::StrCat("localhost:", p4rt_service_.GrpcPort());
  ASSERT_OK_AND_ASSIGN(
      auto default_role,
      pdpi::P4RuntimeSession::Create(
          address, grpc::InsecureChannelCredentials(), device_id_,
          pdpi::P4RuntimeSessionOptionalArgs{.role = ""}));

  // Push the expected PacketIn.
  EXPECT_OK(p4rt_service_.GetFakePacketIoInterface().PushPacketIn(
      "Ethernet1/1/0", "Ethernet1/1/0", "test packet1"));

  // Close the session and verify responses.
  EXPECT_THAT(p4rt_session_->ReadStreamChannelResponsesAndFinish(),
              IsOkAndHolds(UnorderedElementsAre(EqualsProto(R"pb(
                packet {
                  payload: "test packet1"
                  metadata { metadata_id: 1 value: "0" }
                  metadata { metadata_id: 2 value: "0" }
                }
              )pb"))));
  EXPECT_THAT(default_role->ReadStreamChannelResponsesAndFinish(),
              IsOkAndHolds(UnorderedElementsAre(EqualsProto(R"pb(
                packet {
                  payload: "test packet1"
                  metadata { metadata_id: 1 value: "0" }
                  metadata { metadata_id: 2 value: "0" }
                }
              )pb"))));

  sonic::PacketIoCounters counters =
      p4rt_service_.GetP4rtServer().GetPacketIoCounters();
  EXPECT_EQ(counters.packet_in_received, 1);
  EXPECT_EQ(counters.packet_in_errors, 0);
}

TEST_F(FakePacketIoTest, PacketInMessageFailsWhenPrimaryHasNonAuthorizeRole) {
  // Close the existing primary connection.
  ASSERT_OK(p4rt_session_->Finish());

  const std::string address =
      absl::StrCat("localhost:", p4rt_service_.GrpcPort());
  ASSERT_OK_AND_ASSIGN(
      auto default_role,
      pdpi::P4RuntimeSession::Create(
          address, grpc::InsecureChannelCredentials(), device_id_,
          pdpi::P4RuntimeSessionOptionalArgs{.role = "NonAuthorized"}));

  // Push a dummy PacketIn message.
  ASSERT_OK(AddPacketIoPort("Ethernet1/1/0", "0"));
  EXPECT_THAT(p4rt_service_.GetFakePacketIoInterface().PushPacketIn(
                  "Ethernet1/1/0", "Ethernet1/1/0", "test packet1"),
              StatusIs(absl::StatusCode::kFailedPrecondition,
                       HasSubstr("No active role has a primary connection")));

  sonic::PacketIoCounters counters =
      p4rt_service_.GetP4rtServer().GetPacketIoCounters();
  EXPECT_EQ(counters.packet_in_received, 0);
  EXPECT_EQ(counters.packet_in_errors, 1);
}

TEST(PacketIoTest, PacketInMessageFailsWhenNoPrimaryIsEstablished) {
  // Start a P4Runtime service and do not establish any connection.
  test_lib::P4RuntimeGrpcService p4rt_service = test_lib::P4RuntimeGrpcService(
      P4RuntimeImplOptions{.translate_port_ids = false});

  // Push a dummy PacketIn message.
  ASSERT_OK(p4rt_service.GetP4rtServer().AddPacketIoPort("Ethernet1/1/0"));
  ASSERT_OK(
      p4rt_service.GetP4rtServer().AddPortTranslation("Ethernet1/1/0", "0"));
  EXPECT_THAT(p4rt_service.GetFakePacketIoInterface().PushPacketIn(
                  "Ethernet1/1/0", "Ethernet1/1/0", "test packet1"),
              StatusIs(absl::StatusCode::kFailedPrecondition,
                       HasSubstr("No active role has a primary connection")));

  sonic::PacketIoCounters counters =
      p4rt_service.GetP4rtServer().GetPacketIoCounters();
  EXPECT_EQ(counters.packet_in_received, 0);
  EXPECT_EQ(counters.packet_in_errors, 1);
}

}  // namespace
}  // namespace p4rt_app
