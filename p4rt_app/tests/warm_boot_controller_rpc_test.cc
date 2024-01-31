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
#include <grpcpp/support/status.h>

#include <cstdint>
#include <memory>
#include <string>
#include <utility>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "grpcpp/client_context.h"
#include "grpcpp/create_channel.h"
#include "grpcpp/security/credentials.h"
#include "grpcpp/support/status.h"
#include "grpcpp/support/sync_stream.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/tests/lib/p4runtime_grpc_service.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "swss/warm_restart.h"

namespace p4rt_app {
namespace {

using gutil::StatusIs;
using P4RuntimeStream =
    ::grpc::ClientReaderWriter<p4::v1::StreamMessageRequest,
                               p4::v1::StreamMessageResponse>;

p4::v1::Uint128 ElectionId(int value) {
  p4::v1::Uint128 election_id;
  election_id.set_high(value);
  election_id.set_low(value);
  return election_id;
}

absl::StatusOr<p4::v1::StreamMessageResponse> SendStreamRequestAndGetResponse(
    P4RuntimeStream& stream, const p4::v1::StreamMessageRequest& request) {
  if (!stream.Write(request)) {
    return gutil::InternalErrorBuilder()
           << "Stream closed : " << stream.Finish().error_message();
  }

  p4::v1::StreamMessageResponse response;
  if (!stream.Read(&response)) {
    return gutil::InternalErrorBuilder() << "Did not receive stream response: "
                                         << stream.Finish().error_message();
  }
  return response;
}

class WarmBootControllerRpcTest : public testing::Test {
 protected:
  WarmBootControllerRpcTest() {
    std::string address = absl::StrCat("localhost:", p4rt_service_.GrpcPort());

    auto primary_channel =
        grpc::CreateChannel(address, grpc::InsecureChannelCredentials());
    primary_stub_ = p4::v1::P4Runtime::NewStub(primary_channel);
    LOG(INFO) << "Created primary P4Runtime::Stub for " << address << ".";

    auto backup_channel =
        grpc::CreateChannel(address, grpc::InsecureChannelCredentials());
    backup_stub_ = p4::v1::P4Runtime::NewStub(backup_channel);
    LOG(INFO) << "Created backup P4Runtime::Stub for " << address << ".";
  }

  // Opens a P4RT stream, and verifies that it is the primary connection. Note
  // that the stream can still become a backup if a test updates the election
  // ID, or opens a new connection.
  absl::StatusOr<std::unique_ptr<P4RuntimeStream>> CreatePrimaryConnection(
      grpc::ClientContext& context, uint64_t device_id,
      const p4::v1::Uint128 election_id) {
    context.set_deadline(absl::ToChronoTime(absl::Now() + absl::Seconds(10)));
    context.set_wait_for_ready(true);
    auto stream = primary_stub_->StreamChannel(&context);

    // Verify that connection is the primary.
    p4::v1::StreamMessageRequest request;
    request.mutable_arbitration()->set_device_id(device_id);
    *request.mutable_arbitration()->mutable_election_id() = election_id;
    ASSIGN_OR_RETURN(p4::v1::StreamMessageResponse response,
                     SendStreamRequestAndGetResponse(*stream, request));
    if (response.arbitration().status().code() != grpc::StatusCode::OK) {
      return gutil::UnknownErrorBuilder()
             << "could not become primary. "
             << response.arbitration().status().ShortDebugString();
    }

    return stream;
  }

  // Opens a P4RT stream without an election ID so it is forced to be a backup.
  absl::StatusOr<std::unique_ptr<P4RuntimeStream>> CreateBackupConnection(
      grpc::ClientContext& context, uint64_t device_id) {
    // No test should take more than 10 seconds.
    context.set_deadline(absl::ToChronoTime(absl::Now() + absl::Seconds(10)));
    context.set_wait_for_ready(true);
    auto stream = backup_stub_->StreamChannel(&context);

    // Verify that connection is a backup.
    p4::v1::StreamMessageRequest request;
    request.mutable_arbitration()->set_device_id(device_id);
    ASSIGN_OR_RETURN(p4::v1::StreamMessageResponse response,
                     SendStreamRequestAndGetResponse(*stream, request));
    if (response.arbitration().status().code() == grpc::StatusCode::OK) {
      return gutil::UnknownErrorBuilder()
             << "could not become backup. "
             << response.arbitration().status().ShortDebugString();
    }

    return stream;
  }

  test_lib::P4RuntimeGrpcService p4rt_service_ =
      test_lib::P4RuntimeGrpcService(P4RuntimeImplOptions{});
  std::unique_ptr<p4::v1::P4Runtime::Stub> primary_stub_;
  std::unique_ptr<p4::v1::P4Runtime::Stub> backup_stub_;
  std::unique_ptr<pdpi::P4RuntimeSession> p4rt_session_;
};

TEST_F(WarmBootControllerRpcTest, WriteRpcReceivesUnavailableAfterFreeze) {
  const uint64_t device_id = 11223344;
  ASSERT_OK(p4rt_service_.GetP4rtServer().UpdateDeviceId(device_id));

  ASSERT_OK_AND_ASSIGN(p4rt_session_, pdpi::P4RuntimeSession::Create(
                                          std::move(primary_stub_), device_id));

  EXPECT_OK(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      p4rt_session_.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      sai::GetP4Info(sai::Instantiation::kMiddleblock)));

  p4::v1::WriteRequest write_request;
  write_request.set_device_id(p4rt_session_->DeviceId());
  write_request.set_role(p4rt_session_->Role());
  *write_request.mutable_election_id() = p4rt_session_->ElectionId();

  EXPECT_OK(p4rt_session_->Write(write_request));

  // Send freeze notification.
  ASSERT_OK(p4rt_service_.GetP4rtServer().HandleWarmBootNotification(
      swss::WarmStart::WarmBootNotification::kFreeze));
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  EXPECT_THAT(p4rt_session_->Write(write_request),
              StatusIs(absl::StatusCode::kUnavailable,
                       "P4RT is performing warm reboot."));

  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  // Set warm boot state as FAILED.
  p4rt_service_.GetWarmBootStateAdapter()->SetWarmBootState(
      swss::WarmStart::WarmStartState::FAILED);
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::FAILED);

  EXPECT_THAT(p4rt_session_->Write(write_request),
              StatusIs(absl::StatusCode::kUnavailable,
                       "P4RT is performing warm reboot."));

  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::FAILED);
}

TEST_F(WarmBootControllerRpcTest, ReadRpcReceivesUnavailableAfterFreeze) {
  const uint64_t device_id = 11223344;
  ASSERT_OK(p4rt_service_.GetP4rtServer().UpdateDeviceId(device_id));

  ASSERT_OK_AND_ASSIGN(p4rt_session_, pdpi::P4RuntimeSession::Create(
                                          std::move(primary_stub_), device_id));

  EXPECT_OK(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      p4rt_session_.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      sai::GetP4Info(sai::Instantiation::kMiddleblock)));

  p4::v1::ReadRequest read_request;
  read_request.set_device_id(device_id);
  read_request.set_role(p4rt_session_->Role());
  p4::v1::ReadResponse read_response;

  EXPECT_OK(p4rt_session_->Read(read_request));

  // Send freeze notification.
  ASSERT_OK(p4rt_service_.GetP4rtServer().HandleWarmBootNotification(
      swss::WarmStart::WarmBootNotification::kFreeze));
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  EXPECT_THAT(p4rt_session_->Read(read_request),
              StatusIs(absl::StatusCode::kUnavailable,
                       "P4RT is performing warm reboot."));

  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  // Set warm boot state as FAILED.
  p4rt_service_.GetWarmBootStateAdapter()->SetWarmBootState(
      swss::WarmStart::WarmStartState::FAILED);
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::FAILED);

  EXPECT_THAT(p4rt_session_->Read(read_request),
              StatusIs(absl::StatusCode::kUnavailable,
                       "P4RT is performing warm reboot."));

  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::FAILED);
}

TEST_F(WarmBootControllerRpcTest,
       GetForwardingPipelineConfigRpcReceivesUnavailableAfterFreeze) {
  const uint64_t device_id = 11223344;
  ASSERT_OK(p4rt_service_.GetP4rtServer().UpdateDeviceId(device_id));

  ASSERT_OK_AND_ASSIGN(p4rt_session_, pdpi::P4RuntimeSession::Create(
                                          std::move(primary_stub_), device_id));

  EXPECT_OK(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      p4rt_session_.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      sai::GetP4Info(sai::Instantiation::kMiddleblock)));

  p4::v1::GetForwardingPipelineConfigRequest
      get_forwarding_pipeline_config_request;
  get_forwarding_pipeline_config_request.set_device_id(device_id);

  EXPECT_OK(p4rt_session_->GetForwardingPipelineConfig(
      get_forwarding_pipeline_config_request));

  // Send freeze notification.
  ASSERT_OK(p4rt_service_.GetP4rtServer().HandleWarmBootNotification(
      swss::WarmStart::WarmBootNotification::kFreeze));
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  EXPECT_THAT(p4rt_session_->GetForwardingPipelineConfig(
                  get_forwarding_pipeline_config_request),
              StatusIs(absl::StatusCode::kUnavailable,
                       "P4RT is performing warm reboot."));

  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  // Set warm boot state as FAILED.
  p4rt_service_.GetWarmBootStateAdapter()->SetWarmBootState(
      swss::WarmStart::WarmStartState::FAILED);
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::FAILED);

  EXPECT_THAT(p4rt_session_->GetForwardingPipelineConfig(
                  get_forwarding_pipeline_config_request),
              StatusIs(absl::StatusCode::kUnavailable,
                       "P4RT is performing warm reboot."));

  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::FAILED);
}

TEST_F(WarmBootControllerRpcTest,
       SetForwardingPipelineConfigRpcReceivesUnavailableAfterFreeze) {
  const uint64_t device_id = 11223344;
  ASSERT_OK(p4rt_service_.GetP4rtServer().UpdateDeviceId(device_id));

  ASSERT_OK_AND_ASSIGN(p4rt_session_, pdpi::P4RuntimeSession::Create(
                                          std::move(primary_stub_), device_id));

  EXPECT_OK(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      p4rt_session_.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      sai::GetP4Info(sai::Instantiation::kMiddleblock)));

  // Send freeze notification.
  ASSERT_OK(p4rt_service_.GetP4rtServer().HandleWarmBootNotification(
      swss::WarmStart::WarmBootNotification::kFreeze));
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  EXPECT_THAT(
      pdpi::SetMetadataAndSetForwardingPipelineConfig(
          p4rt_session_.get(),
          p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
          sai::GetP4Info(sai::Instantiation::kMiddleblock)),
      StatusIs(absl::StatusCode::kUnavailable,
               "P4RT is performing warm reboot."));

  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  // Set warm boot state as FAILED.
  p4rt_service_.GetWarmBootStateAdapter()->SetWarmBootState(
      swss::WarmStart::WarmStartState::FAILED);
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::FAILED);

  EXPECT_THAT(
      pdpi::SetMetadataAndSetForwardingPipelineConfig(
          p4rt_session_.get(),
          p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
          sai::GetP4Info(sai::Instantiation::kMiddleblock)),
      StatusIs(absl::StatusCode::kUnavailable,
               "P4RT is performing warm reboot."));

  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::FAILED);
}

TEST_F(WarmBootControllerRpcTest,
       MultipleStreamTerminateAndRpcFailAfterFreeze) {
  const uint64_t device_id = 11223344;
  const p4::v1::Uint128 election_id = ElectionId(11);

  grpc::ClientContext primary_stream_context;
  std::unique_ptr<P4RuntimeStream> primary_stream;
  grpc::ClientContext backup_stream_context;
  std::unique_ptr<P4RuntimeStream> backup_stream;
  ASSERT_OK(p4rt_service_.GetP4rtServer().UpdateDeviceId(device_id));

  p4::v1::StreamMessageRequest request;
  p4::v1::StreamMessageResponse response;
  request.mutable_arbitration()->set_device_id(device_id);
  *request.mutable_arbitration()->mutable_election_id() = election_id;

  ASSERT_OK_AND_ASSIGN(
      primary_stream,
      CreatePrimaryConnection(primary_stream_context, device_id, election_id));
  ASSERT_OK_AND_ASSIGN(
      backup_stream, CreateBackupConnection(backup_stream_context, device_id));

  // Send freeze notification.
  ASSERT_OK(p4rt_service_.GetP4rtServer().HandleWarmBootNotification(
      swss::WarmStart::WarmBootNotification::kFreeze));
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  // Wait for the freeze request to be processed..
  absl::SleepFor(absl::Seconds(1));

  // After freeze client write request will fail.
  EXPECT_FALSE(primary_stream->Write(request));
  // Server will send warm boot error message.
  EXPECT_TRUE(primary_stream->Read(&response));
  EXPECT_EQ(response.mutable_error()->canonical_code(),
            grpc::StatusCode::UNAVAILABLE);
  EXPECT_EQ(response.mutable_error()->message(),
            "P4RT is performing warm reboot.");
  // Future write/read requests will fail.
  EXPECT_FALSE(primary_stream->Write(request));
  EXPECT_FALSE(primary_stream->Read(&response));
  // Verify that the stream was terminated.
  EXPECT_EQ(primary_stream->Finish().error_code(), grpc::StatusCode::CANCELLED);

  // The same for backup stream, after freeze client write request will fail.
  EXPECT_FALSE(backup_stream->Write(request));
  // Server will send warm boot error message.
  EXPECT_TRUE(backup_stream->Read(&response));
  EXPECT_EQ(response.mutable_error()->canonical_code(),
            grpc::StatusCode::UNAVAILABLE);
  EXPECT_EQ(response.mutable_error()->message(),
            "P4RT is performing warm reboot.");
  // Future write/read requests will fail.
  EXPECT_FALSE(backup_stream->Write(request));
  EXPECT_FALSE(backup_stream->Read(&response));
  // Verify that the stream was terminated.
  EXPECT_EQ(backup_stream->Finish().error_code(), grpc::StatusCode::CANCELLED);

  // Verify that the warm boot state is still QUIESCENT.
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);
}

TEST_F(WarmBootControllerRpcTest, NewStreamReceivesUnavailableAfterFreeze) {
  const uint64_t device_id = 11223344;
  const p4::v1::Uint128 election_id = ElectionId(11);

  // Send freeze notification.
  ASSERT_OK(p4rt_service_.GetP4rtServer().HandleWarmBootNotification(
      swss::WarmStart::WarmBootNotification::kFreeze));
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  // Try to open a new primary connection.
  std::unique_ptr<grpc::ClientContext> context =
      std::make_unique<grpc::ClientContext>();
  context->set_deadline(absl::ToChronoTime(absl::Now() + absl::Seconds(10)));
  context->set_wait_for_ready(true);
  auto primary_stream = primary_stub_->StreamChannel(context.get());

  p4::v1::StreamMessageRequest primary_request;
  primary_request.mutable_arbitration()->set_device_id(device_id);
  *primary_request.mutable_arbitration()->mutable_election_id() = election_id;
  primary_stream->Write(primary_request);

  p4::v1::StreamMessageResponse response;
  ASSERT_FALSE(primary_stream->Read(&response));

  EXPECT_EQ(primary_stream->Finish().error_code(),
            grpc::StatusCode::UNAVAILABLE);

  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  // Try to open a new backup connection.

  context = std::make_unique<grpc::ClientContext>();
  context->set_deadline(absl::ToChronoTime(absl::Now() + absl::Seconds(10)));
  context->set_wait_for_ready(true);
  auto backup_stream = backup_stub_->StreamChannel(context.get());

  p4::v1::StreamMessageRequest backup_request;
  backup_request.mutable_arbitration()->set_device_id(device_id);
  backup_stream->Write(backup_request);

  ASSERT_FALSE(backup_stream->Read(&response));

  EXPECT_EQ(backup_stream->Finish().error_code(),
            grpc::StatusCode::UNAVAILABLE);

  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  // Set warm boot state as FAILED.
  p4rt_service_.GetWarmBootStateAdapter()->SetWarmBootState(
      swss::WarmStart::WarmStartState::FAILED);
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::FAILED);

  // Try to open a new primary connection.
  context = std::make_unique<grpc::ClientContext>();
  context->set_deadline(absl::ToChronoTime(absl::Now() + absl::Seconds(10)));
  context->set_wait_for_ready(true);
  primary_stream = primary_stub_->StreamChannel(context.get());

  primary_stream->Write(primary_request);

  ASSERT_FALSE(primary_stream->Read(&response));

  EXPECT_EQ(primary_stream->Finish().error_code(),
            grpc::StatusCode::UNAVAILABLE);

  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::FAILED);

  // Try to open a new backup connection.
  context = std::make_unique<grpc::ClientContext>();
  context->set_deadline(absl::ToChronoTime(absl::Now() + absl::Seconds(10)));
  context->set_wait_for_ready(true);
  backup_stream = backup_stub_->StreamChannel(context.get());

  backup_stream->Write(backup_request);

  ASSERT_FALSE(backup_stream->Read(&response));

  EXPECT_EQ(backup_stream->Finish().error_code(),
            grpc::StatusCode::UNAVAILABLE);

  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::FAILED);
}

}  // namespace
}  // namespace p4rt_app
