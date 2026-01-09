// Copyright 2022 Google LLC
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

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "grpcpp/client_context.h"
#include "grpcpp/support/sync_stream.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/tests/lib/p4runtime_grpc_service.h"

namespace p4rt_app {
namespace {

using P4RuntimeStream =
    ::grpc::ClientReaderWriter<p4::v1::StreamMessageRequest,
                               p4::v1::StreamMessageResponse>;

p4::v1::Uint128 ElectionId(int value) {
  p4::v1::Uint128 election_id;
  election_id.set_high(value);
  election_id.set_low(0);
  return election_id;
}

absl::StatusOr<p4::v1::StreamMessageResponse> SendStreamRequestAndGetResponse(
    P4RuntimeStream& stream, const p4::v1::StreamMessageRequest& request) {
  stream.Write(request);

  p4::v1::StreamMessageResponse response;
  if (!stream.Read(&response)) {
    return gutil::InternalErrorBuilder() << "Did not receive stream response: "
                                         << stream.Finish().error_message();
  }
  return response;
}

// Verifies behavior around who can access the P4Runtime APIs. For example:
//   * only the primary can call Write()
//   * backup connections can call Read()
//   * device ID must match, or election ID can be ignored, etc.
class ApiAccessTest : public testing::Test {
 protected:
  ApiAccessTest() {
    std::string address = absl::StrCat("localhost:", p4rt_service_.GrpcPort());
    auto channel =
        grpc::CreateChannel(address, grpc::InsecureChannelCredentials());
    stub_ = p4::v1::P4Runtime::NewStub(channel);
    LOG(INFO) << "Created P4Runtime::Stub for " << address << ".";
  }

  // Opens a P4RT stream, and verifies that it is the primary connection. Note
  // that the stream can still become a backup if a test updates the election
  // ID, or opens a new connection.
  absl::StatusOr<std::unique_ptr<P4RuntimeStream>> GetPrimaryConnection(
      grpc::ClientContext& context, uint64_t device_id,
      const p4::v1::Uint128 election_id) {
    // No test should take more than 10 seconds.
    context.set_deadline(absl::ToChronoTime(absl::Now() + absl::Seconds(10)));
    context.set_wait_for_ready(true);
    auto stream = stub_->StreamChannel(&context);

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
  absl::StatusOr<std::unique_ptr<P4RuntimeStream>> GetBackupConnection(
      grpc::ClientContext& context, uint64_t device_id) {
    // No test should take more than 10 seconds.
    context.set_deadline(absl::ToChronoTime(absl::Now() + absl::Seconds(10)));
    context.set_wait_for_ready(true);
    auto stream = stub_->StreamChannel(&context);

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
  std::unique_ptr<p4::v1::P4Runtime::Stub> stub_;
};

using WriteApiAccessTest = ApiAccessTest;

TEST_F(WriteApiAccessTest, ReturnsNotFoundIfRequestDoesNotSetDeviceId) {
  const uint64_t device_id = 11223344;
  const p4::v1::Uint128 election_id = ElectionId(11);

  p4::v1::WriteRequest request;
  *request.mutable_election_id() = election_id;

  grpc::ClientContext stream_context;
  ASSERT_OK(p4rt_service_.GetP4rtServer().UpdateDeviceId(device_id));
  ASSERT_OK_AND_ASSIGN(
      auto stream,
      GetPrimaryConnection(stream_context, device_id, election_id));

  grpc::ClientContext write_context;
  p4::v1::WriteResponse response;
  EXPECT_EQ(stub_->Write(&write_context, request, &response).error_code(),
            grpc::StatusCode::NOT_FOUND);
}

TEST_F(WriteApiAccessTest,
       ReturnsNotFoundIfSwitchHasNotBeenConfiguredWithADeviceId) {
  const uint64_t device_id = 11223344;
  const p4::v1::Uint128 election_id = ElectionId(11);

  p4::v1::WriteRequest request;
  request.set_device_id(device_id);
  *request.mutable_election_id() = election_id;

  // Do not try to become primary. The switch doesn't have a device ID, and will
  // simply close the stream.
  grpc::ClientContext write_context;
  p4::v1::WriteResponse response;
  EXPECT_EQ(stub_->Write(&write_context, request, &response).error_code(),
            grpc::StatusCode::NOT_FOUND);
}

TEST_F(WriteApiAccessTest, ReturnsPermissionDeniedForBackupConnections) {
  const uint64_t device_id = 11223344;

  p4::v1::WriteRequest request;
  request.set_device_id(device_id);

  grpc::ClientContext stream_context;
  ASSERT_OK(p4rt_service_.GetP4rtServer().UpdateDeviceId(device_id));
  ASSERT_OK_AND_ASSIGN(auto stream,
                       GetBackupConnection(stream_context, device_id));

  grpc::ClientContext write_context;
  p4::v1::WriteResponse response;
  EXPECT_EQ(stub_->Write(&write_context, request, &response).error_code(),
            grpc::StatusCode::PERMISSION_DENIED);
}

TEST_F(WriteApiAccessTest, ReturnsPermissionDeniedWithNoActiveConnections) {
  const uint64_t device_id = 11223344;
  const p4::v1::Uint128 election_id = ElectionId(11);

  p4::v1::WriteRequest request;
  request.set_device_id(device_id);
  *request.mutable_election_id() = election_id;

  ASSERT_OK(p4rt_service_.GetP4rtServer().UpdateDeviceId(device_id));

  grpc::ClientContext write_context;
  p4::v1::WriteResponse response;
  EXPECT_EQ(stub_->Write(&write_context, request, &response).error_code(),
            grpc::StatusCode::PERMISSION_DENIED);
}

TEST_F(WriteApiAccessTest, ReturnsFailedPreconditionefP4InfoHasNotBeenPushed) {
  const uint64_t device_id = 11223344;
  const p4::v1::Uint128 election_id = ElectionId(11);

  p4::v1::WriteRequest request;
  request.set_device_id(device_id);
  *request.mutable_election_id() = election_id;

  grpc::ClientContext stream_context;
  ASSERT_OK(p4rt_service_.GetP4rtServer().UpdateDeviceId(device_id));
  ASSERT_OK_AND_ASSIGN(
      auto stream,
      GetPrimaryConnection(stream_context, device_id, election_id));

  grpc::ClientContext write_context;
  p4::v1::WriteResponse response;
  EXPECT_EQ(stub_->Write(&write_context, request, &response).error_code(),
            grpc::StatusCode::FAILED_PRECONDITION);
}

using ReadApiAccessTest = ApiAccessTest;

// Read path should not check the election ID so we don't set it. Read also does
// not require an active connection so we don't do arbitration.
TEST_F(ReadApiAccessTest, ReturnsNotFoundIfRequestDoesNotSetDeviceId) {
  const uint64_t device_id = 11223344;
  ASSERT_OK(p4rt_service_.GetP4rtServer().UpdateDeviceId(device_id));

  p4::v1::ReadRequest request;

  grpc::ClientContext read_context;
  auto responses = stub_->Read(&read_context, request);
  ASSERT_NE(responses, nullptr);
  EXPECT_EQ(responses->Finish().error_code(), grpc::StatusCode::NOT_FOUND);
}

// Read path should not check the election ID so we don't set it. Read also does
// not require an active connection so we don't do arbitration.
TEST_F(ReadApiAccessTest,
       ReturnsNotFoundIfSwitchHasNotBeenConfiguredWithADeviceId) {
  const uint64_t device_id = 11223344;

  p4::v1::ReadRequest request;
  request.set_device_id(device_id);

  grpc::ClientContext read_context;
  auto responses = stub_->Read(&read_context, request);
  ASSERT_NE(responses, nullptr);
  EXPECT_EQ(responses->Finish().error_code(), grpc::StatusCode::NOT_FOUND);
}

// Read path should not check the election ID so we don't set it. Read also does
// not require an active connection so we don't do arbitration.
TEST_F(ReadApiAccessTest, ReturnsFailedPreconditionefP4InfoHasNotBeenPushed) {
  const uint64_t device_id = 11223344;
  ASSERT_OK(p4rt_service_.GetP4rtServer().UpdateDeviceId(device_id));

  p4::v1::ReadRequest request;
  request.set_device_id(device_id);

  grpc::ClientContext read_context;
  auto responses = stub_->Read(&read_context, request);
  ASSERT_NE(responses, nullptr);
  EXPECT_EQ(responses->Finish().error_code(),
            grpc::StatusCode::FAILED_PRECONDITION);
}

using SetForwardingPipelineApiAccessTest = ApiAccessTest;

TEST_F(SetForwardingPipelineApiAccessTest,
       ReturnsNotFoundIfRequestDoesNotSetDeviceId) {
  const uint64_t device_id = 11223344;
  const p4::v1::Uint128 election_id = ElectionId(11);

  p4::v1::SetForwardingPipelineConfigRequest request;
  *request.mutable_election_id() = election_id;

  grpc::ClientContext stream_context;
  ASSERT_OK(p4rt_service_.GetP4rtServer().UpdateDeviceId(device_id));
  ASSERT_OK_AND_ASSIGN(
      auto stream,
      GetPrimaryConnection(stream_context, device_id, election_id));

  grpc::ClientContext set_context;
  p4::v1::SetForwardingPipelineConfigResponse response;
  EXPECT_EQ(stub_->SetForwardingPipelineConfig(&set_context, request, &response)
                .error_code(),
            grpc::StatusCode::NOT_FOUND);
}

TEST_F(SetForwardingPipelineApiAccessTest,
       ReturnsNotFoundIfSwitchHasNotBeenConfiguredWithADeviceId) {
  const uint64_t device_id = 11223344;
  const p4::v1::Uint128 election_id = ElectionId(11);

  p4::v1::SetForwardingPipelineConfigRequest request;
  request.set_device_id(device_id);
  *request.mutable_election_id() = election_id;

  // Do not try to become primary. The switch doesn't have a device ID, and will
  // simply close the stream.
  grpc::ClientContext set_context;
  p4::v1::SetForwardingPipelineConfigResponse response;
  EXPECT_EQ(stub_->SetForwardingPipelineConfig(&set_context, request, &response)
                .error_code(),
            grpc::StatusCode::NOT_FOUND);
}

TEST_F(SetForwardingPipelineApiAccessTest,
       ReturnsPermissionDeniedForBackupConnections) {
  const uint64_t device_id = 11223344;

  p4::v1::SetForwardingPipelineConfigRequest request;
  request.set_device_id(device_id);

  grpc::ClientContext stream_context;
  ASSERT_OK(p4rt_service_.GetP4rtServer().UpdateDeviceId(device_id));
  ASSERT_OK_AND_ASSIGN(auto stream,
                       GetBackupConnection(stream_context, device_id));

  grpc::ClientContext set_context;
  p4::v1::SetForwardingPipelineConfigResponse response;
  EXPECT_EQ(stub_->SetForwardingPipelineConfig(&set_context, request, &response)
                .error_code(),
            grpc::StatusCode::PERMISSION_DENIED);
}

TEST_F(SetForwardingPipelineApiAccessTest,
       ReturnsPermissionDeniedWithNoActiveConnections) {
  const uint64_t device_id = 11223344;
  const p4::v1::Uint128 election_id = ElectionId(11);

  p4::v1::SetForwardingPipelineConfigRequest request;
  request.set_device_id(device_id);
  *request.mutable_election_id() = election_id;

  ASSERT_OK(p4rt_service_.GetP4rtServer().UpdateDeviceId(device_id));

  grpc::ClientContext set_context;
  p4::v1::SetForwardingPipelineConfigResponse response;
  EXPECT_EQ(stub_->SetForwardingPipelineConfig(&set_context, request, &response)
                .error_code(),
            grpc::StatusCode::PERMISSION_DENIED);
}

using GetForwardingPipelineConfigApiAccessTest = ApiAccessTest;

TEST_F(GetForwardingPipelineConfigApiAccessTest,
       ReturnsNotFoundIfRequestDoesNotSetDeviceId) {
  const uint64_t device_id = 11223344;
  ASSERT_OK(p4rt_service_.GetP4rtServer().UpdateDeviceId(device_id));

  p4::v1::GetForwardingPipelineConfigRequest request;

  grpc::ClientContext get_context;
  p4::v1::GetForwardingPipelineConfigResponse response;
  EXPECT_EQ(stub_->GetForwardingPipelineConfig(&get_context, request, &response)
                .error_code(),
            grpc::StatusCode::NOT_FOUND);
}

TEST_F(GetForwardingPipelineConfigApiAccessTest,
       ReturnsNotFoundIfSwitchHasNotBeenConfiguredWithADeviceId) {
  const uint64_t device_id = 11223344;

  p4::v1::GetForwardingPipelineConfigRequest request;
  request.set_device_id(device_id);

  grpc::ClientContext get_context;
  p4::v1::GetForwardingPipelineConfigResponse response;
  EXPECT_EQ(stub_->GetForwardingPipelineConfig(&get_context, request, &response)
                .error_code(),
            grpc::StatusCode::NOT_FOUND);
}

TEST_F(GetForwardingPipelineConfigApiAccessTest,
       ReturnsEmptyResponseIfP4InfoHasNotBeenPushed) {
  const uint64_t device_id = 11223344;
  ASSERT_OK(p4rt_service_.GetP4rtServer().UpdateDeviceId(device_id));

  p4::v1::GetForwardingPipelineConfigRequest request;
  request.set_device_id(device_id);

  grpc::ClientContext get_context;
  p4::v1::GetForwardingPipelineConfigResponse response;
  EXPECT_EQ(stub_->GetForwardingPipelineConfig(&get_context, request, &response)
                .error_code(),
            grpc::StatusCode::OK);
  EXPECT_FALSE(response.has_config());
}

}  // namespace
}  // namespace p4rt_app
