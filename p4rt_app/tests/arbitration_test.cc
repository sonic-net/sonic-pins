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
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "google/rpc/status.pb.h"
#include "grpcpp/client_context.h"
#include "grpcpp/create_channel.h"
#include "grpcpp/security/credentials.h"
#include "grpcpp/support/status.h"
#include "grpcpp/support/sync_stream.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4rt_app/tests/lib/p4runtime_grpc_service.h"

namespace p4rt_app {
namespace {

using ::gutil::StatusIs;

using P4RuntimeStream =
    ::grpc::ClientReaderWriter<p4::v1::StreamMessageRequest,
                               p4::v1::StreamMessageResponse>;

p4::v1::Uint128 GetElectionId(int value) {
  p4::v1::Uint128 election_id;
  election_id.set_high(value);
  election_id.set_low(0);
  return election_id;
}

absl::StatusOr<p4::v1::StreamMessageResponse> GetStreamResponse(
    P4RuntimeStream& stream) {
  p4::v1::StreamMessageResponse response;
  if (!stream.Read(&response)) {
    return gutil::InternalErrorBuilder() << "Did not receive stream response: "
                                         << stream.Finish().error_message();
  }
  return response;
}

absl::StatusOr<p4::v1::StreamMessageResponse> SendStreamRequest(
    P4RuntimeStream& stream, const p4::v1::StreamMessageRequest& request) {
  stream.Write(request);
  return GetStreamResponse(stream);
}

class ArbitrationTest : public testing::Test {
 protected:
  void SetUp() override {
    std::string address = absl::StrCat("localhost:", p4rt_service_.GrpcPort());
    auto channel =
        grpc::CreateChannel(address, grpc::InsecureChannelCredentials());
    LOG(INFO) << "Creating P4Runtime::Stub for " << address << ".";
    stub_ = p4::v1::P4Runtime::NewStub(channel);
  }

  int GetDeviceId() const { return 183807201; }

  test_lib::P4RuntimeGrpcService p4rt_service_ =
      test_lib::P4RuntimeGrpcService(test_lib::P4RuntimeGrpcServiceOptions{});
  std::unique_ptr<p4::v1::P4Runtime::Stub> stub_;
};

// TODO: arbitration should fail with invalid device id.
TEST_F(ArbitrationTest, DISABLED_DeviceIdMustMatch) {
  grpc::ClientContext context;
  std::unique_ptr<P4RuntimeStream> stream = stub_->StreamChannel(&context);

  p4::v1::StreamMessageResponse response;
  p4::v1::StreamMessageRequest request;
  request.mutable_arbitration()->set_device_id(GetDeviceId() + 1);
  request.mutable_arbitration()->mutable_election_id()->set_high(2);
  stream->Write(request);
  EXPECT_EQ(stream->Finish().error_code(), grpc::StatusCode::NOT_FOUND);
}

// TODO: arbitration should fail with invalid device id.
TEST_F(ArbitrationTest, DISABLED_DeviceIdCannotChange) {
  grpc::ClientContext context;
  std::unique_ptr<P4RuntimeStream> stream = stub_->StreamChannel(&context);

  p4::v1::StreamMessageResponse response;
  p4::v1::StreamMessageRequest request;
  request.mutable_arbitration()->set_device_id(GetDeviceId());
  request.mutable_arbitration()->mutable_election_id()->set_high(2);
  ASSERT_OK_AND_ASSIGN(response, SendStreamRequest(*stream, request));
  ASSERT_EQ(response.arbitration().status().code(), grpc::StatusCode::OK);

  request.mutable_arbitration()->set_device_id(GetDeviceId() + 1);
  stream->Write(request);
  EXPECT_EQ(stream->Finish().error_code(),
            grpc::StatusCode::FAILED_PRECONDITION);
}

TEST_F(ArbitrationTest, PrimaryConnectionWithElectionId) {
  grpc::ClientContext context;
  std::unique_ptr<P4RuntimeStream> stream = stub_->StreamChannel(&context);

  // Send only 1 arbitration request.
  p4::v1::StreamMessageRequest request;
  request.mutable_arbitration()->set_device_id(GetDeviceId());
  *request.mutable_arbitration()->mutable_election_id() = GetElectionId(1);
  ASSERT_OK_AND_ASSIGN(p4::v1::StreamMessageResponse response,
                       SendStreamRequest(*stream, request));

  // Because only 1 request was sent it should be the primary connection.
  EXPECT_EQ(response.arbitration().status().code(), grpc::StatusCode::OK);
}

TEST_F(ArbitrationTest, PrimaryConnectionWithElectionIdZero) {
  grpc::ClientContext context;
  std::unique_ptr<P4RuntimeStream> stream = stub_->StreamChannel(&context);

  p4::v1::StreamMessageRequest request;
  request.mutable_arbitration()->set_device_id(GetDeviceId());
  request.mutable_arbitration()->mutable_election_id()->set_high(0);
  ASSERT_OK_AND_ASSIGN(p4::v1::StreamMessageResponse response,
                       SendStreamRequest(*stream, request));
  EXPECT_EQ(response.arbitration().status().code(), grpc::StatusCode::OK);
}

TEST_F(ArbitrationTest, NoElectionIdIsAlwaysBackupConnection) {
  grpc::ClientContext context;
  std::unique_ptr<P4RuntimeStream> stream = stub_->StreamChannel(&context);

  p4::v1::StreamMessageRequest request;
  request.mutable_arbitration()->set_device_id(GetDeviceId());
  ASSERT_OK_AND_ASSIGN(p4::v1::StreamMessageResponse response,
                       SendStreamRequest(*stream, request));
  EXPECT_EQ(response.arbitration().status().code(),
            grpc::StatusCode::NOT_FOUND);
}

TEST_F(ArbitrationTest, PrimaryAndBackupConnections) {
  grpc::ClientContext context0;
  std::unique_ptr<P4RuntimeStream> stream0 = stub_->StreamChannel(&context0);

  grpc::ClientContext context1;
  std::unique_ptr<P4RuntimeStream> stream1 = stub_->StreamChannel(&context1);

  // Send first arbitration request.
  p4::v1::StreamMessageRequest request0;
  request0.mutable_arbitration()->set_device_id(GetDeviceId());
  *request0.mutable_arbitration()->mutable_election_id() = GetElectionId(2);
  ASSERT_OK_AND_ASSIGN(p4::v1::StreamMessageResponse response,
                       SendStreamRequest(*stream0, request0));

  // Because it's the first request it will default to the primary connection.
  EXPECT_EQ(response.arbitration().status().code(), grpc::StatusCode::OK);

  // Send second arbitration request with a lower election ID.
  p4::v1::StreamMessageRequest request1;
  request1.mutable_arbitration()->set_device_id(GetDeviceId());
  *request1.mutable_arbitration()->mutable_election_id() = GetElectionId(1);
  ASSERT_OK_AND_ASSIGN(response, SendStreamRequest(*stream1, request1));

  // Because the election ID is lower than the first this becomes the backup
  // connection. Because there is a new primary connection we expect the
  // existing connections to receive an ALREADY_EXISTS response.
  EXPECT_EQ(response.arbitration().status().code(),
            grpc::StatusCode::ALREADY_EXISTS);
}

TEST_F(ArbitrationTest, NotifyAllConnectionsForNewPrimary) {
  grpc::ClientContext context0;
  std::unique_ptr<P4RuntimeStream> stream0 = stub_->StreamChannel(&context0);

  grpc::ClientContext context1;
  std::unique_ptr<P4RuntimeStream> stream1 = stub_->StreamChannel(&context1);

  // Send first arbitration request.
  p4::v1::StreamMessageRequest request0;
  request0.mutable_arbitration()->set_device_id(GetDeviceId());
  *request0.mutable_arbitration()->mutable_election_id() = GetElectionId(2);
  ASSERT_OK_AND_ASSIGN(p4::v1::StreamMessageResponse response,
                       SendStreamRequest(*stream0, request0));

  // Because it's the first request it will default to the primary connection.
  EXPECT_EQ(response.arbitration().status().code(), grpc::StatusCode::OK);

  // Send second arbitration request with a higher election ID.
  p4::v1::StreamMessageRequest request1;
  request1.mutable_arbitration()->set_device_id(GetDeviceId());
  *request1.mutable_arbitration()->mutable_election_id() = GetElectionId(3);
  ASSERT_OK_AND_ASSIGN(response, SendStreamRequest(*stream1, request1));

  // Because the election ID is higher than the first this becomes the new
  // primary connection.
  EXPECT_EQ(response.arbitration().status().code(), grpc::StatusCode::OK);

  // Because the primary connection changed we expect all connections to be
  // informed. Because there is a new primary connection we expect the existing
  // connections to receive an ALREADY_EXISTS response.
  ASSERT_OK_AND_ASSIGN(response, GetStreamResponse(*stream0));
  EXPECT_EQ(response.arbitration().status().code(),
            grpc::StatusCode::ALREADY_EXISTS);
}

TEST_F(ArbitrationTest, NotifyAllConnectionsWhenPrimaryDisconnects) {
  grpc::ClientContext context0;
  std::unique_ptr<P4RuntimeStream> stream0 = stub_->StreamChannel(&context0);

  grpc::ClientContext context1;
  std::unique_ptr<P4RuntimeStream> stream1 = stub_->StreamChannel(&context1);

  // Send first arbitration request, and because it's the first request it will
  // default to the primary connection.
  p4::v1::StreamMessageRequest request0;
  request0.mutable_arbitration()->set_device_id(GetDeviceId());
  *request0.mutable_arbitration()->mutable_election_id() = GetElectionId(2);
  ASSERT_OK_AND_ASSIGN(p4::v1::StreamMessageResponse response,
                       SendStreamRequest(*stream0, request0));
  EXPECT_EQ(response.arbitration().status().code(), grpc::StatusCode::OK);

  // Send second arbitration request with a lower election ID. Because the
  // election ID is lower than the first it becomes a backup connection.
  p4::v1::StreamMessageRequest request1;
  request1.mutable_arbitration()->set_device_id(GetDeviceId());
  *request1.mutable_arbitration()->mutable_election_id() = GetElectionId(1);
  ASSERT_OK_AND_ASSIGN(response, SendStreamRequest(*stream1, request1));
  EXPECT_NE(response.arbitration().status().code(), grpc::StatusCode::OK);

  // Close the primary stream to flush the connection for the P4RT service.
  stream0->WritesDone();
  EXPECT_OK(stream0->Finish());

  // Because the primary connection changed we expect all connections to be
  // informed. Because there is no longer an active primary connection we epxect
  // the existing connections to receive a NOT_FOUND response.
  ASSERT_OK_AND_ASSIGN(response, GetStreamResponse(*stream1));
  EXPECT_EQ(response.arbitration().status().code(),
            grpc::StatusCode::NOT_FOUND);
}

TEST_F(ArbitrationTest, NofityAllConnectionsIfPrimaryIncreasesItsElectionId) {
  grpc::ClientContext context0;
  std::unique_ptr<P4RuntimeStream> stream0 = stub_->StreamChannel(&context0);

  grpc::ClientContext context1;
  std::unique_ptr<P4RuntimeStream> stream1 = stub_->StreamChannel(&context1);

  // Send first arbitration request, and because it's the first request it will
  // default to the primary connection.
  p4::v1::StreamMessageRequest request0;
  request0.mutable_arbitration()->set_device_id(GetDeviceId());
  *request0.mutable_arbitration()->mutable_election_id() = GetElectionId(2);
  ASSERT_OK_AND_ASSIGN(p4::v1::StreamMessageResponse response,
                       SendStreamRequest(*stream0, request0));
  EXPECT_EQ(response.arbitration().status().code(), grpc::StatusCode::OK);

  // Send second arbitration request with a lower election ID. Because the
  // election ID is lower than the first it becomes a backup connection.
  p4::v1::StreamMessageRequest request1;
  request1.mutable_arbitration()->set_device_id(GetDeviceId());
  *request1.mutable_arbitration()->mutable_election_id() = GetElectionId(1);
  ASSERT_OK_AND_ASSIGN(response, SendStreamRequest(*stream1, request1));
  EXPECT_NE(response.arbitration().status().code(), grpc::StatusCode::OK);

  // From the current primary connection update the election ID. It should still
  // be the primary.
  *request0.mutable_arbitration()->mutable_election_id() = GetElectionId(3);
  ASSERT_OK_AND_ASSIGN(response, SendStreamRequest(*stream0, request0));
  EXPECT_EQ(response.arbitration().status().code(), grpc::StatusCode::OK);

  // Because the primary connection changed we expect all connections to be
  // informed about the new election ID.
  ASSERT_OK_AND_ASSIGN(response, GetStreamResponse(*stream1));
  EXPECT_EQ(response.arbitration().status().code(),
            grpc::StatusCode::ALREADY_EXISTS);
  EXPECT_EQ(response.arbitration().election_id().high(),
            request0.arbitration().election_id().high());
  EXPECT_EQ(response.arbitration().election_id().low(),
            request0.arbitration().election_id().low());
}

// Assuming the backup is still lower than the current primary.
TEST_F(ArbitrationTest, DoNotNofityIfBackupIncreasesItsElectionId) {
  grpc::ClientContext context0;
  std::unique_ptr<P4RuntimeStream> stream0 = stub_->StreamChannel(&context0);

  grpc::ClientContext context1;
  std::unique_ptr<P4RuntimeStream> stream1 = stub_->StreamChannel(&context1);

  // Send first arbitration request, and because it's the first request it will
  // default to the primary connection.
  p4::v1::StreamMessageRequest request0;
  request0.mutable_arbitration()->set_device_id(GetDeviceId());
  *request0.mutable_arbitration()->mutable_election_id() = GetElectionId(3);
  ASSERT_OK_AND_ASSIGN(p4::v1::StreamMessageResponse response,
                       SendStreamRequest(*stream0, request0));
  EXPECT_EQ(response.arbitration().status().code(), grpc::StatusCode::OK);

  // Send second arbitration request with a lower election ID. Because the
  // election ID is lower than the first it becomes a backup connection.
  p4::v1::StreamMessageRequest request1;
  request1.mutable_arbitration()->set_device_id(GetDeviceId());
  *request1.mutable_arbitration()->mutable_election_id() = GetElectionId(1);
  ASSERT_OK_AND_ASSIGN(response, SendStreamRequest(*stream1, request1));
  EXPECT_NE(response.arbitration().status().code(), grpc::StatusCode::OK);

  // From the current backup connection update the election ID such that it is
  // higher than the current, but not high enough to become the primary.
  *request1.mutable_arbitration()->mutable_election_id() = GetElectionId(2);
  ASSERT_OK_AND_ASSIGN(response, SendStreamRequest(*stream1, request1));
  EXPECT_NE(response.arbitration().status().code(), grpc::StatusCode::OK);

  // Stop the primary stream, and because it wasn't notified we should see no
  // response.
  stream0->WritesDone();
  EXPECT_THAT(GetStreamResponse(*stream0),
              StatusIs(absl::StatusCode::kInternal));
}

TEST_F(ArbitrationTest, NotifyAllConnectionsWhenPrimaryBecomesBackup) {
  grpc::ClientContext context0;
  std::unique_ptr<P4RuntimeStream> stream0 = stub_->StreamChannel(&context0);

  grpc::ClientContext context1;
  std::unique_ptr<P4RuntimeStream> stream1 = stub_->StreamChannel(&context1);

  // Send first arbitration request, and because it's the first request it will
  // default to the primary connection.
  p4::v1::StreamMessageRequest request0;
  request0.mutable_arbitration()->set_device_id(GetDeviceId());
  *request0.mutable_arbitration()->mutable_election_id() = GetElectionId(2);
  ASSERT_OK_AND_ASSIGN(p4::v1::StreamMessageResponse response,
                       SendStreamRequest(*stream0, request0));
  EXPECT_EQ(response.arbitration().status().code(), grpc::StatusCode::OK);

  // Send second arbitration request with a lower election ID. Because the
  // election ID is lower than the first it becomes a backup connection.
  p4::v1::StreamMessageRequest request1;
  request1.mutable_arbitration()->set_device_id(GetDeviceId());
  *request1.mutable_arbitration()->mutable_election_id() = GetElectionId(1);
  ASSERT_OK_AND_ASSIGN(response, SendStreamRequest(*stream1, request1));
  EXPECT_NE(response.arbitration().status().code(), grpc::StatusCode::OK);

  // Update the primary connection's election ID, and force it to become a
  // backup. Because there is no longer an active primary connection we epxect
  // the connections to receive a NOT_FOUND response.
  request0.mutable_arbitration()->mutable_election_id()->Clear();
  ASSERT_OK_AND_ASSIGN(response, SendStreamRequest(*stream0, request0));
  EXPECT_EQ(response.arbitration().status().code(),
            grpc::StatusCode::NOT_FOUND);

  // Because the primary connection changed we expect all connections to be
  // informed. Because there is no longer an active primary connection we epxect
  // the existing connections to receive a NOT_FOUND response.
  ASSERT_OK_AND_ASSIGN(response, GetStreamResponse(*stream1));
  EXPECT_EQ(response.arbitration().status().code(),
            grpc::StatusCode::NOT_FOUND);
}

TEST_F(ArbitrationTest, PrimaryConnectionCanReestablishAfterGoingDown) {
  grpc::ClientContext context;
  std::unique_ptr<P4RuntimeStream> stream = stub_->StreamChannel(&context);

  // Send first arbitration request.
  p4::v1::StreamMessageRequest request;
  request.mutable_arbitration()->set_device_id(GetDeviceId());
  *request.mutable_arbitration()->mutable_election_id() = GetElectionId(2);
  ASSERT_OK_AND_ASSIGN(p4::v1::StreamMessageResponse response,
                       SendStreamRequest(*stream, request));

  // Because it's the first request it will default to the primary connection.
  EXPECT_EQ(response.arbitration().status().code(), grpc::StatusCode::OK);

  // Close the stream to flush the connection for the P4RT service.
  stream->WritesDone();
  EXPECT_OK(stream->Finish());

  // Then open a new one, and send the same arbitration request.
  grpc::ClientContext new_context;
  stream = stub_->StreamChannel(&new_context);
  ASSERT_OK_AND_ASSIGN(response, SendStreamRequest(*stream, request));

  // Because the old stream was flushed we can re-establish the connection.
  EXPECT_EQ(response.arbitration().status().code(), grpc::StatusCode::OK);
}

TEST_F(ArbitrationTest, PrimaryConnectionCanReestablishAfterBecomingBackup) {
  grpc::ClientContext context0;
  std::unique_ptr<P4RuntimeStream> stream0 = stub_->StreamChannel(&context0);

  grpc::ClientContext context1;
  std::unique_ptr<P4RuntimeStream> stream1 = stub_->StreamChannel(&context1);

  // Send first arbitration request, and because it's the first request it will
  // default to the primary connection.
  p4::v1::StreamMessageRequest request0;
  request0.mutable_arbitration()->set_device_id(GetDeviceId());
  *request0.mutable_arbitration()->mutable_election_id() = GetElectionId(2);
  ASSERT_OK_AND_ASSIGN(p4::v1::StreamMessageResponse response,
                       SendStreamRequest(*stream0, request0));
  EXPECT_EQ(response.arbitration().status().code(), grpc::StatusCode::OK);

  // Send second arbitration request with a lower election ID. Because the
  // election ID is lower than the first it becomes a backup connection.
  p4::v1::StreamMessageRequest request1;
  request1.mutable_arbitration()->set_device_id(GetDeviceId());
  *request1.mutable_arbitration()->mutable_election_id() = GetElectionId(1);
  ASSERT_OK_AND_ASSIGN(response, SendStreamRequest(*stream1, request1));
  EXPECT_NE(response.arbitration().status().code(), grpc::StatusCode::OK);

  // Update the primary connection's election ID, and force it to become a
  // backup. Because there is no longer an active primary connection we epxect
  // the connections to receive a NOT_FOUND response.
  request0.mutable_arbitration()->mutable_election_id()->Clear();
  ASSERT_OK_AND_ASSIGN(response, SendStreamRequest(*stream0, request0));
  EXPECT_EQ(response.arbitration().status().code(),
            grpc::StatusCode::NOT_FOUND);

  // Because the primary connection changed we expect all connections to be
  // informed. Because there is no longer an active primary connection we
  // epxect the existing connections to receive a NOT_FOUND response.
  ASSERT_OK_AND_ASSIGN(response, GetStreamResponse(*stream1));
  EXPECT_EQ(response.arbitration().status().code(),
            grpc::StatusCode::NOT_FOUND);

  // Send third arbitration request with the same election ID as the first.
  // Because it's the highest ID seen so far, it becomes primary again.
  *request0.mutable_arbitration()->mutable_election_id() = GetElectionId(2);
  ASSERT_OK_AND_ASSIGN(response, SendStreamRequest(*stream0, request0));
  EXPECT_EQ(response.arbitration().status().code(), grpc::StatusCode::OK);

  // Because the primary connection changed we expect all connections to be
  // informed. Because there a new active primary connection we epxect the
  // existing connections to receive a ALREADY_EXISTS response.
  ASSERT_OK_AND_ASSIGN(response, GetStreamResponse(*stream1));
  EXPECT_EQ(response.arbitration().status().code(),
            grpc::StatusCode::ALREADY_EXISTS);
}

TEST_F(ArbitrationTest, PrimaryMustUseElectionIdHigherThanAllPastConnections) {
  grpc::ClientContext context;
  std::unique_ptr<P4RuntimeStream> stream = stub_->StreamChannel(&context);

  // Send first arbitration request.
  p4::v1::StreamMessageRequest request;
  request.mutable_arbitration()->set_device_id(GetDeviceId());
  *request.mutable_arbitration()->mutable_election_id() = GetElectionId(2);
  ASSERT_OK_AND_ASSIGN(p4::v1::StreamMessageResponse response,
                       SendStreamRequest(*stream, request));

  // Because it's the first request it will default to the primary connection.
  EXPECT_EQ(response.arbitration().status().code(), grpc::StatusCode::OK);

  // Close the stream to flush the connection for the P4RT service.
  stream->WritesDone();
  EXPECT_OK(stream->Finish());

  // Try to open a new connection with a lower election ID.
  grpc::ClientContext new_context;
  stream = stub_->StreamChannel(&new_context);
  *request.mutable_arbitration()->mutable_election_id() = GetElectionId(1);
  ASSERT_OK_AND_ASSIGN(response, SendStreamRequest(*stream, request));

  // Because the old stream had a higher election ID this new connection becomes
  // a backup.
  EXPECT_NE(response.arbitration().status().code(), grpc::StatusCode::OK);
}

TEST_F(ArbitrationTest, PrimaryCanSendDuplicateArbitationRequests) {
  grpc::ClientContext context;
  std::unique_ptr<P4RuntimeStream> stream = stub_->StreamChannel(&context);

  // Send first arbitration request.
  p4::v1::StreamMessageRequest request;
  request.mutable_arbitration()->set_device_id(GetDeviceId());
  *request.mutable_arbitration()->mutable_election_id() = GetElectionId(2);
  ASSERT_OK_AND_ASSIGN(p4::v1::StreamMessageResponse response,
                       SendStreamRequest(*stream, request));

  // Because it's the first request it will default to the primary connection.
  EXPECT_EQ(response.arbitration().status().code(), grpc::StatusCode::OK);

  // Sending a duplicate request is effectivly a no-op, and the switch should
  // still return that it's the primary connection.
  ASSERT_OK_AND_ASSIGN(response, SendStreamRequest(*stream, request));
  EXPECT_EQ(response.arbitration().status().code(), grpc::StatusCode::OK);
}

TEST_F(ArbitrationTest, BackupConnectionCannotUpdateForwardingPipeline) {
  grpc::ClientContext stream_context;
  std::unique_ptr<P4RuntimeStream> stream =
      stub_->StreamChannel(&stream_context);

  // Test with forced backup connection.
  {
    p4::v1::StreamMessageRequest request;
    request.mutable_arbitration()->set_device_id(GetDeviceId());
    ASSERT_OK_AND_ASSIGN(p4::v1::StreamMessageResponse response,
                         SendStreamRequest(*stream, request));
    ASSERT_NE(response.arbitration().status().code(), grpc::StatusCode::OK);
  }

  p4::v1::SetForwardingPipelineConfigRequest request;
  request.set_device_id(GetDeviceId());

  p4::v1::SetForwardingPipelineConfigResponse response;
  grpc::ClientContext context;
  EXPECT_EQ(stub_->SetForwardingPipelineConfig(&context, request, &response)
                .error_code(),
            grpc::StatusCode::PERMISSION_DENIED);
}

TEST_F(ArbitrationTest, BackupConnectionCannotSendWriteRequest) {
  grpc::ClientContext primary_context;
  std::unique_ptr<P4RuntimeStream> primary =
      stub_->StreamChannel(&primary_context);

  grpc::ClientContext backup_context;
  std::unique_ptr<P4RuntimeStream> backup =
      stub_->StreamChannel(&backup_context);

  // Test with primary & backup connection.
  {
    p4::v1::StreamMessageResponse response;
    p4::v1::StreamMessageRequest request;
    request.mutable_arbitration()->set_device_id(GetDeviceId());
    request.mutable_arbitration()->mutable_election_id()->set_high(2);
    ASSERT_OK_AND_ASSIGN(response, SendStreamRequest(*primary, request));
    ASSERT_EQ(response.arbitration().status().code(), grpc::StatusCode::OK);

    request.mutable_arbitration()->mutable_election_id()->set_high(1);
    ASSERT_OK_AND_ASSIGN(response, SendStreamRequest(*backup, request));
    ASSERT_NE(response.arbitration().status().code(), grpc::StatusCode::OK);
  }

  p4::v1::WriteRequest request;
  request.set_device_id(GetDeviceId());
  request.mutable_election_id()->set_high(1);

  p4::v1::WriteResponse response;
  grpc::ClientContext context;
  EXPECT_EQ(stub_->Write(&context, request, &response).error_code(),
            grpc::StatusCode::PERMISSION_DENIED);
}

// Only applies if they are the same role.
TEST_F(ArbitrationTest, TwoConnectionsCannotReuseElectionId) {
  grpc::ClientContext primary_context;
  std::unique_ptr<P4RuntimeStream> primary =
      stub_->StreamChannel(&primary_context);

  grpc::ClientContext backup_context;
  std::unique_ptr<P4RuntimeStream> backup =
      stub_->StreamChannel(&backup_context);

  p4::v1::StreamMessageResponse response;
  p4::v1::StreamMessageRequest request;
  request.mutable_arbitration()->set_device_id(GetDeviceId());
  request.mutable_arbitration()->mutable_election_id()->set_high(2);
  ASSERT_OK_AND_ASSIGN(response, SendStreamRequest(*primary, request));
  ASSERT_EQ(response.arbitration().status().code(), grpc::StatusCode::OK);

  request.mutable_arbitration()->mutable_election_id()->set_high(2);
  backup->Write(request);
  EXPECT_EQ(backup->Finish().error_code(), grpc::StatusCode::INVALID_ARGUMENT);
}

TEST_F(ArbitrationTest, ConnectionCannotChangeItsRoleId) {
  grpc::ClientContext context;
  std::unique_ptr<P4RuntimeStream> stream = stub_->StreamChannel(&context);

  p4::v1::StreamMessageResponse response;
  p4::v1::StreamMessageRequest request;
  request.mutable_arbitration()->set_device_id(GetDeviceId());
  request.mutable_arbitration()->mutable_election_id()->set_high(2);
  *request.mutable_arbitration()->mutable_role()->mutable_name() = "A";
  ASSERT_OK_AND_ASSIGN(response, SendStreamRequest(*stream, request));
  ASSERT_EQ(response.arbitration().status().code(), grpc::StatusCode::OK);

  *request.mutable_arbitration()->mutable_role()->mutable_name() = "B";
  stream->Write(request);
  EXPECT_EQ(stream->Finish().error_code(),
            grpc::StatusCode::FAILED_PRECONDITION);
}

}  // namespace
}  // namespace p4rt_app
