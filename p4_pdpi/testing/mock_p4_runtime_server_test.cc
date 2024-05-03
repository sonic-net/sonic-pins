#include "p4_pdpi/testing/mock_p4_runtime_server.h"

#include <memory>

#include "gmock/gmock.h"
#include "grpcpp/channel.h"
#include "grpcpp/client_context.h"
#include "grpcpp/create_channel.h"
#include "gtest/gtest.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4/v1/p4runtime.pb.h"

namespace pdpi {
namespace {

using ::p4::v1::P4Runtime;

using ::p4::v1::GetForwardingPipelineConfigRequest;
using ::p4::v1::GetForwardingPipelineConfigResponse;
using ::p4::v1::ReadRequest;
using ::p4::v1::ReadResponse;
using ::p4::v1::SetForwardingPipelineConfigRequest;
using ::p4::v1::SetForwardingPipelineConfigResponse;
using ::p4::v1::StreamMessageResponse;
using ::p4::v1::WriteRequest;
using ::p4::v1::WriteResponse;

std::unique_ptr<P4Runtime::Stub> ConnectTo(const MockP4RuntimeServer& server) {
  return P4Runtime::NewStub(
      grpc::CreateChannel(server.address(), server.channel_credentials()));
}

TEST(MockP4RuntimeServerTest, WriteMockWorks) {
  MockP4RuntimeServer server;
  std::unique_ptr<P4Runtime::Stub> stub = ConnectTo(server);
  grpc::ClientContext context;

  EXPECT_CALL(server.service(), Write);
  WriteRequest request;
  WriteResponse response;
  EXPECT_TRUE(stub->Write(&context, request, &response).ok());
}

TEST(MockP4RuntimeServerTest, ReadMockWorks) {
  MockP4RuntimeServer server;
  std::unique_ptr<P4Runtime::Stub> stub = ConnectTo(server);
  grpc::ClientContext context;

  EXPECT_CALL(server.service(), Read);
  ReadRequest request;
  auto response_stream = stub->Read(&context, request);
  EXPECT_NE(response_stream, nullptr);
  ReadResponse response;
  EXPECT_FALSE(response_stream->Read(&response));
}

TEST(MockP4RuntimeServerTest, SetForwardingPipelineConfigMockWorks) {
  MockP4RuntimeServer server;
  std::unique_ptr<P4Runtime::Stub> stub = ConnectTo(server);
  grpc::ClientContext context;

  EXPECT_CALL(server.service(), SetForwardingPipelineConfig);
  SetForwardingPipelineConfigRequest request;
  SetForwardingPipelineConfigResponse response;
  EXPECT_TRUE(
      stub->SetForwardingPipelineConfig(&context, request, &response).ok());
}

TEST(MockP4RuntimeServerTest, GetForwardingPipelineConfigMockWorks) {
  MockP4RuntimeServer server;
  std::unique_ptr<P4Runtime::Stub> stub = ConnectTo(server);
  grpc::ClientContext context;

  EXPECT_CALL(server.service(), GetForwardingPipelineConfig);
  GetForwardingPipelineConfigRequest request;
  GetForwardingPipelineConfigResponse response;
  EXPECT_TRUE(
      stub->GetForwardingPipelineConfig(&context, request, &response).ok());
}

TEST(MockP4RuntimeServerTest, StreamChannelMockWorks) {
  MockP4RuntimeServer server;
  std::unique_ptr<P4Runtime::Stub> stub = ConnectTo(server);
  grpc::ClientContext context;

  EXPECT_CALL(server.service(), StreamChannel);
  auto stream = stub->StreamChannel(&context);
  EXPECT_NE(stream, nullptr);
  StreamMessageResponse response;
  EXPECT_FALSE(stream->Read(&response));
}

}  // namespace
}  // namespace pdpi
