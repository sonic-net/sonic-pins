#include "fourward/fourward_server.h"

#include <chrono>
#include <memory>

#include "grpcpp/create_channel.h"
#include "grpcpp/security/credentials.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "p4/v1/p4runtime.grpc.pb.h"

namespace dvaas {
namespace {

TEST(FourwardServerTest, StartsAndRespondsToCapabilities) {
  ASSERT_OK_AND_ASSIGN(FourwardServer server, FourwardServer::Start());

  EXPECT_GT(server.Port(), 0);
  EXPECT_EQ(server.DeviceId(), 1);

  std::shared_ptr<grpc::Channel> channel = grpc::CreateChannel(
      server.Address(), grpc::InsecureChannelCredentials());
  std::unique_ptr<p4::v1::P4Runtime::StubInterface> stub =
      p4::v1::P4Runtime::NewStub(channel);

  grpc::ClientContext context;
  context.set_deadline(std::chrono::system_clock::now() +
                       std::chrono::seconds(5));
  p4::v1::CapabilitiesRequest request;
  p4::v1::CapabilitiesResponse response;
  grpc::Status status = stub->Capabilities(&context, request, &response);
  EXPECT_TRUE(status.ok()) << status.error_message();
  EXPECT_FALSE(response.p4runtime_api_version().empty());
}

TEST(FourwardServerTest, CustomDeviceId) {
  ASSERT_OK_AND_ASSIGN(FourwardServer server, FourwardServer::Start(42));
  EXPECT_EQ(server.DeviceId(), 42);
}

}  // namespace
}  // namespace dvaas
