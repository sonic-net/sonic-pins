#include "fourward/fourward_server.h"

#include <memory>
#include <string>

#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "grpcpp/channel.h"
#include "grpcpp/create_channel.h"
#include "grpcpp/security/credentials.h"
#include "gtest/gtest.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "tools/cpp/runfiles/runfiles.h"

namespace dvaas {
namespace {

using ::bazel::tools::cpp::runfiles::Runfiles;

std::string ServerBinaryPath() {
  std::string error;
  std::unique_ptr<Runfiles> runfiles(Runfiles::CreateForTest(&error));
  if (runfiles == nullptr) {
    ADD_FAILURE() << "Failed to create Runfiles: " << error;
    return "";
  }
  return runfiles->Rlocation("fourward/p4runtime/p4runtime_server");
}

TEST(FourwardServerTest, StartsAndRespondsToCapabilities) {
  std::string binary = ServerBinaryPath();
  ASSERT_FALSE(binary.empty());

  auto server = FourwardServer::Start(binary);
  ASSERT_TRUE(server.ok()) << server.status();

  EXPECT_GT(server->Port(), 0);
  EXPECT_EQ(server->DeviceId(), 1);
  EXPECT_EQ(server->Address(),
            absl::StrCat("localhost:", server->Port()));

  // Verify the server is actually responding to gRPC.
  auto channel = grpc::CreateChannel(server->Address(),
                                     grpc::InsecureChannelCredentials());
  auto stub = p4::v1::P4Runtime::NewStub(channel);

  grpc::ClientContext context;
  context.set_deadline(std::chrono::system_clock::now() +
                       std::chrono::seconds(5));
  p4::v1::CapabilitiesRequest request;
  p4::v1::CapabilitiesResponse response;
  auto status = stub->Capabilities(&context, request, &response);
  EXPECT_TRUE(status.ok()) << status.error_message();
  EXPECT_FALSE(response.p4runtime_api_version().empty());
}

TEST(FourwardServerTest, CustomDeviceId) {
  std::string binary = ServerBinaryPath();
  ASSERT_FALSE(binary.empty());

  auto server = FourwardServer::Start(binary, /*device_id=*/42);
  ASSERT_TRUE(server.ok()) << server.status();

  EXPECT_EQ(server->DeviceId(), 42);
}

TEST(FourwardServerTest, InvalidBinaryFails) {
  auto server = FourwardServer::Start("/nonexistent/binary");
  EXPECT_FALSE(server.ok());
}

}  // namespace
}  // namespace dvaas
