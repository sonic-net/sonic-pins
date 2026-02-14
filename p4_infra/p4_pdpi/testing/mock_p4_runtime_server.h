#ifndef PINS_P4_PDPI_TESTING_MOCK_P4_RUNTIME_SERVER_H_
#define PINS_P4_PDPI_TESTING_MOCK_P4_RUNTIME_SERVER_H_

#include <memory>
#include <vector>

#include "absl/strings/str_cat.h"
#include "grpcpp/security/credentials.h"
#include "grpcpp/server.h"
#include "grpcpp/server_builder.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "gmock/gmock.h"

namespace pdpi {

// A mocked `P4Runtime::Service` class.
class MockP4RuntimeService final : public p4::v1::P4Runtime::Service {
public:
  MOCK_METHOD(grpc::Status, Write,
              (grpc::ServerContext * context,
               const p4::v1::WriteRequest *request,
               p4::v1::WriteResponse *response),
              (override));

  MOCK_METHOD(grpc::Status, Read,
              (grpc::ServerContext * context,
               const p4::v1::ReadRequest *request,
               grpc::ServerWriter<p4::v1::ReadResponse> *response_writer),
              (override));

  MOCK_METHOD(grpc::Status, SetForwardingPipelineConfig,
              (grpc::ServerContext * context,
               const p4::v1::SetForwardingPipelineConfigRequest *request,
               p4::v1::SetForwardingPipelineConfigResponse *response),
              (override));

  MOCK_METHOD(grpc::Status, GetForwardingPipelineConfig,
              (grpc::ServerContext * context,
               const p4::v1::GetForwardingPipelineConfigRequest *request,
               p4::v1::GetForwardingPipelineConfigResponse *response),
              (override));

  MOCK_METHOD(
      grpc::Status, StreamChannel,
      (grpc::ServerContext * context,
       (grpc::ServerReaderWriter<p4::v1::StreamMessageResponse,
                                 p4::v1::StreamMessageRequest> *)stream),
      (override));
};

// A P4Runtime server running on `localhost` whose underlying P4Runtime service
// is a mock. Useful for testing.
class MockP4RuntimeServer {
public:
  // Starts up the server on `localhost`.
  MockP4RuntimeServer() = default;

  // Returns underlying mock.
  MockP4RuntimeService &service() { return service_; }

  // Returns client-side credentials for connecting to this server.
  std::shared_ptr<grpc::ChannelCredentials> channel_credentials() const {
    return channel_credentials_;
  }

  // Returns server-side credentials.
  std::shared_ptr<grpc::ServerCredentials> server_credentials() const {
    return server_credentials_;
  }
  // Returns port on which this server is reachable.
  int port() const { return port_; }

  // Returns address at which this server is reachable.
  const std::string &address() const { return address_; }

private:
  MockP4RuntimeService service_;
  std::shared_ptr<grpc::ChannelCredentials> channel_credentials_ =
      grpc::experimental::LocalCredentials(LOCAL_TCP);
  std::shared_ptr<grpc::ServerCredentials> server_credentials_ =
      grpc::experimental::LocalServerCredentials(LOCAL_TCP);
  std::unique_ptr<grpc::Server> server_ =
      grpc::ServerBuilder()
          .AddListeningPort("[::]:0", server_credentials_, &port_)
          .RegisterService(&service_)
          .BuildAndStart();
  int port_; // Initialized by the `ServerBuilder` above.
  std::string address_ = absl::StrCat("localhost:", port_);
};

} // namespace pdpi

#endif // PINS_P4_PDPI_TESTING_MOCK_P4_RUNTIME_SERVER_H_
