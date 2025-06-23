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

#ifndef PINS_P4_INFRA_PR_RUNTIME_MOCK_P4_RUNTIME_SERVER_H_
#define PINS_P4_INFRA_PR_RUNTIME_MOCK_P4_RUNTIME_SERVER_H_

#include <memory>
#include <string>
#include <vector>

#include "absl/strings/str_cat.h"
#include "gmock/gmock.h"
#include "grpcpp/security/credentials.h"
#include "grpcpp/server.h"
#include "grpcpp/server_builder.h"
#include "grpcpp/support/status.h"
#include "p4/v1/p4runtime.grpc.pb.h"

namespace p4_runtime {

// A mocked `P4Runtime::Service` class.
class MockP4RuntimeService final : public p4::v1::P4Runtime::Service {
 public:
  MOCK_METHOD(grpc::Status, Write,
              (grpc::ServerContext * context,
               const p4::v1::WriteRequest* request,
               p4::v1::WriteResponse* response),
              (override));

  MOCK_METHOD(grpc::Status, Read,
              (grpc::ServerContext * context,
               const p4::v1::ReadRequest* request,
               grpc::ServerWriter<p4::v1::ReadResponse>* response_writer),
              (override));

  MOCK_METHOD(grpc::Status, SetForwardingPipelineConfig,
              (grpc::ServerContext * context,
               const p4::v1::SetForwardingPipelineConfigRequest* request,
               p4::v1::SetForwardingPipelineConfigResponse* response),
              (override));

  MOCK_METHOD(grpc::Status, GetForwardingPipelineConfig,
              (grpc::ServerContext * context,
               const p4::v1::GetForwardingPipelineConfigRequest* request,
               p4::v1::GetForwardingPipelineConfigResponse* response),
              (override));

  MOCK_METHOD(grpc::Status, StreamChannel,
              (grpc::ServerContext * context,
               (grpc::ServerReaderWriter<p4::v1::StreamMessageResponse,
                                         p4::v1::StreamMessageRequest>*)stream),
              (override));
};

// A P4Runtime server running on `localhost` whose underlying P4Runtime service
// is a mock. Useful for testing.
class MockP4RuntimeServer {
 public:
  // Starts up the server on `localhost`.
  MockP4RuntimeServer() = default;

  // Returns underlying mock.
  MockP4RuntimeService& service() { return service_; }

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
  const std::string& address() const { return address_; }

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
  int port_;  // Initialized by the `ServerBuilder` above.
  std::string address_ = absl::StrCat("localhost:", port_);
};

}  // namespace p4_runtime

#endif  // PINS_P4_INFRA_PR_RUNTIME_MOCK_P4_RUNTIME_SERVER_H_
