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

#include "p4_infra/p4_runtime/p4_runtime_client_interceptor.h"

#include <memory>
#include <optional>
#include <vector>

#include "gmock/gmock.h"
#include "grpcpp/client_context.h"
#include "grpcpp/security/credentials.h"
#include "grpcpp/support/channel_arguments.h"
#include "grpcpp/support/client_interceptor.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/testing.h"
#include "net/google::protobuf/public/message.h"
#include "net/google::protobuf/public/repeated_field.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_runtime/mock_p4_runtime_server.h"

namespace p4_runtime {
namespace {

using ::grpc::experimental::ClientInterceptorFactoryInterface;
using ::grpc::experimental::CreateCustomChannelWithInterceptors;
using ::p4::v1::GetForwardingPipelineConfigRequest;
using ::p4::v1::GetForwardingPipelineConfigResponse;
using ::p4::v1::P4Runtime;
using ::p4::v1::ReadRequest;
using ::p4::v1::ReadResponse;
using ::p4::v1::SetForwardingPipelineConfigRequest;
using ::p4::v1::SetForwardingPipelineConfigResponse;
using ::p4::v1::StreamMessageRequest;
using ::p4::v1::StreamMessageResponse;
using ::p4::v1::WriteRequest;
using ::p4::v1::WriteResponse;
using ::testing::_;
using ::testing::EqualsProto;
using ::testing::InSequence;
using ::testing::Pointee;
using ::testing::Return;

// Returns P4Runtime stub connected to the given server, with the given
// `interceptors` injected in-between.
std::unique_ptr<P4Runtime::StubInterface> ConnectWithInterceptors(
    const MockP4RuntimeServer& server,
    std::vector<std::unique_ptr<ClientInterceptorFactoryInterface>>
        interceptors) {
  std::shared_ptr<grpc::Channel> channel = CreateCustomChannelWithInterceptors(
      server.address(), server.channel_credentials(), grpc::ChannelArguments(),
      std::move(interceptors));
  return P4Runtime::NewStub(channel);
}

// For the purposes of testing `P4RuntimeClientInterceptor`, a simple sub class
// that intercepts requests of type `T` and checks that they are equal to a
// given `expected_request_`. Optionally also modifies the `expected_request_`
// to a given `modified_request_`.
template <class T>
class RequestInterceptor : public P4RuntimeClientInterceptor {
 public:
  RequestInterceptor(T expected_request,
                     std::optional<T> modified_request = std::nullopt)
      : expected_request_(std::move(expected_request)),
        modified_request_(std::move(modified_request)) {}

  std::unique_ptr<T> InterceptRequest(const T& request) override {
    EXPECT_THAT(request, EqualsProto(expected_request_));
    return modified_request_.has_value()
               ? std::make_unique<T>(*modified_request_)
               : nullptr;
  }

 private:
  T expected_request_;
  std::optional<T> modified_request_;
};

// For the purposes of testing `P4RuntimeClientInterceptor`, a simple sub class
// that intercepts responses of type `T` and checks that they are equal to a
// given `expected_response_`. Optionally also modifies the `expected_response_`
// to a given `modified_response_`.
template <class T>
class ResponseInterceptor : public P4RuntimeClientInterceptor {
 public:
  ResponseInterceptor(T expected_response,
                      std::optional<T> modified_response = std::nullopt)
      : expected_response_(std::move(expected_response)),
        modified_response_(std::move(modified_response)) {}

  void InterceptResponse(T& response) override {
    EXPECT_THAT(response, EqualsProto(expected_response_));
    if (modified_response_.has_value()) response = *modified_response_;
  }

 private:
  T expected_response_;
  std::optional<T> modified_response_;
};

TEST(P4RuntimeClientInterceptorTest, WriteInterceptionWorks) {
  // Start up mock server.
  MockP4RuntimeServer mock_server;

  // Test requests and responses.
  ASSERT_OK_AND_ASSIGN(auto request, gutil::ParseTextProto<WriteRequest>(R"pb(
                         device_id: 42
                       )pb"));
  ASSERT_OK_AND_ASSIGN(auto modified_request,
                       gutil::ParseTextProto<WriteRequest>(R"pb(
                         device_id: 24
                       )pb"));
  WriteResponse response;  // Empty message.

  InSequence s;
  using Interceptors =
      std::vector<std::unique_ptr<ClientInterceptorFactoryInterface>>;

  // Test no-op interceptor: server receives unmodified request.
  {
    Interceptors noop_interceptors;
    noop_interceptors.emplace_back() =
        std::make_unique<RequestInterceptor<WriteRequest>>(request);
    noop_interceptors.emplace_back() =
        std::make_unique<ResponseInterceptor<WriteResponse>>(response);
    std::unique_ptr<P4Runtime::StubInterface> stub =
        ConnectWithInterceptors(mock_server, std::move(noop_interceptors));
    EXPECT_CALL(mock_server.service(),
                Write(_, Pointee(EqualsProto(request)), _))
        .WillOnce(Return(grpc::Status::OK));
    grpc::ClientContext context;
    WriteResponse actual_response;  // Empty message.
    ASSERT_TRUE(stub->Write(&context, request, &actual_response).ok());
  }

  // Test modifying interceptor: server receives modified request.
  {
    Interceptors modifying_interceptors;
    modifying_interceptors.emplace_back() =
        std::make_unique<RequestInterceptor<WriteRequest>>(request,
                                                           modified_request);
    modifying_interceptors.emplace_back() =
        std::make_unique<ResponseInterceptor<WriteResponse>>(response,
                                                             response);
    std::unique_ptr<P4Runtime::StubInterface> stub =
        ConnectWithInterceptors(mock_server, std::move(modifying_interceptors));
    EXPECT_CALL(mock_server.service(),
                Write(_, Pointee(EqualsProto(modified_request)), _))
        .WillOnce(Return(grpc::Status::OK));
    grpc::ClientContext context;
    WriteResponse actual_response;  // Empty message.
    ASSERT_TRUE(stub->Write(&context, request, &response).ok());
  }
}

TEST(P4RuntimeClientInterceptorTest, ReadInterceptionWorks) {
  // Start up mock server.
  MockP4RuntimeServer mock_server;

  // Test requests.
  ASSERT_OK_AND_ASSIGN(auto request, gutil::ParseTextProto<ReadRequest>(R"pb(
                         device_id: 42
                       )pb"));
  ASSERT_OK_AND_ASSIGN(auto modified_request,
                       gutil::ParseTextProto<ReadRequest>(R"pb(
                         device_id: 24
                       )pb"));
  ASSERT_OK_AND_ASSIGN(auto response, gutil::ParseTextProto<ReadResponse>(R"pb(
                         entities { extern_entry {} }
                       )pb"));
  ASSERT_OK_AND_ASSIGN(auto modified_response,
                       gutil::ParseTextProto<ReadResponse>(R"pb(
                         entities { table_entry {} }
                       )pb"));

  InSequence s;
  using Interceptors =
      std::vector<std::unique_ptr<ClientInterceptorFactoryInterface>>;

  // Test no-op interceptor: server receives unmodified request, client receives
  // back unmodified response.
  {
    Interceptors noop_interceptors;
    noop_interceptors.emplace_back() =
        std::make_unique<RequestInterceptor<ReadRequest>>(request);
    noop_interceptors.emplace_back() =
        std::make_unique<ResponseInterceptor<ReadResponse>>(response);
    std::unique_ptr<P4Runtime::StubInterface> stub =
        ConnectWithInterceptors(mock_server, std::move(noop_interceptors));
    EXPECT_CALL(mock_server.service(), Read)
        .WillOnce([&](auto*, auto* request_ptr, auto* response_stream) {
          EXPECT_THAT(request_ptr, Pointee(EqualsProto(request)));
          EXPECT_TRUE(response_stream->Write(response));
          return grpc::Status::OK;
        });
    grpc::ClientContext context;
    auto reader = stub->Read(&context, request);
    ReadResponse actual_response;
    EXPECT_TRUE(reader->Read(&actual_response));
    EXPECT_THAT(actual_response, EqualsProto(response));
    EXPECT_FALSE(reader->Read(&actual_response));
  }

  // Test modifying interceptor: server receives modified request, client
  // receives back modified response.
  {
    Interceptors modifying_interceptors;
    modifying_interceptors.emplace_back() =
        std::make_unique<RequestInterceptor<ReadRequest>>(request,
                                                          modified_request);
    modifying_interceptors.emplace_back() =
        std::make_unique<ResponseInterceptor<ReadResponse>>(response,
                                                            modified_response);
    std::unique_ptr<P4Runtime::StubInterface> stub =
        ConnectWithInterceptors(mock_server, std::move(modifying_interceptors));
    EXPECT_CALL(mock_server.service(), Read)
        .WillOnce([&](auto*, auto* request_ptr, auto* response_stream) {
          EXPECT_THAT(request_ptr, Pointee(EqualsProto(modified_request)));
          EXPECT_TRUE(response_stream->Write(response));
          return grpc::Status::OK;
        });
    grpc::ClientContext context;
    auto reader = stub->Read(&context, request);
    ReadResponse actual_response;
    EXPECT_TRUE(reader->Read(&actual_response));
    EXPECT_THAT(actual_response, EqualsProto(modified_response));
    EXPECT_FALSE(reader->Read(&actual_response));
  }
}

TEST(P4RuntimeClientInterceptorTest,
     SetForwardingPipelineConfigInterceptionWorks) {
  // Start up mock server.
  MockP4RuntimeServer mock_server;

  // Test requests and responses.
  ASSERT_OK_AND_ASSIGN(
      auto request,
      gutil::ParseTextProto<SetForwardingPipelineConfigRequest>(R"pb(
        device_id: 42
      )pb"));
  ASSERT_OK_AND_ASSIGN(
      auto modified_request,
      gutil::ParseTextProto<SetForwardingPipelineConfigRequest>(R"pb(
        device_id: 24
      )pb"));
  SetForwardingPipelineConfigResponse response;  // Empty message.

  InSequence s;
  using Interceptors =
      std::vector<std::unique_ptr<ClientInterceptorFactoryInterface>>;

  // Test no-op interceptor: server receives unmodified request.
  {
    Interceptors noop_interceptors;
    noop_interceptors.emplace_back() = std::make_unique<
        RequestInterceptor<SetForwardingPipelineConfigRequest>>(request);
    noop_interceptors.emplace_back() = std::make_unique<
        ResponseInterceptor<SetForwardingPipelineConfigResponse>>(response);
    std::unique_ptr<P4Runtime::StubInterface> stub =
        ConnectWithInterceptors(mock_server, std::move(noop_interceptors));
    EXPECT_CALL(mock_server.service(), SetForwardingPipelineConfig(
                                           _, Pointee(EqualsProto(request)), _))
        .WillOnce(Return(grpc::Status::OK));
    grpc::ClientContext context;
    SetForwardingPipelineConfigResponse response;
    ASSERT_TRUE(
        stub->SetForwardingPipelineConfig(&context, request, &response).ok());
  }

  // Test modifying interceptor: server receives modified request.
  {
    Interceptors modifying_interceptors;
    modifying_interceptors.emplace_back() = std::make_unique<
        RequestInterceptor<SetForwardingPipelineConfigRequest>>(
        request, modified_request);
    modifying_interceptors.emplace_back() = std::make_unique<
        ResponseInterceptor<SetForwardingPipelineConfigResponse>>(response,
                                                                  response);
    std::unique_ptr<P4Runtime::StubInterface> stub =
        ConnectWithInterceptors(mock_server, std::move(modifying_interceptors));
    EXPECT_CALL(mock_server.service(),
                SetForwardingPipelineConfig(
                    _, Pointee(EqualsProto(modified_request)), _))
        .WillOnce(Return(grpc::Status::OK));
    grpc::ClientContext context;
    SetForwardingPipelineConfigResponse response;
    ASSERT_TRUE(
        stub->SetForwardingPipelineConfig(&context, request, &response).ok());
  }
}

TEST(P4RuntimeClientInterceptorTest,
     GetForwardingPipelineConfigInterceptionWorks) {
  // Start up mock server.
  MockP4RuntimeServer mock_server;

  // Test requests.
  ASSERT_OK_AND_ASSIGN(
      auto request,
      gutil::ParseTextProto<GetForwardingPipelineConfigRequest>(R"pb(
        device_id: 42
      )pb"));
  ASSERT_OK_AND_ASSIGN(
      auto modified_request,
      gutil::ParseTextProto<GetForwardingPipelineConfigRequest>(R"pb(
        device_id: 24
      )pb"));
  ASSERT_OK_AND_ASSIGN(
      auto response,
      gutil::ParseTextProto<GetForwardingPipelineConfigResponse>(R"pb(
        config {}
      )pb"));
  ASSERT_OK_AND_ASSIGN(
      auto modified_response,
      gutil::ParseTextProto<GetForwardingPipelineConfigResponse>(R"pb(
        config { p4_device_config: "foo" }
      )pb"));

  InSequence s;
  using Interceptors =
      std::vector<std::unique_ptr<ClientInterceptorFactoryInterface>>;

  // Test no-op interceptor: server receives unmodified request, client receives
  // back unmodified response.
  {
    Interceptors noop_interceptors;
    noop_interceptors.emplace_back() = std::make_unique<
        RequestInterceptor<GetForwardingPipelineConfigRequest>>(request);
    noop_interceptors.emplace_back() = std::make_unique<
        ResponseInterceptor<GetForwardingPipelineConfigResponse>>(response);
    std::unique_ptr<P4Runtime::StubInterface> stub =
        ConnectWithInterceptors(mock_server, std::move(noop_interceptors));
    EXPECT_CALL(mock_server.service(), GetForwardingPipelineConfig)
        .WillOnce([&](auto*, auto* request_ptr, auto* response_ptr) {
          EXPECT_THAT(request_ptr, Pointee(EqualsProto(request)));
          *response_ptr = response;
          return grpc::Status::OK;
        });
    grpc::ClientContext context;
    GetForwardingPipelineConfigResponse actual_response;
    EXPECT_TRUE(
        stub->GetForwardingPipelineConfig(&context, request, &actual_response)
            .ok());
    EXPECT_THAT(actual_response, EqualsProto(response));
  }

  // Test modifying interceptor: server receives modified request, client
  // receives back modified response.
  {
    Interceptors modifying_interceptors;
    modifying_interceptors.emplace_back() = std::make_unique<
        RequestInterceptor<GetForwardingPipelineConfigRequest>>(
        request, modified_request);
    modifying_interceptors.emplace_back() = std::make_unique<
        ResponseInterceptor<GetForwardingPipelineConfigResponse>>(
        response, modified_response);
    std::unique_ptr<P4Runtime::StubInterface> stub =
        ConnectWithInterceptors(mock_server, std::move(modifying_interceptors));
    EXPECT_CALL(mock_server.service(), GetForwardingPipelineConfig)
        .WillOnce([&](auto*, auto* request_ptr, auto* response_ptr) {
          EXPECT_THAT(request_ptr, Pointee(EqualsProto(modified_request)));
          *response_ptr = response;
          return grpc::Status::OK;
        });
    grpc::ClientContext context;
    GetForwardingPipelineConfigResponse actual_response;
    EXPECT_TRUE(
        stub->GetForwardingPipelineConfig(&context, request, &actual_response)
            .ok());
    EXPECT_THAT(actual_response, EqualsProto(modified_response));
  }
}

TEST(P4RuntimeClientInterceptorTest, StreamMessageInterceptionWorks) {
  // Start up mock server.
  MockP4RuntimeServer mock_server;

  // Test requests.
  ASSERT_OK_AND_ASSIGN(auto request,
                       gutil::ParseTextProto<StreamMessageRequest>(R"pb(
                         arbitration {}
                       )pb"));
  ASSERT_OK_AND_ASSIGN(auto modified_request,
                       gutil::ParseTextProto<StreamMessageRequest>(R"pb(
                         packet {}
                       )pb"));
  ASSERT_OK_AND_ASSIGN(auto response,
                       gutil::ParseTextProto<StreamMessageResponse>(R"pb(
                         digest {}
                       )pb"));
  ASSERT_OK_AND_ASSIGN(auto modified_response,
                       gutil::ParseTextProto<StreamMessageResponse>(R"pb(
                         error {}
                       )pb"));

  InSequence s;
  using Interceptors =
      std::vector<std::unique_ptr<ClientInterceptorFactoryInterface>>;

  // Test no-op interceptor: server receives unmodified request, client receives
  // back unmodified response.
  {
    Interceptors noop_interceptors;
    noop_interceptors.emplace_back() =
        std::make_unique<RequestInterceptor<StreamMessageRequest>>(request);
    noop_interceptors.emplace_back() =
        std::make_unique<ResponseInterceptor<StreamMessageResponse>>(response);
    std::unique_ptr<P4Runtime::StubInterface> stub =
        ConnectWithInterceptors(mock_server, std::move(noop_interceptors));
    EXPECT_CALL(mock_server.service(), StreamChannel)
        .WillOnce([&](auto*, auto* stream) {
          StreamMessageRequest actual_request;
          EXPECT_TRUE(stream->Read(&actual_request));
          EXPECT_THAT(actual_request, EqualsProto(request));
          EXPECT_FALSE(stream->Read(&actual_request));
          EXPECT_TRUE(stream->Write(response));
          return grpc::Status::OK;
        });
    grpc::ClientContext context;
    StreamMessageResponse actual_response;
    auto stream = stub->StreamChannel(&context);
    EXPECT_TRUE(stream->Write(request));
    EXPECT_TRUE(stream->WritesDone());
    EXPECT_TRUE(stream->Read(&actual_response));
    EXPECT_THAT(actual_response, EqualsProto(response));
    EXPECT_FALSE(stream->Read(&actual_response));
  }

  // Test modifying interceptor: server receives modified request, client
  // receives back modified response.
  {
    Interceptors modifying_interceptors;
    modifying_interceptors.emplace_back() =
        std::make_unique<RequestInterceptor<StreamMessageRequest>>(
            request, modified_request);
    modifying_interceptors.emplace_back() =
        std::make_unique<ResponseInterceptor<StreamMessageResponse>>(
            response, modified_response);
    std::unique_ptr<P4Runtime::StubInterface> stub =
        ConnectWithInterceptors(mock_server, std::move(modifying_interceptors));
    EXPECT_CALL(mock_server.service(), StreamChannel)
        .WillOnce([&](auto*, auto* stream) {
          StreamMessageRequest actual_request;
          EXPECT_TRUE(stream->Read(&actual_request));
          EXPECT_THAT(actual_request, EqualsProto(modified_request));
          EXPECT_FALSE(stream->Read(&actual_request));
          EXPECT_TRUE(stream->Write(response));
          return grpc::Status::OK;
        });
    grpc::ClientContext context;
    StreamMessageResponse actual_response;
    auto stream = stub->StreamChannel(&context);
    EXPECT_TRUE(stream->Write(request));
    EXPECT_TRUE(stream->WritesDone());
    EXPECT_TRUE(stream->Read(&actual_response));
    EXPECT_THAT(actual_response, EqualsProto(modified_response));
    EXPECT_FALSE(stream->Read(&actual_response));
  }
}

}  // namespace
}  // namespace p4_runtime
