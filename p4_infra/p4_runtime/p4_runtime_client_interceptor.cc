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

#include "absl/cleanup/cleanup.h"
#include "absl/log/log.h"
#include "grpcpp/support/client_interceptor.h"
#include "grpcpp/support/interceptor.h"
#include "net/google::protobuf/public/message.h"
#include "p4/v1/p4runtime.pb.h"

namespace p4_runtime {

namespace {

using ::grpc::experimental::ClientRpcInfo;
using ::grpc::experimental::InterceptionHookPoints;
using ::grpc::experimental::Interceptor;
using ::grpc::experimental::InterceptorBatchMethods;
using ::p4::v1::GetForwardingPipelineConfigRequest;
using ::p4::v1::GetForwardingPipelineConfigResponse;
using ::p4::v1::ReadRequest;
using ::p4::v1::ReadResponse;
using ::p4::v1::SetForwardingPipelineConfigRequest;
using ::p4::v1::SetForwardingPipelineConfigResponse;
using ::p4::v1::StreamMessageRequest;
using ::p4::v1::StreamMessageResponse;
using ::p4::v1::WriteRequest;
using ::p4::v1::WriteResponse;

// Intercepts the given `request` using the appropriate overload of
// `interceptor.InterceptRequest` based on the type of the `request`.
std::unique_ptr<google::protobuf::Message> InterceptRequest(
    const google::protobuf::Message& request,
    P4RuntimeClientInterceptor& interceptor) {
  // Branch on request type via dynamic type casting.
  auto* write_request =
      google::protobuf::DynamicCastMessage<WriteRequest>(&request);
  auto* read_request =
      google::protobuf::DynamicCastMessage<ReadRequest>(&request);
  auto* set_config_request =
      google::protobuf::DynamicCastMessage<SetForwardingPipelineConfigRequest>(
          &request);
  auto* get_config_request =
      google::protobuf::DynamicCastMessage<GetForwardingPipelineConfigRequest>(
          &request);
  auto* stream_request =
      google::protobuf::DynamicCastMessage<StreamMessageRequest>(&request);

  if (write_request != nullptr) {
    return interceptor.InterceptRequest(*write_request);
  } else if (read_request != nullptr) {
    return interceptor.InterceptRequest(*read_request);
  } else if (set_config_request != nullptr) {
    return interceptor.InterceptRequest(*set_config_request);
  } else if (get_config_request != nullptr) {
    return interceptor.InterceptRequest(*get_config_request);
  } else if (stream_request != nullptr) {
    return interceptor.InterceptRequest(*stream_request);
  } else {
    LOG(DFATAL) << "UNIMPLEMENTED: unknown P4Runtime request type: "
                << request.GetTypeName();
  }

  return nullptr;
}

// Intercepts the given `response` using the appropriate overload of
// `interceptor.InterceptResponse` based on the type of the `response`.
void InterceptResponse(google::protobuf::Message& response,
                       P4RuntimeClientInterceptor& interceptor) {
  // Branch on response type via dynamic type casting.
  auto* write_response =
      google::protobuf::DynamicCastMessage<WriteResponse>(&response);
  auto* read_response =
      google::protobuf::DynamicCastMessage<ReadResponse>(&response);
  auto* set_config_response =
      google::protobuf::DynamicCastMessage<SetForwardingPipelineConfigResponse>(
          &response);
  auto* get_config_response =
      google::protobuf::DynamicCastMessage<GetForwardingPipelineConfigResponse>(
          &response);
  auto* stream_response =
      google::protobuf::DynamicCastMessage<StreamMessageResponse>(&response);

  if (write_response != nullptr) {
    interceptor.InterceptResponse(*write_response);
  } else if (read_response != nullptr) {
    interceptor.InterceptResponse(*read_response);
  } else if (set_config_response != nullptr) {
    interceptor.InterceptResponse(*set_config_response);
  } else if (get_config_response != nullptr) {
    interceptor.InterceptResponse(*get_config_response);
  } else if (stream_response != nullptr) {
    interceptor.InterceptResponse(*stream_response);
  } else {
    LOG(DFATAL) << "UNIMPLEMENTED: unknown P4Runtime response type: "
                << response.GetTypeName();
  }
}

class P4RuntimeClientInterceptorImpl : public Interceptor {
 public:
  P4RuntimeClientInterceptorImpl(P4RuntimeClientInterceptor& interceptor)
      : interceptor_(interceptor) {}

  void Intercept(InterceptorBatchMethods* methods) final {
    // The RPC will not proceed until we call `Proceed`.
    // Ensure we don't forget to do this when we return.
    auto proceed = absl::Cleanup([&] { methods->Proceed(); });

    if (methods->QueryInterceptionHookPoint(
            InterceptionHookPoints::PRE_SEND_MESSAGE)) {
      auto* request = static_cast<const google::protobuf::Message*>(
          methods->GetSendMessage());
      if (request == nullptr) return;
      std::unique_ptr<google::protobuf::Message> modified_request =
          InterceptRequest(*request, interceptor_);
      if (modified_request != nullptr) {
        methods->ModifySendMessage(modified_request.get());
        // Required to ensure `modified_request` outlives serialization.
        methods->GetSerializedSendMessage();
      }
    } else if (methods->QueryInterceptionHookPoint(
                   InterceptionHookPoints::POST_RECV_MESSAGE)) {
      auto* response =
          static_cast<google::protobuf::Message*>(methods->GetRecvMessage());
      if (response != nullptr) InterceptResponse(*response, interceptor_);
    }
  };

 private:
  P4RuntimeClientInterceptor& interceptor_;
};

}  // namespace

Interceptor* P4RuntimeClientInterceptor::CreateClientInterceptor(
    ClientRpcInfo* info) {
  return new P4RuntimeClientInterceptorImpl(*this);
}

}  // namespace p4_runtime
