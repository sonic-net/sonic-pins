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

#ifndef PINS_P4_INFRA_P4_RUNTIME_P4_RUNTIME_CLIENT_INTERCEPTOR_H_
#define PINS_P4_INFRA_P4_RUNTIME_P4_RUNTIME_CLIENT_INTERCEPTOR_H_

#include "grpcpp/support/client_interceptor.h"
#include "grpcpp/support/interceptor.h"
#include "p4/v1/p4runtime.pb.h"

namespace p4_runtime {

// Base class for intercepting P4Runtime RPC requests and responses on the
// client side.
//
// Allows intercepting (and optionally, modifying) requests and responses in a
// way that is transparent to the client and server.
//
// To implement your own interceptor, inherit from this base class and override
// (a subset of) the overloads of the virtual methods `InterceptRequest` and
// `InterceptResponse` as desired. By default, this base class performs no
// interception actions.
//
// To apply this interceptor, create a gRPC channel via the method
// `CreateCustomChannelWithInterceptors`. Then create a P4Runtime stub using
// that channel.
class P4RuntimeClientInterceptor
    : public grpc::experimental::ClientInterceptorFactoryInterface {
 public:
  // Called whenever client makes a `request`.
  // Returns modified `request`, or `nullptr` to leave the `request` unmodified.
  virtual std::unique_ptr<p4::v1::WriteRequest> InterceptRequest(
      const p4::v1::WriteRequest& request) {
    return nullptr;
  }
  virtual std::unique_ptr<p4::v1::ReadRequest> InterceptRequest(
      const p4::v1::ReadRequest& request) {
    return nullptr;
  }
  virtual std::unique_ptr<p4::v1::SetForwardingPipelineConfigRequest>
  InterceptRequest(const p4::v1::SetForwardingPipelineConfigRequest& request) {
    return nullptr;
  }
  virtual std::unique_ptr<p4::v1::GetForwardingPipelineConfigRequest>
  InterceptRequest(const p4::v1::GetForwardingPipelineConfigRequest& request) {
    return nullptr;
  }
  virtual std::unique_ptr<p4::v1::StreamMessageRequest> InterceptRequest(
      const p4::v1::StreamMessageRequest& request) {
    return nullptr;
  }

  // Called whenever client receives a response.
  // May mutate the response, causing client to receive modified response.
  virtual void InterceptResponse(p4::v1::WriteResponse& response) {}
  virtual void InterceptResponse(p4::v1::ReadResponse& response) {}
  virtual void InterceptResponse(
      p4::v1::SetForwardingPipelineConfigResponse& response) {}
  virtual void InterceptResponse(
      p4::v1::GetForwardingPipelineConfigResponse& response) {}
  virtual void InterceptResponse(p4::v1::StreamMessageResponse& response) {}

  virtual ~P4RuntimeClientInterceptor() = default;

 private:
  // Implementation detail, to satisfy `ClientInterceptorFactoryInterface`.
  grpc::experimental::Interceptor* CreateClientInterceptor(
      grpc::experimental::ClientRpcInfo* info) final;
};

}  // namespace p4_runtime

#endif  // PINS_P4_INFRA_P4_RUNTIME_P4_RUNTIME_CLIENT_INTERCEPTOR_H_
