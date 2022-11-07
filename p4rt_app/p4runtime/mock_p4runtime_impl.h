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
#ifndef GOOGLE_P4RT_APP_P4RUNTIME_MOCK_P4RUNTIME_IMPL_H_
#define GOOGLE_P4RT_APP_P4RUNTIME_MOCK_P4RUNTIME_IMPL_H_

#include "gmock/gmock.h"
#include "grpcpp/grpcpp.h"
#include "grpcpp/server_context.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"

namespace p4rt_app {

class MockP4RuntimeImpl final : public P4RuntimeImpl {
 public:
  MockP4RuntimeImpl()
      : P4RuntimeImpl(/*translate_port_ids=*/false) {}

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

  MOCK_METHOD(absl::Status, UpdateDeviceId, (uint64_t device_id), (override));

  MOCK_METHOD(absl::Status, AddPacketIoPort, (const std::string& port_name),
              (override));

  MOCK_METHOD(absl::Status, RemovePacketIoPort, (const std::string& port_name),
              (override));

  MOCK_METHOD(absl::Status, AddPortTranslation,
              (const std::string& port_name, const std::string& port_id),
              (override));

  MOCK_METHOD(absl::Status, RemovePortTranslation,
              (const std::string& port_name), (override));

  MOCK_METHOD(absl::Status, VerifyState, (), (override));
};

}  // namespace p4rt_app

#endif  // GOOGLE_P4RT_APP_P4RUNTIME_MOCK_P4RUNTIME_IMPL_H_
