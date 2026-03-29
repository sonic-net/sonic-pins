// Copyright 2026 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "fourward/fake_gnmi_service.h"

#include <memory>
#include <string>
#include <vector>

#include "github.com/openconfig/gnmi/proto/gnmi/gnmi.grpc.pb.h"
#include "github.com/openconfig/gnmi/proto/gnmi/gnmi.pb.h"
#include "gmock/gmock.h"
#include "grpcpp/channel.h"
#include "grpcpp/client_context.h"
#include "grpcpp/create_channel.h"
#include "grpcpp/security/credentials.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"

namespace dvaas {
namespace {

using ::testing::HasSubstr;
using ::testing::Not;

TEST(FakeGnmiServerTest, CreateSucceeds) {
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<FakeGnmiServer> server,
                        FakeGnmiServer::Create());
  EXPECT_THAT(server->Address(), HasSubstr("localhost:"));
}

TEST(FakeGnmiServerTest, GetStateReturnsInterfaces) {
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<FakeGnmiServer> server,
                        FakeGnmiServer::Create());

  std::shared_ptr<grpc::Channel> channel = grpc::CreateChannel(
      server->Address(), grpc::InsecureChannelCredentials());
  std::unique_ptr<gnmi::gNMI::Stub> stub = gnmi::gNMI::NewStub(channel);

  grpc::ClientContext context;
  gnmi::GetRequest request;
  request.set_type(gnmi::GetRequest::STATE);
  gnmi::GetResponse response;
  grpc::Status status = stub->Get(&context, request, &response);

  ASSERT_TRUE(status.ok()) << status.error_message();
  ASSERT_GE(response.notification_size(), 1);
  ASSERT_GE(response.notification(0).update_size(), 1);
  std::string json = response.notification(0).update(0).val().json_ietf_val();

  // Default interfaces: Ethernet0..Ethernet7 with p4rt IDs 1..8.
  EXPECT_THAT(json, HasSubstr("Ethernet0"));
  EXPECT_THAT(json, HasSubstr("Ethernet7"));
  EXPECT_THAT(json, HasSubstr("oper-status"));
  EXPECT_THAT(json, HasSubstr("openconfig-p4rt:id"));
}

TEST(FakeGnmiServerTest, GetConfigReturnsInterfaces) {
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<FakeGnmiServer> server,
                        FakeGnmiServer::Create());

  std::shared_ptr<grpc::Channel> channel = grpc::CreateChannel(
      server->Address(), grpc::InsecureChannelCredentials());
  std::unique_ptr<gnmi::gNMI::Stub> stub = gnmi::gNMI::NewStub(channel);

  grpc::ClientContext context;
  gnmi::GetRequest request;
  request.set_type(gnmi::GetRequest::CONFIG);
  gnmi::GetResponse response;
  grpc::Status status = stub->Get(&context, request, &response);

  ASSERT_TRUE(status.ok()) << status.error_message();
  ASSERT_GE(response.notification_size(), 1);
  std::string json = response.notification(0).update(0).val().json_ietf_val();
  EXPECT_THAT(json, HasSubstr("Ethernet0"));
  // Config uses "config" key, not "state".
  EXPECT_THAT(json, HasSubstr(R"("config":)"));
}

TEST(FakeGnmiServerTest, SetAcceptedSilently) {
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<FakeGnmiServer> server,
                        FakeGnmiServer::Create());

  std::shared_ptr<grpc::Channel> channel = grpc::CreateChannel(
      server->Address(), grpc::InsecureChannelCredentials());
  std::unique_ptr<gnmi::gNMI::Stub> stub = gnmi::gNMI::NewStub(channel);

  grpc::ClientContext context;
  gnmi::SetRequest request;
  gnmi::SetResponse response;
  grpc::Status status = stub->Set(&context, request, &response);
  EXPECT_TRUE(status.ok()) << status.error_message();
}

TEST(FakeGnmiServerTest, CustomInterfaces) {
  std::vector<FakeInterface> interfaces = {
      {.name = "Ethernet42", .p4rt_id = 42},
  };
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<FakeGnmiServer> server,
                        FakeGnmiServer::Create(interfaces));

  std::shared_ptr<grpc::Channel> channel = grpc::CreateChannel(
      server->Address(), grpc::InsecureChannelCredentials());
  std::unique_ptr<gnmi::gNMI::Stub> stub = gnmi::gNMI::NewStub(channel);

  grpc::ClientContext context;
  gnmi::GetRequest request;
  request.set_type(gnmi::GetRequest::STATE);
  gnmi::GetResponse response;
  grpc::Status status = stub->Get(&context, request, &response);

  ASSERT_TRUE(status.ok()) << status.error_message();
  std::string json = response.notification(0).update(0).val().json_ietf_val();
  EXPECT_THAT(json, HasSubstr("Ethernet42"));
  // Default interfaces should NOT be present.
  EXPECT_THAT(json, Not(HasSubstr("Ethernet0")));
}

}  // namespace
}  // namespace dvaas
