// Copyright 2020 Google LLC
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
#include <gtest/gtest-death-test.h>
#include <memory>
#include <string>
#include <utility>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "google/protobuf/repeated_field.h"
#include "grpcpp/client_context.h"
#include "grpcpp/security/credentials.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4rt_app/tests/lib/p4runtime_grpc_service.h"
#include "p4rt_app/tests/lib/p4runtime_request_helpers.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace p4rt_app {
namespace {

using ::gutil::StatusIs;
using ::p4::v1::GetForwardingPipelineConfigResponse;
using ::p4::v1::SetForwardingPipelineConfigRequest;
using ::p4::v1::SetForwardingPipelineConfigResponse;

class ForwardingPipelineConfigTest : public testing::Test {
 protected:
  void SetUp() override {
    std::string address = absl::StrCat("localhost:", p4rt_service_.GrpcPort());
    LOG(INFO) << "Opening P4RT connection to " << address << ".";
    auto stub =
        pdpi::CreateP4RuntimeStub(address, grpc::InsecureChannelCredentials());
    ASSERT_OK_AND_ASSIGN(
        p4rt_session_, pdpi::P4RuntimeSession::Create(std::move(stub),
                                                      /*device_id=*/183807201));
  }

  test_lib::P4RuntimeGrpcService p4rt_service_ =
      test_lib::P4RuntimeGrpcService(test_lib::P4RuntimeGrpcServiceOptions{});
  std::unique_ptr<pdpi::P4RuntimeSession> p4rt_session_;
};

TEST_F(ForwardingPipelineConfigTest, SetForwardingPipelineConfig) {
  EXPECT_OK(pdpi::SetForwardingPipelineConfig(
      p4rt_session_.get(),
      SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      sai::GetP4Info(sai::Instantiation::kMiddleblock)));
}

TEST_F(ForwardingPipelineConfigTest, GetForwardingPipelineConfig) {
  const p4::config::v1::P4Info p4_info =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);
  ASSERT_OK(pdpi::SetForwardingPipelineConfig(
      p4rt_session_.get(),
      SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT, p4_info));
  ASSERT_OK_AND_ASSIGN(GetForwardingPipelineConfigResponse response,
                       pdpi::GetForwardingPipelineConfig(
                           p4rt_session_.get(),
                           p4::v1::GetForwardingPipelineConfigRequest::ALL));

  // Ensure the P4Info we read back matches what we set.
  EXPECT_THAT(response.config().p4info(), gutil::EqualsProto(p4_info));
}

TEST_F(ForwardingPipelineConfigTest, SetDuplicateForwardingPipelineConfig) {
  auto p4_info = sai::GetP4Info(sai::Instantiation::kMiddleblock);
  EXPECT_OK(pdpi::SetForwardingPipelineConfig(
      p4rt_session_.get(),
      SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT, p4_info));
  EXPECT_OK(pdpi::SetForwardingPipelineConfig(
      p4rt_session_.get(),
      SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT, p4_info));
}

TEST_F(ForwardingPipelineConfigTest, FailVerifyAndSave) {
  pdpi::P4RuntimeSession* session = p4rt_session_.get();
  SetForwardingPipelineConfigRequest request;
  request.set_device_id(session->DeviceId());
  request.set_role(session->Role());
  *request.mutable_election_id() = session->ElectionId();
  request.set_action(SetForwardingPipelineConfigRequest::VERIFY_AND_SAVE);

  SetForwardingPipelineConfigResponse response;
  grpc::ClientContext context;
  EXPECT_THAT(
      gutil::GrpcStatusToAbslStatus(session->Stub().SetForwardingPipelineConfig(
          &context, request, &response)),
      gutil::StatusIs(absl::StatusCode::kUnimplemented));
}

TEST_F(ForwardingPipelineConfigTest, ModifyConfig) {
  auto p4_info = sai::GetP4Info(sai::Instantiation::kMiddleblock);
  EXPECT_OK(pdpi::SetForwardingPipelineConfig(
      p4rt_session_.get(),
      SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT, p4_info));
  p4_info.mutable_tables()->RemoveLast();
  EXPECT_THAT(
      pdpi::SetForwardingPipelineConfig(
          p4rt_session_.get(),
          SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT, p4_info),
      gutil::StatusIs(absl::StatusCode::kUnimplemented,
                      testing::HasSubstr("deleted: ")));
}

}  // namespace
}  // namespace p4rt_app
