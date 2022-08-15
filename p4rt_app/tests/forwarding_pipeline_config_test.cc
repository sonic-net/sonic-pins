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
#include <cstdlib>
#include <memory>
#include <optional>
#include <string>
#include <utility>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/ascii.h"
#include "absl/strings/str_cat.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "google/protobuf/repeated_field.h"
#include "grpcpp/client_context.h"
#include "grpcpp/security/credentials.h"
#include "grpcpp/support/status.h"
#include "gtest/gtest.h"
#include "gutil/proto.h"
#include "gutil/proto_matchers.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/tests/lib/p4runtime_grpc_service.h"
#include "p4rt_app/tests/lib/p4runtime_request_helpers.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_p4info_fetcher.h"

namespace p4rt_app {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::p4::v1::GetForwardingPipelineConfigRequest;
using ::p4::v1::GetForwardingPipelineConfigResponse;
using ::p4::v1::SetForwardingPipelineConfigRequest;
using ::p4::v1::SetForwardingPipelineConfigResponse;
using ::testing::IsEmpty;
using ::testing::Not;

MATCHER_P(GrpcStatusIs, status_code, "") {
  return arg.error_code() == status_code;
}

// Get a writeable directory where bazel tests can save output files to.
// https://docs.bazel.build/versions/main/test-encyclopedia.html#initial-conditions
absl::StatusOr<std::string> GetTestTmpDir() {
  char* test_tmpdir = std::getenv("TEST_TMPDIR");
  if (test_tmpdir == nullptr) {
    return gutil::InternalErrorBuilder()
           << "Could not find environment variable ${TEST_TMPDIR}. Is this a "
              "bazel test run?";
  }
  return test_tmpdir;
}

class ForwardingPipelineConfigTest : public testing::Test {
 protected:
  void SetUp() override {
    // Configure the P4RT session to save the P4Info to a file.
    ASSERT_OK_AND_ASSIGN(std::string test_tmpdir, GetTestTmpDir());
    config_save_path_ = absl::StrCat(test_tmpdir, "/forwarding_config.pb.txt");

    // The config file should not exist before running a test. We expect all
    // tests to cleanup their state.
    ASSERT_NE(GetSavedConfig().status(), absl::OkStatus());

    ASSERT_OK(ResetGrpcServerAndClient());
  }

  void TearDown() override {
    // If a test created a config file we try to clean it up at teardown.
    if (GetSavedConfig().status().ok() &&
        std::remove(config_save_path_->c_str()) != 0) {
      FAIL() << "Could not remove file: " << *config_save_path_;
    }
  }

  absl::Status ResetGrpcServerAndClient() {
    uint64_t device_id = 100500;

    // The P4RT service will wait for the client to close before stopping.
    // Therefore, we need to close the client connection first if it exists.
    if (p4rt_session_ != nullptr) RETURN_IF_ERROR(p4rt_session_->Finish());

    // Restart a new P4RT service.
    p4rt_service_ =
        std::make_unique<test_lib::P4RuntimeGrpcService>(P4RuntimeImplOptions{
            .forwarding_config_full_path = config_save_path_,
        });
    RETURN_IF_ERROR(p4rt_service_->GetP4rtServer().UpdateDeviceId(device_id));

    // Reset the P4RT client.
    std::string address = absl::StrCat("localhost:", p4rt_service_->GrpcPort());
    LOG(INFO) << "Opening P4RT connection to " << address << ".";
    auto stub =
        pdpi::CreateP4RuntimeStub(address, grpc::InsecureChannelCredentials());
    ASSIGN_OR_RETURN(p4rt_session_, pdpi::P4RuntimeSession::Create(
                                        std::move(stub), device_id));

    return absl::OkStatus();
  }

  absl::Status SaveConfigFile(const p4::v1::ForwardingPipelineConfig& config) {
    if (!config_save_path_.has_value()) {
      return gutil::FailedPreconditionErrorBuilder()
             << "Save path is not set for the config.";
    }
    return gutil::SaveProtoToFile(*config_save_path_, config);
  }

  absl::StatusOr<p4::v1::ForwardingPipelineConfig> GetSavedConfig() {
    if (!config_save_path_.has_value()) {
      return gutil::FailedPreconditionErrorBuilder()
             << "Save path is not set for the config.";
    }

    p4::v1::ForwardingPipelineConfig config;
    RETURN_IF_ERROR(gutil::ReadProtoFromFile(*config_save_path_, &config));
    return config;
  }

  // SetForwardingPipelineConfig will reject any flow that doesn't have an
  // expected 'device ID', 'role', or 'election ID'. Since this information is
  // irrelevant to these test we use a helper function to simplify setup.
  SetForwardingPipelineConfigRequest GetBasicForwardingRequest() {
    SetForwardingPipelineConfigRequest request;
    request.set_device_id(p4rt_session_->DeviceId());
    request.set_role(p4rt_session_->Role());
    *request.mutable_election_id() = p4rt_session_->ElectionId();
    return request;
  }

  // File path for where the forwarding config is saved.
  std::optional<std::string> config_save_path_;

  // A fake P4RT gRPC service to run tests against.
  std::unique_ptr<test_lib::P4RuntimeGrpcService> p4rt_service_;

  // A gRPC client session to send and receive gRPC calls.
  std::unique_ptr<pdpi::P4RuntimeSession> p4rt_session_;
};

using VerifyTest = ForwardingPipelineConfigTest;

TEST_F(VerifyTest, DoesNotUpdateAppDbState) {
  // By using the "middleblock" config we expect the ACL table definitions to
  // be written into the AppDb during a config push.
  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::VERIFY);
  *request.mutable_config()->mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  // However, since we're only verifying the config we should not see anything
  // being written to the AppDb tables.
  SetForwardingPipelineConfigResponse response;
  grpc::ClientContext context;
  // This is the first test that runs verify against the P4info so it's the most
  // visible failure. Therefore, annotate this failure with suggestions for
  // fixing verification issues.
  EXPECT_OK(p4rt_session_->Stub().SetForwardingPipelineConfig(&context, request,
                                                              &response))
      << "Is the p4info_verification_schema updated? If not, run: "
      << "p4rt_app/scripts/"
      << "update_p4info_verification_schema.sh";
  EXPECT_THAT(p4rt_service_->GetP4rtAppDbTable().GetAllKeys(), IsEmpty());
}

TEST_F(VerifyTest, FailsWhenNoConfigIsSet) {
  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::VERIFY);

  SetForwardingPipelineConfigResponse response;
  grpc::ClientContext context;
  EXPECT_THAT(p4rt_session_->Stub().SetForwardingPipelineConfig(
                  &context, request, &response),
              GrpcStatusIs(grpc::StatusCode::INVALID_ARGUMENT));
}

TEST_F(VerifyTest, FailsWhenVerifyFails) {
  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::VERIFY);
  *request.mutable_config()->mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);
  request.mutable_config()->mutable_p4info()->clear_actions();

  SetForwardingPipelineConfigResponse response;
  grpc::ClientContext context;
  EXPECT_THAT(p4rt_session_->Stub().SetForwardingPipelineConfig(
                  &context, request, &response),
              GrpcStatusIs(grpc::StatusCode::INVALID_ARGUMENT));
}

using VerifyAndCommitTest = ForwardingPipelineConfigTest;

TEST_F(VerifyAndCommitTest, UpdatesAppDbState) {
  // By using the "middleblock" config we expect the ACL table definitionss to
  // be written into the AppDb during a config push.
  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::VERIFY_AND_COMMIT);
  *request.mutable_config()->mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  // Since we're both verifying and committing the config we expect to see
  // changes to the AppDb tables.
  SetForwardingPipelineConfigResponse response;
  grpc::ClientContext context;
  EXPECT_OK(p4rt_session_->Stub().SetForwardingPipelineConfig(&context, request,
                                                              &response));
  EXPECT_THAT(p4rt_service_->GetP4rtAppDbTable().GetAllKeys(), Not(IsEmpty()));
}

TEST_F(VerifyAndCommitTest, FailsWhenNoConfigIsSet) {
  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::VERIFY_AND_COMMIT);

  SetForwardingPipelineConfigResponse response;
  grpc::ClientContext context;
  EXPECT_THAT(p4rt_session_->Stub().SetForwardingPipelineConfig(
                  &context, request, &response),
              GrpcStatusIs(grpc::StatusCode::INVALID_ARGUMENT));
}

// This is not expected P4Runtime behavior. We simply haven't implemented it
// today, and currently have no plans to.
TEST_F(VerifyAndCommitTest, CannotClearForwardingState) {
  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::VERIFY_AND_COMMIT);
  *request.mutable_config()->mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  // For the first config push we expect everything to pass since the switch is
  // in a clean state.
  {
    SetForwardingPipelineConfigResponse response;
    grpc::ClientContext context;
    ASSERT_OK(p4rt_session_->Stub().SetForwardingPipelineConfig(
        &context, request, &response));
  }

  // Because we don't support it today we fail when trying to push the same
  // config a second time.
  {
    SetForwardingPipelineConfigResponse response;
    grpc::ClientContext context;
    EXPECT_THAT(p4rt_session_->Stub().SetForwardingPipelineConfig(
                    &context, request, &response),
                GrpcStatusIs(grpc::StatusCode::UNIMPLEMENTED));
  }
}

using CommitTest = ForwardingPipelineConfigTest;

TEST_F(CommitTest, LoadsLastSavedConfig) {
  // First we need to save the config.
  p4::v1::ForwardingPipelineConfig expected_config;
  *expected_config.mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);
  ASSERT_OK(SaveConfigFile(expected_config));

  // Then we'll load the saved config with the COMMIT action.
  SetForwardingPipelineConfigRequest load_request = GetBasicForwardingRequest();
  load_request.set_action(SetForwardingPipelineConfigRequest::COMMIT);

  // Finally we'll verify we can read back the saved request.
  GetForwardingPipelineConfigRequest get_request;
  get_request.set_device_id(p4rt_session_->DeviceId());

  SetForwardingPipelineConfigResponse load_response;
  grpc::ClientContext load_context;
  ASSERT_OK(p4rt_session_->Stub().SetForwardingPipelineConfig(
      &load_context, load_request, &load_response));

  GetForwardingPipelineConfigResponse get_response;
  grpc::ClientContext get_context;
  EXPECT_OK(p4rt_session_->Stub().GetForwardingPipelineConfig(
      &get_context, get_request, &get_response));
  EXPECT_THAT(get_response.config(), EqualsProto(expected_config));
}

TEST_F(CommitTest, FailsIfNoConfigHasBeenSaved) {
  // If the file exists before this test for any reason then this test is
  // pointless.
  ASSERT_EQ(GetSavedConfig().status().code(),
            absl::StatusCode::kInvalidArgument)
      << "This test requires the config file to not be saved before running.";

  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::COMMIT);

  SetForwardingPipelineConfigResponse response;
  grpc::ClientContext context;
  EXPECT_THAT(p4rt_session_->Stub().SetForwardingPipelineConfig(
                  &context, request, &response),
              GrpcStatusIs(grpc::StatusCode::INVALID_ARGUMENT));
}

TEST_F(CommitTest, FailsIfAConfigIsSet) {
  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::COMMIT);
  *request.mutable_config()->mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  SetForwardingPipelineConfigResponse response;
  grpc::ClientContext context;
  EXPECT_THAT(p4rt_session_->Stub().SetForwardingPipelineConfig(
                  &context, request, &response),
              GrpcStatusIs(grpc::StatusCode::INVALID_ARGUMENT));
}

using ReconcileAndCommitTest = ForwardingPipelineConfigTest;

TEST_F(ReconcileAndCommitTest, SetForwardingPipelineConfig) {
  SetForwardingPipelineConfigRequest commit_request =
      GetBasicForwardingRequest();
  commit_request.set_action(
      SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT);
  *commit_request.mutable_config()->mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  GetForwardingPipelineConfigRequest get_request;
  get_request.set_device_id(p4rt_session_->DeviceId());

  SetForwardingPipelineConfigResponse commit_response;
  grpc::ClientContext commit_context;
  EXPECT_OK(p4rt_session_->Stub().SetForwardingPipelineConfig(
      &commit_context, commit_request, &commit_response));

  GetForwardingPipelineConfigResponse get_response;
  grpc::ClientContext get_context;
  EXPECT_OK(p4rt_session_->Stub().GetForwardingPipelineConfig(
      &get_context, get_request, &get_response));
  EXPECT_THAT(get_response.config(), EqualsProto(commit_request.config()));
}

TEST_F(ReconcileAndCommitTest, WritesConfigToAFile) {
  SetForwardingPipelineConfigRequest request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT);
  *request.mutable_config()->mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  SetForwardingPipelineConfigResponse response;
  grpc::ClientContext context;
  ASSERT_OK(p4rt_session_->Stub().SetForwardingPipelineConfig(&context, request,
                                                              &response));

  EXPECT_THAT(GetSavedConfig(), IsOkAndHolds(EqualsProto(request.config())));
}

TEST_F(ReconcileAndCommitTest, FailsWhenNoConfigIsSet) {
  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT);

  SetForwardingPipelineConfigResponse response;
  grpc::ClientContext context;
  EXPECT_THAT(p4rt_session_->Stub().SetForwardingPipelineConfig(
                  &context, request, &response),
              GrpcStatusIs(grpc::StatusCode::INVALID_ARGUMENT));
}

TEST_F(ReconcileAndCommitTest, SetDuplicateForwardingPipelineConfig) {
  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT);
  *request.mutable_config()->mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  SetForwardingPipelineConfigResponse response;
  grpc::ClientContext context;
  ASSERT_OK(p4rt_session_->Stub().SetForwardingPipelineConfig(&context, request,
                                                              &response));

  grpc::ClientContext duplicate_context;
  EXPECT_OK(p4rt_session_->Stub().SetForwardingPipelineConfig(
      &duplicate_context, request, &response));
}

TEST_F(ReconcileAndCommitTest, FailsIfAModifiedConfigIsPushed) {
  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT);
  *request.mutable_config()->mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  SetForwardingPipelineConfigResponse response;
  grpc::ClientContext context;
  ASSERT_OK(p4rt_session_->Stub().SetForwardingPipelineConfig(&context, request,
                                                              &response));

  // Remove the last table from the P4Info, and try pushing again.
  request.mutable_config()->mutable_p4info()->mutable_tables()->RemoveLast();
  grpc::ClientContext modify_context;
  EXPECT_THAT(p4rt_session_->Stub().SetForwardingPipelineConfig(
                  &modify_context, request, &response),
              GrpcStatusIs(grpc::StatusCode::UNIMPLEMENTED));
}

using GetForwardingConfigTest = ForwardingPipelineConfigTest;

TEST_F(GetForwardingConfigTest, ReturnsNothingIfConfigHasNotBeenSet) {
  GetForwardingPipelineConfigRequest get_request;
  get_request.set_device_id(p4rt_session_->DeviceId());
  get_request.set_response_type(GetForwardingPipelineConfigRequest::ALL);

  GetForwardingPipelineConfigResponse get_response;
  grpc::ClientContext get_context;
  EXPECT_OK(p4rt_session_->Stub().GetForwardingPipelineConfig(
      &get_context, get_request, &get_response));
  EXPECT_THAT(get_response.config(),
              EqualsProto(p4::v1::ForwardingPipelineConfig{}));
}

TEST_F(GetForwardingConfigTest, CanReadBackAllTheConfig) {
  auto set_request = GetBasicForwardingRequest();
  set_request.set_action(
      SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT);
  set_request.mutable_config()->mutable_cookie()->set_cookie(123);
  *set_request.mutable_config()->mutable_p4_device_config() = "abc";
  *set_request.mutable_config()->mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  // Read back all parts of the forwarding config.
  GetForwardingPipelineConfigRequest get_request;
  get_request.set_device_id(p4rt_session_->DeviceId());
  get_request.set_response_type(GetForwardingPipelineConfigRequest::ALL);

  SetForwardingPipelineConfigResponse set_response;
  grpc::ClientContext set_context;
  ASSERT_OK(p4rt_session_->Stub().SetForwardingPipelineConfig(
      &set_context, set_request, &set_response));

  GetForwardingPipelineConfigResponse get_response;
  grpc::ClientContext get_context;
  EXPECT_OK(p4rt_session_->Stub().GetForwardingPipelineConfig(
      &get_context, get_request, &get_response));
  EXPECT_THAT(get_response.config(), EqualsProto(set_request.config()));
}

TEST_F(GetForwardingConfigTest, CanReadBackCookieOnly) {
  auto set_request = GetBasicForwardingRequest();
  set_request.set_action(
      SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT);
  set_request.mutable_config()->mutable_cookie()->set_cookie(123);
  *set_request.mutable_config()->mutable_p4_device_config() = "abc";
  *set_request.mutable_config()->mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  // Read back just the cookie value.
  GetForwardingPipelineConfigRequest get_request;
  get_request.set_device_id(p4rt_session_->DeviceId());
  get_request.set_response_type(
      GetForwardingPipelineConfigRequest::COOKIE_ONLY);

  // Expect to see just the cookie being set.
  p4::v1::ForwardingPipelineConfig expected_config;
  expected_config.mutable_cookie()->set_cookie(123);

  SetForwardingPipelineConfigResponse set_response;
  grpc::ClientContext set_context;
  ASSERT_OK(p4rt_session_->Stub().SetForwardingPipelineConfig(
      &set_context, set_request, &set_response));

  GetForwardingPipelineConfigResponse get_response;
  grpc::ClientContext get_context;
  EXPECT_OK(p4rt_session_->Stub().GetForwardingPipelineConfig(
      &get_context, get_request, &get_response));
  EXPECT_THAT(get_response.config(), EqualsProto(expected_config));
}

TEST_F(GetForwardingConfigTest, CanReadBackP4InfoAndCookie) {
  auto set_request = GetBasicForwardingRequest();
  set_request.set_action(
      SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT);
  set_request.mutable_config()->mutable_cookie()->set_cookie(123);
  *set_request.mutable_config()->mutable_p4_device_config() = "abc";
  *set_request.mutable_config()->mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  // Read back just the p4info and the cookie values.
  GetForwardingPipelineConfigRequest get_request;
  get_request.set_device_id(p4rt_session_->DeviceId());
  get_request.set_response_type(
      GetForwardingPipelineConfigRequest::P4INFO_AND_COOKIE);

  // Expect to see just the cookie and the p4info being set.
  p4::v1::ForwardingPipelineConfig expected_config;
  *expected_config.mutable_cookie() = set_request.config().cookie();
  *expected_config.mutable_p4info() = set_request.config().p4info();

  SetForwardingPipelineConfigResponse set_response;
  grpc::ClientContext set_context;
  ASSERT_OK(p4rt_session_->Stub().SetForwardingPipelineConfig(
      &set_context, set_request, &set_response));

  GetForwardingPipelineConfigResponse get_response;
  grpc::ClientContext get_context;
  EXPECT_OK(p4rt_session_->Stub().GetForwardingPipelineConfig(
      &get_context, get_request, &get_response));
  EXPECT_THAT(get_response.config(), EqualsProto(expected_config));
}

TEST_F(GetForwardingConfigTest, CanReadBackDeviceConfigAndCookie) {
  auto set_request = GetBasicForwardingRequest();
  set_request.set_action(
      SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT);
  set_request.mutable_config()->mutable_cookie()->set_cookie(123);
  *set_request.mutable_config()->mutable_p4_device_config() = "abc";
  *set_request.mutable_config()->mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  // Read back just the device config and the cookie values.
  GetForwardingPipelineConfigRequest get_request;
  get_request.set_device_id(p4rt_session_->DeviceId());
  get_request.set_response_type(
      GetForwardingPipelineConfigRequest::DEVICE_CONFIG_AND_COOKIE);

  // Expect to see just the device config and the cookie set.
  p4::v1::ForwardingPipelineConfig expected_config;
  *expected_config.mutable_cookie() = set_request.config().cookie();
  *expected_config.mutable_p4_device_config() =
      set_request.config().p4_device_config();

  SetForwardingPipelineConfigResponse set_response;
  grpc::ClientContext set_context;
  ASSERT_OK(p4rt_session_->Stub().SetForwardingPipelineConfig(
      &set_context, set_request, &set_response));

  GetForwardingPipelineConfigResponse get_response;
  grpc::ClientContext get_context;
  EXPECT_OK(p4rt_session_->Stub().GetForwardingPipelineConfig(
      &get_context, get_request, &get_response));
  EXPECT_THAT(get_response.config(), EqualsProto(expected_config));
}

TEST_F(GetForwardingConfigTest, CanUpdateTheConfigAndReadItBack) {
  auto set_request = GetBasicForwardingRequest();
  set_request.set_action(
      SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT);
  set_request.mutable_config()->mutable_cookie()->set_cookie(123);
  *set_request.mutable_config()->mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  // Set the forwarding pipeline.
  {
    SetForwardingPipelineConfigResponse set_response;
    grpc::ClientContext set_context;
    ASSERT_OK(p4rt_session_->Stub().SetForwardingPipelineConfig(
        &set_context, set_request, &set_response));
  }

  // Verify we can read the same forwarding config back.
  {
    GetForwardingPipelineConfigRequest get_request;
    get_request.set_device_id(p4rt_session_->DeviceId());
    GetForwardingPipelineConfigResponse get_response;
    grpc::ClientContext get_context;
    EXPECT_OK(p4rt_session_->Stub().GetForwardingPipelineConfig(
        &get_context, get_request, &get_response));
    EXPECT_THAT(get_response.config(), EqualsProto(set_request.config()));
  }

  // Update the forwarding config's cookie, and reset it.
  set_request.mutable_config()->mutable_cookie()->set_cookie(456);
  {
    SetForwardingPipelineConfigResponse set_response;
    grpc::ClientContext set_context;
    ASSERT_OK(p4rt_session_->Stub().SetForwardingPipelineConfig(
        &set_context, set_request, &set_response));
  }

  // Verify we can read back the new forwarding config.
  {
    GetForwardingPipelineConfigRequest get_request;
    get_request.set_device_id(p4rt_session_->DeviceId());
    GetForwardingPipelineConfigResponse get_response;
    grpc::ClientContext get_context;
    EXPECT_OK(p4rt_session_->Stub().GetForwardingPipelineConfig(
        &get_context, get_request, &get_response));
    EXPECT_THAT(get_response.config(), EqualsProto(set_request.config()));
  }
}

TEST_F(ForwardingPipelineConfigTest,
       DISABLED_RejectWriteRequestsIfForwardingPipelineConfigFails) {
  auto p4_info = sai::GetP4Info(sai::Instantiation::kMiddleblock);
  auto ir_p4_info = sai::GetIrP4Info(sai::Instantiation::kMiddleblock);

  // Generate error from the OrchAgent layer when programming the PRE_INGRESS
  // ACL table.
  p4rt_service_->GetP4rtAppDbTable().SetResponseForKey(
      "DEFINITION:ACL_ACL_PRE_INGRESS_TABLE", "SWSS_RC_INVALID_PARAM",
      "my error message");
  ASSERT_THAT(pdpi::SetMetadataAndSetForwardingPipelineConfig(
                  p4rt_session_.get(),
                  SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
                  sai::GetP4Info(sai::Instantiation::kMiddleblock)),
              StatusIs(absl::StatusCode::kInternal));

  // Because we failed to program the forwarding pipeline config we should not
  // be able to write to the table.
  p4::v1::WriteRequest request;
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kInternal));
}

class PerConfigTest : public ForwardingPipelineConfigTest,
                      public testing::WithParamInterface<
                          std::tuple<sai::Instantiation, sai::ClosStage> > {};

TEST_P(PerConfigTest, VerifySucceeds) {
  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::VERIFY);
  *request.mutable_config()->mutable_p4info() =
      sai::FetchP4Info(std::get<0>(GetParam()), std::get<1>(GetParam()));

  SetForwardingPipelineConfigResponse response;
  grpc::ClientContext context;
  EXPECT_OK(p4rt_session_->Stub().SetForwardingPipelineConfig(&context, request,
                                                              &response));
}

TEST_P(PerConfigTest, VerifyAndCommitSucceeds) {
  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::VERIFY_AND_COMMIT);
  *request.mutable_config()->mutable_p4info() =
      sai::FetchP4Info(std::get<0>(GetParam()), std::get<1>(GetParam()));

  SetForwardingPipelineConfigResponse response;
  grpc::ClientContext context;
  EXPECT_OK(p4rt_session_->Stub().SetForwardingPipelineConfig(&context, request,
                                                              &response));
  EXPECT_THAT(p4rt_service_->GetP4rtAppDbTable().GetAllKeys(), Not(IsEmpty()));
}

TEST_P(PerConfigTest, ReconcileAndCommitSucceeds) {
  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT);
  *request.mutable_config()->mutable_p4info() =
      sai::FetchP4Info(std::get<0>(GetParam()), std::get<1>(GetParam()));

  SetForwardingPipelineConfigResponse response;
  {
    grpc::ClientContext context;
    EXPECT_OK(p4rt_session_->Stub().SetForwardingPipelineConfig(
        &context, request, &response));
  }
  EXPECT_THAT(p4rt_service_->GetP4rtAppDbTable().GetAllKeys(), Not(IsEmpty()));
  {
    grpc::ClientContext context;
    EXPECT_OK(p4rt_session_->Stub().SetForwardingPipelineConfig(
        &context, request, &response))
        << "Failed second commit (expected no-op)";
  }
  EXPECT_THAT(p4rt_service_->GetP4rtAppDbTable().GetAllKeys(), Not(IsEmpty()));
}

// Generate the test case name for an <Instantiation, ClosStage> tuple.
// The generated test name is in CamelCase.
// Example: FabricBorderRouterStage3
std::string PerConfigTestCaseName(
    testing::TestParamInfo<PerConfigTest::ParamType> param_info) {
  bool to_upper = true;
  std::string test_name;

  // InstantiationToString returns strings with underscore. Swap to CamelCase.
  // Example: fabric_border_router -> FabricBorderRouter
  for (char c : sai::InstantiationToString(std::get<0>(param_info.param))) {
    if (c == '_') {
      to_upper = true;
    } else {
      test_name.push_back(to_upper ? absl::ascii_toupper(c) : c);
      to_upper = false;
    }
  }
  test_name.append(sai::ClosStageToString(std::get<1>(param_info.param)));
  return test_name;
}

INSTANTIATE_TEST_SUITE_P(
    ForwardingPipelineConfig, PerConfigTest,
    testing::Combine(testing::ValuesIn(sai::AllInstantiations()),
                     testing::ValuesIn(sai::AllStages())),
    PerConfigTestCaseName);

}  // namespace
}  // namespace p4rt_app
