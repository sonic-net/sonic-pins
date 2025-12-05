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
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "grpcpp/client_context.h"
#include "grpcpp/create_channel.h"
#include "grpcpp/security/credentials.h"
#include "grpcpp/support/status.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/p4runtime/queue_translator.h"
#include "p4rt_app/sonic/packetio_interface.h"
#include "p4rt_app/tests/lib/app_db_entry_builder.h"
#include "p4rt_app/tests/lib/p4runtime_grpc_service.h"
#include "p4rt_app/tests/lib/p4runtime_request_helpers.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "swss/warm_restart.h"
namespace p4rt_app {
namespace {
using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::p4::v1::SetForwardingPipelineConfigRequest;
using ::testing::ElementsAre;
using ::testing::ExplainMatchResult;
using ::testing::HasSubstr;
using ::testing::UnorderedElementsAreArray;
using P4RuntimeStream =
    ::grpc::ClientReaderWriter<p4::v1::StreamMessageRequest,
                               p4::v1::StreamMessageResponse>;

// Expects a DB to contain the provided port map.
MATCHER_P2(
    ContainsPortMap, port_name, port_id,
    absl::Substitute("Contains mapping of port_name '$0' to port id '$1'",
                     port_name, port_id)) {
  return ExplainMatchResult(
      IsOkAndHolds(ElementsAre(std::make_pair("id", port_id))),
      arg.ReadTableEntry(port_name), result_listener);
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

p4::v1::Uint128 ElectionId(int value) {
  p4::v1::Uint128 election_id;
  election_id.set_high(value);
  election_id.set_low(value);
  return election_id;
}

absl::StatusOr<p4::v1::StreamMessageResponse> SendStreamRequestAndGetResponse(
    P4RuntimeStream& stream, const p4::v1::StreamMessageRequest& request) {
  if (!stream.Write(request)) {
    return gutil::InternalErrorBuilder()
           << "Stream closed : " << stream.Finish().error_message();
  }

  p4::v1::StreamMessageResponse response;
  if (!stream.Read(&response)) {
    return gutil::InternalErrorBuilder() << "Did not receive stream response: "
                                         << stream.Finish().error_message();
  }
  return response;
}

class WarmRestartTest : public testing::Test {
 protected:
  void SetUp() override {
    // Configure the P4RT session to save the P4Info to a file.
    ASSERT_OK_AND_ASSIGN(std::string test_tmpdir, GetTestTmpDir());
    config_save_path_ = absl::StrCat(test_tmpdir, "/forwarding_config.pb.txt");

    // The config file should not exist before running a test. We expect all
    // tests to cleanup their state.
    ASSERT_NE(GetSavedConfig().status(), absl::OkStatus());

    ASSERT_OK(ResetGrpcServerAndClient(false));
  }

  void TearDown() override {
    // If a test created a config file we try to clean it up at teardown.
    if (GetSavedConfig().status().ok() &&
        std::remove(config_save_path_->c_str()) != 0) {
      FAIL() << "Could not remove file: " << *config_save_path_;
    }
  }

  void SetUpControllerRpcStubs() {
    std::string address = absl::StrCat("localhost:", p4rt_service_->GrpcPort());

    auto primary_channel =
        grpc::CreateChannel(address, grpc::InsecureChannelCredentials());
    primary_stub_ = p4::v1::P4Runtime::NewStub(primary_channel);
    LOG(INFO) << "Created primary P4Runtime::Stub for " << address << ".";

    auto backup_channel =
        grpc::CreateChannel(address, grpc::InsecureChannelCredentials());
    backup_stub_ = p4::v1::P4Runtime::NewStub(backup_channel);
    LOG(INFO) << "Created backup P4Runtime::Stub for " << address << ".";
  }

  // Opens a P4RT stream, and verifies that it is the primary connection. Note
  // that the stream can still become a backup if a test updates the election
  // ID, or opens a new connection.
  absl::StatusOr<std::unique_ptr<P4RuntimeStream>> CreatePrimaryConnection(
      grpc::ClientContext& context, uint64_t device_id,
      const p4::v1::Uint128 election_id) {
    context.set_deadline(absl::ToChronoTime(absl::Now() + absl::Seconds(10)));
    context.set_wait_for_ready(true);
    auto stream = primary_stub_->StreamChannel(&context);

    // Verify that connection is the primary.
    p4::v1::StreamMessageRequest request;
    request.mutable_arbitration()->set_device_id(device_id);
    *request.mutable_arbitration()->mutable_election_id() = election_id;
    ASSIGN_OR_RETURN(p4::v1::StreamMessageResponse response,
                     SendStreamRequestAndGetResponse(*stream, request));
    if (response.arbitration().status().code() != grpc::StatusCode::OK) {
      return gutil::UnknownErrorBuilder()
             << "could not become primary. "
             << response.arbitration().status().ShortDebugString();
    }

    return stream;
  }

  // Opens a P4RT stream without an election ID so it is forced to be a backup.
  absl::StatusOr<std::unique_ptr<P4RuntimeStream>> CreateBackupConnection(
      grpc::ClientContext& context, uint64_t device_id) {
    // No test should take more than 10 seconds.
    context.set_deadline(absl::ToChronoTime(absl::Now() + absl::Seconds(10)));
    context.set_wait_for_ready(true);
    auto stream = backup_stub_->StreamChannel(&context);

    // Verify that connection is a backup.
    p4::v1::StreamMessageRequest request;
    request.mutable_arbitration()->set_device_id(device_id);
    ASSIGN_OR_RETURN(p4::v1::StreamMessageResponse response,
                     SendStreamRequestAndGetResponse(*stream, request));
    if (response.arbitration().status().code() == grpc::StatusCode::OK) {
      return gutil::UnknownErrorBuilder()
             << "could not become backup. "
             << response.arbitration().status().ShortDebugString();
    }

    return stream;
  }

  absl::Status ResetGrpcServerAndClient(bool is_freeze_mode) {
    uint64_t device_id = 100500;

    // The P4RT service will wait for the client to close before stopping.
    // Therefore, we need to close the client connection first if it exists.
    if (p4rt_session_ != nullptr) RETURN_IF_ERROR(p4rt_session_->Finish());

    if (p4rt_service_ != nullptr) {
      // Copy existing DB tables and rebuild P4RT server.
      auto p4runtime_impl = p4rt_service_->BuildP4rtServer(P4RuntimeImplOptions{
          .translate_port_ids = true,
          .is_freeze_mode = true,
          .forwarding_config_full_path = config_save_path_,
      });
      SetUpControllerRpcStubs();
      p4rt_service_->ResetP4rtServer(std::move(p4runtime_impl));
    } else {
      // Restart a new P4RT service.
      p4rt_service_ =
          std::make_unique<test_lib::P4RuntimeGrpcService>(P4RuntimeImplOptions{
              .translate_port_ids = true,
              .is_freeze_mode = is_freeze_mode,
              .forwarding_config_full_path = config_save_path_,
          });
      SetUpControllerRpcStubs();
    }
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

  std::unique_ptr<p4::v1::P4Runtime::Stub> primary_stub_;
  std::unique_ptr<p4::v1::P4Runtime::Stub> backup_stub_;
};

TEST_F(WarmRestartTest, ReconciliationSucceeds) {
  // Set forwarding config and save P4Info file
  SetForwardingPipelineConfigRequest request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT);
  *request.mutable_config()->mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kTor);

  ASSERT_OK(p4rt_session_->SetForwardingPipelineConfig(request));

  EXPECT_THAT(GetSavedConfig(), IsOkAndHolds(EqualsProto(request.config())));

  // Set port name to id mapping
  ASSERT_OK(
      p4rt_service_->GetP4rtServer().AddPortTranslation("Ethernet0", "1"));
  ASSERT_OK(
      p4rt_service_->GetP4rtServer().AddPortTranslation("Ethernet4", "2"));
  EXPECT_THAT(p4rt_service_->GetPortAppDbTable(),
              ContainsPortMap("Ethernet0", "1"));
  EXPECT_THAT(p4rt_service_->GetPortAppDbTable(),
              ContainsPortMap("Ethernet4", "2"));

  // Set CPU queue id mapping
  ASSERT_OK_AND_ASSIGN(auto translator, QueueTranslator::Create(
                                            {{"CONTROLLER_PRIORITY_1", "32"},
                                             {"CONTROLLER_PRIORITY_2", "33"}}));
  p4rt_service_->GetP4rtServer().AssignQueueTranslator(QueueType::kCpu,
                                                       std::move(translator));

  // Reset P4RT server
  EXPECT_OK(ResetGrpcServerAndClient(/*is_freeze_mode=*/true));
  // State Verification
  EXPECT_OK(p4rt_service_->GetP4rtServer().VerifyState());
}

TEST_F(WarmRestartTest, ReconciliationFailsWhenDbEntryInvalid) {
  // Set forwarding config and save P4Info file
  SetForwardingPipelineConfigRequest pipeline_request =
      GetBasicForwardingRequest();
  pipeline_request.set_action(
      SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT);
  *pipeline_request.mutable_config()->mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kTor);
  ASSERT_OK(p4rt_session_->SetForwardingPipelineConfig(pipeline_request));
  EXPECT_THAT(GetSavedConfig(),
              IsOkAndHolds(EqualsProto(pipeline_request.config())));
  EXPECT_OK(p4rt_service_->GetP4rtServer().AddPacketIoPort("Ethernet1/1/0"));
  EXPECT_OK(
      p4rt_service_->GetP4rtServer().AddPortTranslation("Ethernet1/1/0", "0"));
  EXPECT_OK(p4rt_service_->GetP4rtServer().AddPacketIoPort("Ethernet1/1/1"));
  EXPECT_OK(
      p4rt_service_->GetP4rtServer().AddPortTranslation("Ethernet1/1/1", "1"));

  // Insert invalid L3 entries
  p4rt_service_->GetP4rtAppDbTable().InsertTableEntry(
      "P4RT:FIXED_ROUTER_INTERFACE_TABLE:invalid", {});

  // State Verification fails
  EXPECT_THAT(p4rt_service_->GetP4rtServer().VerifyState(),
              StatusIs(absl::StatusCode::kUnknown,
                       HasSubstr("EntityCache is missing key: "
                                 "P4RT:FIXED_ROUTER_INTERFACE_TABLE:invalid")));
  SCOPED_TRACE("Failed to stay frozen after reconcile error");
}

}  // namespace
}  // namespace p4rt_app
