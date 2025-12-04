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
#include "gmock/gmock.h"
#include "grpcpp/security/credentials.h"
#include "grpcpp/support/status.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/p4runtime/queue_translator.h"
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
      p4rt_service_->ResetP4rtServer(std::move(p4runtime_impl));
    } else {
      // Restart a new P4RT service.
      p4rt_service_ =
          std::make_unique<test_lib::P4RuntimeGrpcService>(P4RuntimeImplOptions{
              .translate_port_ids = true,
              .is_freeze_mode = is_freeze_mode,
              .forwarding_config_full_path = config_save_path_,
          });
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

  // Insert invalid L3 entries
  p4rt_service_->GetP4rtAppDbTable().InsertTableEntry(
      "P4RT:FIXED_ROUTER_INTERFACE_TABLE:invalid", {});

  // State Verification fails
  EXPECT_THAT(p4rt_service_->GetP4rtServer().VerifyState(),
              StatusIs(absl::StatusCode::kUnknown,
                       HasSubstr("EntityCache is missing key: "
                                 "P4RT:FIXED_ROUTER_INTERFACE_TABLE:invalid")));
  // TODO: grpc/internal/packet-in requests are rejected in freeze
  // mode.
}

}  // namespace
}  // namespace p4rt_app
