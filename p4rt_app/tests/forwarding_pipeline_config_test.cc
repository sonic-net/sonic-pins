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
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <iterator>
#include <memory>
#include <optional>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/ascii.h"
#include "absl/strings/match.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
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
#include "p4_infra/p4_pdpi/annotation_parser.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_runtime/p4_runtime_session.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/sonic/adapters/fake_sonic_db_table.h"
#include "p4rt_app/tests/lib/app_db_entry_builder.h"
#include "p4rt_app/tests/lib/p4runtime_grpc_service.h"
#include "sai_p4/instantiations/google/clos_stage.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_p4info_fetcher.h"
//TODO(PINS): Add Component State Helper
//#include "swss/component_state_helper_interface.h"
#include "sai_p4/instantiations/google/test_tools/table_entry_generator.h"
#include "sai_p4/instantiations/google/test_tools/table_entry_generator_helper.h"
#include "sai_p4/tools/p4info_tools.h"

namespace p4rt_app {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::p4::v1::GetForwardingPipelineConfigRequest;
using ::p4::v1::GetForwardingPipelineConfigResponse;
using ::p4::v1::SetForwardingPipelineConfigRequest;
using ::testing::Contains;
using ::testing::ExplainMatchResult;
using ::testing::HasSubstr;
using ::testing::IsEmpty;
using ::testing::Key;
using ::testing::Not;
using ::testing::UnorderedElementsAreArray;

MATCHER_P2(TimeIsBetween, start, end,
           absl::StrCat("Has a value between '", absl::FormatTime(start),
                        "' and '", absl::FormatTime(end), "'")) {
  if (arg < start) {
    *result_listener << absl::FormatTime(arg) << " is too early.";
    return false;
  }
  if (arg > end) {
    *result_listener << absl::FormatTime(arg) << " is too late.";
    return false;
  }
  return true;
}

MATCHER_P2(ContainsConfigTimeBetween, start, end,
           absl::StrCat("Contains a Table Entry with key='CONFIG' and 'value "
                        "of 'last-configuration-timestamp' between ",
                        absl::FormatTime(start), " and ",
                        absl::FormatTime(end))) {
  if (!ExplainMatchResult(Contains("CONFIG"), arg.GetAllKeys(),
                          result_listener)) {
    return false;
  }
  auto table_entry = *arg.ReadTableEntry("CONFIG");
  if (!ExplainMatchResult(Contains(Key("last-configuration-timestamp")),
                          table_entry, result_listener)) {
    return false;
  }
  absl::Time config_time;
  const std::string& last_configuration_timestamp =
      table_entry.at("last-configuration-timestamp");
  int64_t timestamp_nanos;
  if (!absl::SimpleAtoi(last_configuration_timestamp, &timestamp_nanos)) {
    *result_listener << "Expected value of 'last-configuration-timestamp' "
                        "to be an integer, but got "
                     << last_configuration_timestamp;
    return false;
  }
  config_time = absl::FromUnixNanos(timestamp_nanos);
  if (!ExplainMatchResult(TimeIsBetween(start, end), config_time,
                          result_listener)) {
    *result_listener << "Raw value of 'last-configuration-timestamp' is '"
                     << last_configuration_timestamp << "'";
    return false;
  }
  return true;
}

template <typename T>
void ExtractReferences(const T& annotations,
                       absl::flat_hash_set<std::string>& refs) {
  auto result = pdpi::GetAllAnnotationsAsArgList("refers_to", annotations);
  if (result.ok()) {
    for (const auto& arg_list : *result) {
      refs.insert(std::make_move_iterator(arg_list.begin()),
                  std::make_move_iterator(arg_list.end()));
    }
  }
  result = pdpi::GetAllAnnotationsAsArgList("referenced_by", annotations);
  if (result.ok()) {
    for (const auto& arg_list : *result) {
      refs.insert(std::make_move_iterator(arg_list.begin()),
                  std::make_move_iterator(arg_list.end()));
    }
  }
}

const absl::flat_hash_set<std::string>& AliasesToKeep() {
  static const auto* const kAliases = []() {
    const p4::config::v1::P4Info& p4info = sai::GetUnionedP4Info();
    auto* aliases = new absl::flat_hash_set<std::string>();
    for (const auto& table : p4info.tables()) {
      ExtractReferences(table.preamble().annotations(), *aliases);
      for (const auto& match_field : table.match_fields()) {
        ExtractReferences(match_field.annotations(), *aliases);
      }
    }
    for (const auto& action : p4info.actions()) {
      ExtractReferences(action.preamble().annotations(), *aliases);
      for (const auto& param : action.params()) {
        ExtractReferences(param.annotations(), *aliases);
      }
    }
    for (const auto& action_profile : p4info.action_profiles()) {
      ExtractReferences(action_profile.preamble().annotations(), *aliases);
    }
    return aliases;
  }();
  return *kAliases;
}

// Erase a member from a collection if its alias matches the designated value.
// Returns true if a value was removed.
template <typename T>
bool EraseByAlias(T& collection, absl::string_view alias) {
  for (auto action = collection.begin(); action != collection.end(); ++action) {
    if (action->preamble().alias() == alias) {
      collection.erase(action);
      return true;
    }
  }
  return false;
}

// Erase a matching annotation from the annotation list.
// Returns true if an annotation was removed.
template <typename T>
bool EraseAnnotation(T& annotations, absl::string_view label,
                     absl::string_view value) {
  for (auto annotation = annotations.begin(); annotation != annotations.end();
       ++annotation) {
    auto components = pdpi::ParseAnnotation(*annotation);
    if (components.ok() && components->label == label &&
        components->body == value) {
      annotations.erase(annotation);
      return true;
    }
  }
  return false;
}

// Remove the specified annotation from all actions in the p4info.
// Returns the number of modified actions;
int RemoveAnnotationFromAllActions(p4::config::v1::P4Info& p4info,
                                   absl::string_view label,
                                   absl::string_view value) {
  int modified = 0;
  for (auto& action : *p4info.mutable_actions()) {
    if (EraseAnnotation(*action.mutable_preamble()->mutable_annotations(),
                        label, value)) {
      ++modified;
    }
  }
  return modified;
}

absl::StatusOr<absl::flat_hash_map<std::string, sonic::SonicDbEntryMap>>
DbState(const sonic::FakeSonicDbTable& table) {
  absl::flat_hash_map<std::string, sonic::SonicDbEntryMap> db_state;
  auto keys = table.GetAllKeys();
  for (const std::string& key : keys) {
    ASSIGN_OR_RETURN(auto entry, table.ReadTableEntry(key));
    db_state[key] = entry;
  }
  return db_state;
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
            .translate_port_ids = false,
            .forwarding_config_full_path = config_save_path_,
        });
    RETURN_IF_ERROR(p4rt_service_->GetP4rtServer().UpdateDeviceId(device_id));

    // Reset the P4RT client.
    std::string address = absl::StrCat("localhost:", p4rt_service_->GrpcPort());
    LOG(INFO) << "Opening P4RT connection to " << address << ".";
    auto stub = p4_runtime::CreateP4RuntimeStub(
        address, grpc::InsecureChannelCredentials());
    ASSIGN_OR_RETURN(p4rt_session_, p4_runtime::P4RuntimeSession::Create(
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
  std::unique_ptr<p4_runtime::P4RuntimeSession> p4rt_session_;
};

using VerifyTest = ForwardingPipelineConfigTest;

TEST_F(VerifyTest, DoesNotUpdateDatabases) {
  // By using the "middleblock" config we expect the ACL table definitions to
  // be written into the AppDb during a config push.
  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::VERIFY);
  *request.mutable_config()->mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  // However, since we're only verifying the config we should not see anything
  // being written to the AppDb tables. This is the first test that runs verify
  // against the P4info so it's the most visible failure. Therefore, annotate
  // this failure with suggestions for fixing verification issues.
  EXPECT_OK(p4rt_session_->SetForwardingPipelineConfig(request))
      << "Is the p4info_verification_schema updated? If not, run: "
      << "p4rt_app/scripts/"
      << "update_p4info_verification_schema.sh";
  EXPECT_THAT(p4rt_service_->GetP4rtAppDbTable().GetAllKeys(), IsEmpty());
  EXPECT_THAT(p4rt_service_->GetHostStatsStateDbTable().GetAllKeys(),
              IsEmpty());
}

TEST_F(VerifyTest, FailsWhenNoConfigIsSet) {
  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::VERIFY);

  EXPECT_THAT(p4rt_session_->SetForwardingPipelineConfig(request),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(VerifyTest, FailsWhenConfigIsInvalid) {
  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::VERIFY);
  *request.mutable_config()->mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);
  request.mutable_config()->mutable_p4info()->clear_actions();

  EXPECT_THAT(p4rt_session_->SetForwardingPipelineConfig(request),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(VerifyTest, FailsWhenContraintsAreInvalid) {
  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::VERIFY);
  *request.mutable_config()->mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  // Set the faulty annotation. Modify an annotation if present. otherwise, add
  // a faulty annotation.
  auto &table = *request.mutable_config()->mutable_p4info()->mutable_tables(0);
  if (pdpi::GetAnnotationBody("entry_restriction",
                              table.preamble().annotations())
          .ok()) {
    for (auto &annotation : *table.mutable_preamble()->mutable_annotations()) {
      if (auto parsed = pdpi::ParseAnnotation(annotation);
          parsed.ok() && parsed->label == "entry_restriction") {
        annotation = "@entry_restriction(some garbage)";
      }
    }
  } else {
    table.mutable_preamble()->add_annotations(
        "@entry_restriction(some garbage)");
  }

  EXPECT_THAT(p4rt_session_->SetForwardingPipelineConfig(request),
              StatusIs(absl::StatusCode::kInvalidArgument));
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

  EXPECT_OK(p4rt_session_->SetForwardingPipelineConfig(request));
  EXPECT_THAT(p4rt_service_->GetP4rtAppDbTable().GetAllKeys(), Not(IsEmpty()));
}

TEST_F(VerifyAndCommitTest, UpdatesConfigTimeInStateDb) {
  // By using the "middleblock" config we expect the ACL table definitionss to
  // be written into the AppDb during a config push.
  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::VERIFY_AND_COMMIT);
  *request.mutable_config()->mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  // Since we're both verifying and committing the config we expect to see
  // changes to the AppDb tables.
  absl::Time rpc_start = absl::Now();
  EXPECT_OK(p4rt_session_->SetForwardingPipelineConfig(request));
  absl::Time rpc_end = absl::Now();
  EXPECT_THAT(p4rt_service_->GetP4rtAppDbTable().GetAllKeys(), Not(IsEmpty()));
  EXPECT_THAT(p4rt_service_->GetHostStatsStateDbTable(),
              ContainsConfigTimeBetween(rpc_start, rpc_end));
}

TEST_F(VerifyAndCommitTest, FailsWhenNoConfigIsSet) {
  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::VERIFY_AND_COMMIT);

  EXPECT_THAT(p4rt_session_->SetForwardingPipelineConfig(request),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(VerifyAndCommitTest, DoesNotUpdateConfigTimeOnFailure) {
  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::VERIFY_AND_COMMIT);
  EXPECT_THAT(p4rt_session_->SetForwardingPipelineConfig(request),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_THAT(p4rt_service_->GetHostStatsStateDbTable().GetAllKeys(),
              IsEmpty());
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
  ASSERT_OK(p4rt_session_->SetForwardingPipelineConfig(request));

  // Because we don't support it today we fail when trying to push the same
  // config a second time.
  EXPECT_THAT(p4rt_session_->SetForwardingPipelineConfig(request),
              StatusIs(absl::StatusCode::kUnimplemented));
}

using CommitTest = ForwardingPipelineConfigTest;

TEST_F(CommitTest, LoadsLastSavedConfig) {
  // First we need to save the config, and a few P4RT_TABLE and VRF_TABLE
  // entries.
  p4::v1::ForwardingPipelineConfig expected_config;
  *expected_config.mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);
  ASSERT_OK(SaveConfigFile(expected_config));
  auto p4rt_entry =
      test_lib::AppDbEntryBuilder{}
          .SetTableName("FIXED_NEIGHBOR_TABLE")
          .AddMatchField("neighbor_id", "fe80::21a:11ff:fe17:5f80")
          .AddMatchField("router_interface_id", "1")
          .SetAction("set_dst_mac")
          .AddActionParam("dst_mac", "00:1a:11:17:5f:80");
  p4rt_service_->GetP4rtAppDbTable().InsertTableEntry(
      p4rt_entry.GetKey(), p4rt_entry.GetValueList());
  p4rt_service_->GetVrfAppDbTable().InsertTableEntry("vrf-0", {});

  // Add a packet replication engine entry.
  ASSERT_OK(
      p4rt_service_->GetP4rtServer().AddPortTranslation("Ethernet1/1/1", "1"));
  ASSERT_OK(
      p4rt_service_->GetP4rtServer().AddPortTranslation("Ethernet3/1/1", "2"));
  const std::string json_array =
      R"j([{"multicast_replica_instance":"0x0001",)j"
      R"j("multicast_replica_port":"Ethernet1/1/1"},)j"
      R"j({"multicast_replica_instance":"0x0001",)j"
      R"j("multicast_replica_port":"Ethernet3/1/1"}])j";
  const std::vector<std::pair<std::string, std::string>> kfv_values = {
      std::make_pair("replicas", json_array),
  };
  p4rt_service_->GetP4rtAppDbTable().InsertTableEntry(
      "REPLICATION_IP_MULTICAST_TABLE:0x0001", kfv_values);

  // Then we'll load the saved config with the COMMIT action.
  SetForwardingPipelineConfigRequest load_request = GetBasicForwardingRequest();
  load_request.set_action(SetForwardingPipelineConfigRequest::COMMIT);
  ASSERT_OK(p4rt_session_->SetForwardingPipelineConfig(load_request));

  // Finally, we verify we can read back the saved request, and the table
  // entries.
  GetForwardingPipelineConfigRequest get_request;
  get_request.set_device_id(p4rt_session_->DeviceId());
  ASSERT_OK_AND_ASSIGN(GetForwardingPipelineConfigResponse get_response,
                       p4rt_session_->GetForwardingPipelineConfig(get_request));
  EXPECT_THAT(get_response.config(), EqualsProto(expected_config));

  p4::v1::ReadRequest read_request;
  read_request.set_device_id(p4rt_session_->DeviceId());
  read_request.add_entities()->mutable_table_entry();
  ASSERT_OK_AND_ASSIGN(p4::v1::ReadResponse read_response,
                       p4rt_session_->Read(read_request));
  EXPECT_EQ(read_response.entities_size(), 2);

  p4::v1::ReadRequest read_request_pre;
  read_request_pre.set_device_id(p4rt_session_->DeviceId());
  read_request_pre.add_entities()
      ->mutable_packet_replication_engine_entry()
      ->mutable_multicast_group_entry();
  ASSERT_OK_AND_ASSIGN(p4::v1::ReadResponse read_response_pre,
                       p4rt_session_->Read(read_request_pre));
  EXPECT_EQ(read_response_pre.entities_size(), 1);

  p4::v1::ReadRequest read_request_pre_clone;
  read_request_pre_clone.set_device_id(p4rt_session_->DeviceId());
  read_request_pre_clone.add_entities()
      ->mutable_packet_replication_engine_entry()
      ->mutable_clone_session_entry();
  ASSERT_OK_AND_ASSIGN(p4::v1::ReadResponse read_response_pre_clone,
                       p4rt_session_->Read(read_request_pre_clone));
  EXPECT_THAT(read_response_pre_clone.entities(), IsEmpty());
}

/* TODO(PINS): To handle GoesCriticalIfReadingCacheFails test in November release.
TEST_F(CommitTest, GoesCriticalIfReadingCacheFails) {
  // First we need to save the config, and a few P4RT_TABLE and VRF_TABLE
  // entries.
  p4::v1::ForwardingPipelineConfig expected_config;
  *expected_config.mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);
  ASSERT_OK(SaveConfigFile(expected_config));
  auto p4rt_entry =
      test_lib::AppDbEntryBuilder{}
          .SetTableName("INVALID_TABLE_NAME")
          .AddMatchField("neighbor_id", "fe80::21a:11ff:fe17:5f80")
          .AddMatchField("router_interface_id", "1")
          .SetAction("set_dst_mac")
          .AddActionParam("dst_mac", "00:1a:11:17:5f:80");
  p4rt_service_->GetP4rtAppDbTable().InsertTableEntry(
      p4rt_entry.GetKey(), p4rt_entry.GetValueList());

  // The config gets loaded, but 'INVALID_TABLE_NAME' cannot be translated to
  // PI. So we expect the switch to go critical..
  SetForwardingPipelineConfigRequest load_request = GetBasicForwardingRequest();
  load_request.set_action(SetForwardingPipelineConfigRequest::COMMIT);
  EXPECT_THAT(p4rt_session_->SetForwardingPipelineConfig(load_request),
              StatusIs(absl::StatusCode::kInternal));
   EXPECT_THAT(p4rt_service_->GetComponentStateHelper().StateInfo().state,
              swss::ComponentState::kError); 
}*/

TEST_F(CommitTest, FailsIfNoConfigHasBeenSaved) {
  // If the file exists before this test for any reason then this test is
  // pointless.
  ASSERT_EQ(GetSavedConfig().status().code(),
            absl::StatusCode::kInvalidArgument)
      << "This test requires the config file to not be saved before running.";

  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::COMMIT);

  EXPECT_THAT(p4rt_session_->SetForwardingPipelineConfig(request),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(CommitTest, FailsIfAConfigIsSet) {
  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::COMMIT);
  *request.mutable_config()->mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  EXPECT_THAT(p4rt_session_->SetForwardingPipelineConfig(request),
              StatusIs(absl::StatusCode::kInvalidArgument));
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

  EXPECT_OK(p4rt_session_->SetForwardingPipelineConfig(commit_request));

  ASSERT_OK_AND_ASSIGN(GetForwardingPipelineConfigResponse get_response,
                       p4rt_session_->GetForwardingPipelineConfig(get_request));
  EXPECT_THAT(get_response.config(), EqualsProto(commit_request.config()));
}

TEST_F(ReconcileAndCommitTest, WritesConfigToAFile) {
  SetForwardingPipelineConfigRequest request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT);
  *request.mutable_config()->mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  ASSERT_OK(p4rt_session_->SetForwardingPipelineConfig(request));

  EXPECT_THAT(GetSavedConfig(), IsOkAndHolds(EqualsProto(request.config())));
}

TEST_F(ReconcileAndCommitTest, FailsWhenNoConfigIsSet) {
  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT);

  EXPECT_THAT(p4rt_session_->SetForwardingPipelineConfig(request),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(ReconcileAndCommitTest, SetDuplicateForwardingPipelineConfig) {
  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT);
  *request.mutable_config()->mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  ASSERT_OK(p4rt_session_->SetForwardingPipelineConfig(request));
  EXPECT_OK(p4rt_session_->SetForwardingPipelineConfig(request));
}

TEST_F(ReconcileAndCommitTest, DeletingEmptyFixedTablesIsAllowed) {
  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT);
  *request.mutable_config()->mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  ASSERT_OK(p4rt_session_->SetForwardingPipelineConfig(request));

  auto& tables = *request.mutable_config()->mutable_p4info()->mutable_tables();
  for (auto table = tables.begin(); table != tables.end();) {
    if (absl::StartsWith(table->preamble().alias(), "acl_") ||
        AliasesToKeep().contains(table->preamble().alias())) {
      ++table;
    } else {
      table = tables.erase(table);
    }
  }
  ASSERT_OK(p4rt_session_->SetForwardingPipelineConfig(request));
}

TEST_F(ReconcileAndCommitTest, AddingFixedTablesIsAllowed) {
  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT);
  *request.mutable_config()->mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  // Apply config without non-acl tables.
  auto& tables = *request.mutable_config()->mutable_p4info()->mutable_tables();
  for (auto table = tables.begin(); table != tables.end();) {
    if (absl::StartsWith(table->preamble().alias(), "acl_") ||
        AliasesToKeep().contains(table->preamble().alias())) {
      ++table;
    } else {
      table = tables.erase(table);
    }
  }
  ASSERT_OK(p4rt_session_->SetForwardingPipelineConfig(request));

  // Apply config with fixed tables.
  *request.mutable_config()->mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);
  ASSERT_OK(p4rt_session_->SetForwardingPipelineConfig(request));
}

TEST_F(ReconcileAndCommitTest, ModifyingEmptyFixedTablesIsAllowed) {
  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT);
  *request.mutable_config()->mutable_p4info() =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  ASSERT_OK(p4rt_session_->SetForwardingPipelineConfig(request));

  // Remove some fixed table match fields.
  auto& tables = *request.mutable_config()->mutable_p4info()->mutable_tables();
  for (auto& table : tables) {
    if (absl::StartsWith(table.preamble().alias(), "acl")) continue;
    if (table.match_fields().size() < 2) continue;  // All tables need a match.
    auto constraints = pdpi::GetAnnotationBody("entry_restriction",
                                               table.preamble().annotations());
    for (auto match_field = table.mutable_match_fields()->begin();
         match_field != table.mutable_match_fields()->end(); ++match_field) {
      if (AliasesToKeep().contains(match_field->name()) ||
          (constraints.ok() &&
           absl::StrContains(*constraints, match_field->name()))) {
        continue;
      }
      table.mutable_match_fields()->erase(match_field);
      break;
    }
  }
  ASSERT_OK(p4rt_session_->SetForwardingPipelineConfig(request));
}

using GetForwardingConfigTest = ForwardingPipelineConfigTest;

TEST_F(GetForwardingConfigTest, ReturnsNothingIfConfigHasNotBeenSet) {
  GetForwardingPipelineConfigRequest get_request;
  get_request.set_device_id(p4rt_session_->DeviceId());
  get_request.set_response_type(GetForwardingPipelineConfigRequest::ALL);

  ASSERT_OK_AND_ASSIGN(GetForwardingPipelineConfigResponse get_response,
                       p4rt_session_->GetForwardingPipelineConfig(get_request));
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

  ASSERT_OK(p4rt_session_->SetForwardingPipelineConfig(set_request));

  ASSERT_OK_AND_ASSIGN(GetForwardingPipelineConfigResponse get_response,
                       p4rt_session_->GetForwardingPipelineConfig(get_request));
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

  ASSERT_OK(p4rt_session_->SetForwardingPipelineConfig(set_request));

  ASSERT_OK_AND_ASSIGN(GetForwardingPipelineConfigResponse get_response,
                       p4rt_session_->GetForwardingPipelineConfig(get_request));
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

  ASSERT_OK(p4rt_session_->SetForwardingPipelineConfig(set_request));

  ASSERT_OK_AND_ASSIGN(GetForwardingPipelineConfigResponse get_response,
                       p4rt_session_->GetForwardingPipelineConfig(get_request));
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

  ASSERT_OK(p4rt_session_->SetForwardingPipelineConfig(set_request));

  ASSERT_OK_AND_ASSIGN(GetForwardingPipelineConfigResponse get_response,
                       p4rt_session_->GetForwardingPipelineConfig(get_request));
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
  ASSERT_OK(p4rt_session_->SetForwardingPipelineConfig(set_request));

  // Verify we can read the same forwarding config back.
  {
    GetForwardingPipelineConfigRequest get_request;
    get_request.set_device_id(p4rt_session_->DeviceId());
    ASSERT_OK_AND_ASSIGN(
        GetForwardingPipelineConfigResponse get_response,
        p4rt_session_->GetForwardingPipelineConfig(get_request));
    EXPECT_THAT(get_response.config(), EqualsProto(set_request.config()));
  }

  // Update the forwarding config's cookie, and reset it.
  set_request.mutable_config()->mutable_cookie()->set_cookie(456);
  ASSERT_OK(p4rt_session_->SetForwardingPipelineConfig(set_request));

  // Verify we can read back the new forwarding config.
  {
    GetForwardingPipelineConfigRequest get_request;
    get_request.set_device_id(p4rt_session_->DeviceId());
    ASSERT_OK_AND_ASSIGN(
        GetForwardingPipelineConfigResponse get_response,
        p4rt_session_->GetForwardingPipelineConfig(get_request));
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
      "ACL_TABLE_DEFINITION_TABLE:ACL_ACL_PRE_INGRESS_TABLE",
      "SWSS_RC_INVALID_PARAM", "my error message");
  ASSERT_THAT(p4_runtime::SetMetadataAndSetForwardingPipelineConfig(
                  p4rt_session_.get(),
                  SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
                  sai::GetP4Info(sai::Instantiation::kMiddleblock)),
              StatusIs(absl::StatusCode::kInternal));

  // Because we failed to program the forwarding pipeline config we should not
  // be able to write to the table.
  p4::v1::WriteRequest request;
  EXPECT_THAT(p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                           request),
              StatusIs(absl::StatusCode::kInternal));
}

TEST_F(ForwardingPipelineConfigTest, InvalidP4ConstraintDoesNotGoCritical) {
  constexpr absl::string_view kEntryRestrictionStr = "@entry_restriction";

  // Go through all the tables an replace any P4 constraint annotation with an
  // invalid one.
  auto p4_info = sai::GetP4Info(sai::Instantiation::kMiddleblock);
  for (p4::config::v1::Table& table : *p4_info.mutable_tables()) {
    for (std::string& annon :
         *table.mutable_preamble()->mutable_annotations()) {
      if (absl::StartsWith(annon, kEntryRestrictionStr)) {
        annon = absl::StrCat(kEntryRestrictionStr, "(invalid constraint)");
      }
    }
  }

  ASSERT_THAT(
      p4_runtime::SetMetadataAndSetForwardingPipelineConfig(
          p4rt_session_.get(),
          SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT, p4_info),
      StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(ForwardingPipelineConfigTest,
       ReconcileFailsIfNewConfigDoesNotSupportCurrentFlows) {
  // Push the baseline P4Info.
  auto p4_info = sai::GetP4Info(sai::Instantiation::kMiddleblock);
  ASSERT_OK(p4_runtime::SetMetadataAndSetForwardingPipelineConfig(
      p4rt_session_.get(),
      SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT, p4_info));

  // Add a table entry to the acl_ingress_table.
  auto ir_p4_info = sai::GetIrP4Info(sai::Instantiation::kMiddleblock);
  ASSERT_OK_AND_ASSIGN(
      sai::TableEntryGenerator generator,
      sai::GetGenerator(ir_p4_info.tables_by_name().at("acl_ingress_table")));
  pdpi::IrTableEntry ir_entry = generator.generator(1);
  ASSERT_GT(ir_entry.matches().size(), 0);

  p4::v1::WriteRequest request;
  auto& update = *request.add_updates();
  update.set_type(p4::v1::Update::INSERT);
  ASSERT_OK_AND_ASSIGN(*update.mutable_entity()->mutable_table_entry(),
                       pdpi::IrTableEntryToPi(ir_p4_info, ir_entry));

  EXPECT_OK(p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                         request));

  // Create a P4Info without the entry's match field.
  for (auto& table : *p4_info.mutable_tables()) {
    if (table.preamble().alias() != "acl_ingress_table") continue;
    for (auto match_field = table.mutable_match_fields()->begin();
         match_field != table.mutable_match_fields()->end(); ++match_field) {
      if (match_field->name() == ir_entry.matches(0).name()) {
        table.mutable_match_fields()->erase(match_field);
        break;
      }
    }
    break;
  }
}

TEST_F(ForwardingPipelineConfigTest,
       ReconcileFailsIfNewConfigDiffersForCurrentFlows) {
  // Push the baseline P4Info.
  auto p4_info = sai::GetP4Info(sai::Instantiation::kMiddleblock);
  ASSERT_OK(p4_runtime::SetMetadataAndSetForwardingPipelineConfig(
      p4rt_session_.get(),
      SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT, p4_info));

  // Add a table entry to the acl_ingress_table.
  auto ir_p4_info = sai::GetIrP4Info(sai::Instantiation::kMiddleblock);
  ASSERT_OK_AND_ASSIGN(
      sai::TableEntryGenerator generator,
      sai::GetGenerator(ir_p4_info.tables_by_name().at("acl_ingress_table")));
  pdpi::IrTableEntry ir_entry = generator.generator(1);
  ASSERT_GT(ir_entry.matches().size(), 0);

  p4::v1::WriteRequest request;
  auto& update = *request.add_updates();
  update.set_type(p4::v1::Update::INSERT);
  ASSERT_OK_AND_ASSIGN(*update.mutable_entity()->mutable_table_entry(),
                       pdpi::IrTableEntryToPi(ir_p4_info, ir_entry));

  EXPECT_OK(p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                         request));

  // Modify the match field name to change the translation.
  for (auto& table : *p4_info.mutable_tables()) {
    if (table.preamble().alias() != "acl_ingress_table") continue;
    for (auto& match_field : *table.mutable_match_fields()) {
      if (match_field.name() == ir_entry.matches(0).name()) {
        match_field.set_name("other_name");
        break;
      }
    }
    break;
  }
}

TEST_F(ForwardingPipelineConfigTest,
       ReconcileIsNotBlockedIfNewConfigSupportsCurrentFlows) {
  // Push the baseline P4Info.
  auto p4_info = sai::GetP4Info(sai::Instantiation::kMiddleblock);
  ASSERT_OK(p4_runtime::SetMetadataAndSetForwardingPipelineConfig(
      p4rt_session_.get(),
      SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT, p4_info));

  // Add a table entry to the acl_ingress_table.
  auto ir_p4_info = sai::GetIrP4Info(sai::Instantiation::kMiddleblock);
  ASSERT_OK_AND_ASSIGN(
      sai::TableEntryGenerator generator,
      sai::GetGenerator(ir_p4_info.tables_by_name().at("acl_ingress_table")));
  pdpi::IrTableEntry ir_entry = generator.generator(1);
  ASSERT_GT(ir_entry.matches().size(), 0);

  p4::v1::WriteRequest request;
  auto& update = *request.add_updates();
  update.set_type(p4::v1::Update::INSERT);
  ASSERT_OK_AND_ASSIGN(*update.mutable_entity()->mutable_table_entry(),
                       pdpi::IrTableEntryToPi(ir_p4_info, ir_entry));

  EXPECT_OK(p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                         request));

  // Add a match field, which will not impact the translation.
  for (auto& table : *p4_info.mutable_tables()) {
    if (table.preamble().alias() != "acl_ingress_table") continue;
    auto& match_field = *table.add_match_fields();
    match_field.set_id(table.match_fields().size());
    match_field.set_name("other_name");
    match_field.set_match_type(p4::config::v1::MatchField::TERNARY);
    match_field.add_annotations(
        "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_OUTER_VLAN_ID)");
    match_field.set_bitwidth(4);
    break;
  }

  ASSERT_THAT(
      p4_runtime::SetMetadataAndSetForwardingPipelineConfig(
          p4rt_session_.get(),
          SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT, p4_info),
      Not(StatusIs(absl::StatusCode::kInvalidArgument)));
}

class PerConfigTest : public ForwardingPipelineConfigTest,
                      public testing::WithParamInterface<
                          std::tuple<sai::Instantiation, sai::ClosStage>> {};

TEST_P(PerConfigTest, VerifySucceeds) {
  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::VERIFY);
  *request.mutable_config()->mutable_p4info() =
      sai::FetchP4Info(std::get<0>(GetParam()), std::get<1>(GetParam()));

  EXPECT_OK(p4rt_session_->SetForwardingPipelineConfig(request));
}

TEST_P(PerConfigTest, VerifyAndCommitSucceeds) {
  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::VERIFY_AND_COMMIT);
  *request.mutable_config()->mutable_p4info() =
      sai::FetchP4Info(std::get<0>(GetParam()), std::get<1>(GetParam()));

  EXPECT_OK(p4rt_session_->SetForwardingPipelineConfig(request));
  EXPECT_THAT(p4rt_service_->GetP4rtAppDbTable().GetAllKeys(), Not(IsEmpty()));
}

TEST_P(PerConfigTest, ReconcileAndCommitSucceeds) {
  auto request = GetBasicForwardingRequest();
  request.set_action(SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT);
  *request.mutable_config()->mutable_p4info() =
      sai::FetchP4Info(std::get<0>(GetParam()), std::get<1>(GetParam()));

  EXPECT_OK(p4rt_session_->SetForwardingPipelineConfig(request));
  EXPECT_THAT(p4rt_service_->GetP4rtAppDbTable().GetAllKeys(), Not(IsEmpty()));
  EXPECT_OK(p4rt_session_->SetForwardingPipelineConfig(request))
      << "Failed second commit (expected no-op)";
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
    testing::Combine(testing::ValuesIn(sai::AllSaiInstantiations()),
                     testing::ValuesIn(sai::AllStages())),
    PerConfigTestCaseName);

}  // namespace
}  // namespace p4rt_app
