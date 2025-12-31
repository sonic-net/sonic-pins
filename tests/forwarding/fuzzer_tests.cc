// Copyright 2024 Google LLC
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
#include "tests/forwarding/fuzzer_tests.h"

#include <algorithm>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "absl/algorithm/container.h"
#include "absl/container/flat_hash_set.h"
#include "absl/flags/flag.h"
#include "absl/log/log.h"
#include "absl/random/random.h"
#include "absl/random/seed_sequences.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/status.h"           // IWYU pragma: keep
#include "gutil/gutil/status_matchers.h"  // IWYU pragma: keep
#include "gutil/gutil/version.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_fuzzer/annotation_util.h"
#include "p4_fuzzer/fuzz_util.h"
#include "p4_fuzzer/fuzzer.pb.h"
#include "p4_fuzzer/fuzzer_config.h"
#include "p4_fuzzer/switch_state.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/names.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/p4_runtime_session_extras.h"
#include "p4_pdpi/sequencing.h"
#include "proto/gnmi/gnmi.pb.h"
// TODO: A temporary dependence on SAI to mask a bug. Ideally, safe
// to remove in April 2024.
#include "sai_p4/instantiations/google/versions.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "tests/thinkit_sanity_tests.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/mirror_testbed_fixture.h"
#include "thinkit/switch.h"
#include "thinkit/test_environment.h"

ABSL_FLAG(std::optional<int>, fuzzer_iterations, std::nullopt,
          "Number of updates the fuzzer should generate. If not set, fuzzer "
          "runs until `fuzzer_duration` seconds has elapsed (default 1 hour).");

// NOTE: If fuzzer_duration flag > 1 hour, then test_timeout blaze flag must be
// set to > 1 hour to avoid timeout failure when running blaze test.
ABSL_FLAG(absl::Duration, fuzzer_duration, absl::Hours(1),
          "Max duration the fuzzer should run for. Includes time for setup and"
          "tear down.");

ABSL_FLAG(
    std::vector<std::string>, fuzzer_ports, {},
    "Set of valid port names for the fuzzer to use. The empty default value "
    "signifies that the fuzzer should get the ports from the gNMI config.");

ABSL_FLAG(std::vector<std::string>, fuzzer_qos_queues, {"0x1"},
          "Set of valid QoS queues for the fuzzer to use.");

ABSL_FLAG(bool, fuzzer_clear_switch_at_end, true,
          "Clear the switch (possibly through forcible restart) at end of "
          "test. Useful to disable for debugging.");

namespace p4_fuzzer {
namespace {

// Buffer time to wind down testing after the test iterations are complete.
constexpr absl::Duration kEndOfTestBuffer = absl::Minutes(10);

// Returns true if the given table should be masked with `current_version`.
bool IsMaskedResource(absl::string_view table_name,
                      gutil::Version current_version) {
  absl::flat_hash_set<std::string> masked_tables = {};
  return masked_tables.contains(table_name);
}

}  // namespace

// FuzzerTestFixture class functions

void FuzzerTestFixture::SetUp() {
  GetParam().mirror_testbed->SetUp();
  if (auto& id = GetParam().test_case_id; id.has_value()) {
    GetParam().mirror_testbed->GetMirrorTestbed().Environment().SetTestCaseID(
        *id);
  }
}

void FuzzerTestFixture::TearDown() {
  auto& sut = GetParam().mirror_testbed->GetMirrorTestbed().Sut();

  if (HasFailure()) {
    LOG(INFO) << "Switch state on failure:\n"
              << switch_state_->SwitchStateSummary();
  }

  // Save the logs before reset clearing to help with debug in case of failure.
  if (HasFatalFailure()) {
    LOG(INFO) << "Saving failure state.";
    EXPECT_OK(GetParam().mirror_testbed->SaveSwitchLogs(
        /*save_prefix=*/"failure_state_"));
  }

  // Clear the switch of all entries if flag is enabled.
  if (absl::GetFlag(FLAGS_fuzzer_clear_switch_at_end)) {
    // Attempt to connect to switch and clear tables.
    auto session = pdpi::P4RuntimeSession::Create(sut);
    absl::Status switch_cleared =
        session.ok() ? pdpi::ClearEntities(**session) : session.status();

    // Though the above statement should never fail, it sometimes
    // inadvertently does due to some bug. Then we reboot the switch to
    // clear the state.
    if (!switch_cleared.ok()) {
      ADD_FAILURE()
          << "Failed to clear entries from switch (attempting reboot)";
      LOG(WARNING) << "Dumping reported error:\n " << switch_cleared;
      // Save the logs before rebooting to help with debug.
      EXPECT_OK(GetParam().mirror_testbed->SaveSwitchLogs(
          /*save_prefix=*/"failed_to_clear_sut_state_"));
      pins_test::TestGnoiSystemColdReboot(sut);
    }
  }
  GetParam().mirror_testbed->TearDown();
}

using ::p4::v1::WriteRequest;

TEST_P(FuzzerTestFixture, P4rtWriteAndCheckNoInternalErrors) {
  const absl::Time deadline =
      absl::Now() + absl::GetFlag(FLAGS_fuzzer_duration) - kEndOfTestBuffer;

  // Gets the mirror testbed from the test parameters given to
  // FuzzerTestFixture.
  thinkit::MirrorTestbed& mirror_testbed =
      GetParam().mirror_testbed->GetMirrorTestbed();
  thinkit::Switch& sut = mirror_testbed.Sut();
  thinkit::TestEnvironment& environment = mirror_testbed.Environment();

  // Probabilities must be between 0 and 1.
  float mutate_update_probability = GetParam().mutate_update_probability;
  ASSERT_GE(mutate_update_probability, 0.0);
  ASSERT_LE(mutate_update_probability, 1.0);

  // Initialize connection, clear switch state, and push the GNMI configuration,
  // if given.
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<pdpi::P4RuntimeSession> session,
                       pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
                           sut, GetParam().gnmi_config, GetParam().p4info));

  // Current switch version.
  ASSERT_OK_AND_ASSIGN(
      gutil::Version current_version,
      gutil::ParseVersion(GetParam().p4info.pkg_info().version()));

  // Record gNMI config and P4Info that we plan to push for debugging purposes.
  if (GetParam().gnmi_config.has_value()) {
    ASSERT_OK(environment.StoreTestArtifact("gnmi_config.txt",
                                            *GetParam().gnmi_config));
  }
  ASSERT_OK(environment.StoreTestArtifact("p4info.txt", GetParam().p4info));

  bool mask_known_failures = environment.MaskKnownFailures();

  // Construct gNMI stub.
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<gnmi::gNMI::StubInterface> stub,
                       sut.CreateGnmiStub());

  ASSERT_OK_AND_ASSIGN(std::vector<pins_test::P4rtPortId> ports,
                       pins_test::P4rtPortId::MakeVectorFromP4rtEncodings(
                           absl::GetFlag(FLAGS_fuzzer_ports)));
  if (ports.empty()) {
    // Get all valid ports from the gNMI config if none are specified as a flag.
    // Currently, we only get Ethernet ports by default.
    ASSERT_OK_AND_ASSIGN(ports,
                         pins_test::GetMatchingP4rtPortIds(
                             *stub, pins_test::IsEnabledEthernetInterface));
  }

  ASSERT_OK_AND_ASSIGN(
      p4_fuzzer::FuzzerConfig config,
      p4_fuzzer::FuzzerConfig::Create(
          GetParam().p4info,
          ConfigParams{
              .ports = ports,
              .qos_queues = absl::GetFlag(FLAGS_fuzzer_qos_queues),
              .role = GetParam().p4rt_role,
              .mutate_update_probability = mutate_update_probability,
              .tables_for_which_to_not_exceed_resource_guarantees =
                  GetParam().tables_for_which_to_not_exceed_resource_guarantees,
              .disabled_fully_qualified_names =
                  GetParam().disabled_fully_qualified_names,
              .non_modifiable_tables = GetParam().non_modifiable_tables,
              .TreatAsEqualDuringReadDueToKnownBug =
                  GetParam().TreatAsEqualDuringReadDueToKnownBug,
              .ignore_constraints_on_tables =
                  GetParam().ignore_constraints_on_tables,
              .IsBuggyUpdateThatShouldBeSkipped =
                  GetParam().IsBuggyUpdateThatShouldBeSkipped,
              .ModifyFuzzedTableEntry = GetParam().ModifyFuzzedTableEntry,
              .ModifyFuzzedMulticastGroupEntry =
                  GetParam().ModifyFuzzedMulticastGroupEntry,
          }));

  // Remove once switch state transitions to entities. This
  // would allow multicast to be included in the weighted distribution the
  // fuzzer uses.
  int total_entries_supported = GetParam().multicast_group_table_size;
  for (const auto& table : AllValidTablesForP4RtRole(config)) {
    total_entries_supported += table.size();
  }
  double fuzz_multicast_probability =
      static_cast<double>(GetParam().multicast_group_table_size) /
      static_cast<double>(total_entries_supported);
  config.SetFuzzMulticastGroupEntryProbability(fuzz_multicast_probability);
  LOG(INFO) << "Proability of fuzzing multicast is "
            << fuzz_multicast_probability;

  // TODO: Remove absl::StreamFormatter when we update to a new LTS
  // branch of Abseil.
  ASSERT_OK(environment.StoreTestArtifact(
      "ports_used_by_fuzzer.txt",
      absl::StrJoin(config.GetPorts(), ",", absl::StreamFormatter())));
  ASSERT_OK(environment.StoreTestArtifact(
      "queues_used_fuzzer.txt",
      absl::StrJoin(config.GetQosQueues(), ",", absl::StreamFormatter())));

  absl::BitGen gen;

  const absl::Time start_time = absl::Now();

  // Run fuzzer.
  int num_updates = 0;
  int num_ok_statuses = 0;
  int num_notok_without_mutations = 0;
  int num_ok_with_mutations = 0;
  int max_batch_size_seen = 0;
  std::set<std::string> error_messages;
  switch_state_ = std::make_unique<SwitchState>(config.GetIrP4Info());
  const std::optional<int> num_iterations =
      absl::GetFlag(FLAGS_fuzzer_iterations);
  int iteration = 0;

  int longest_iteration = 0;
  absl::Duration longest_iteration_duration = absl::ZeroDuration();

  // Run until the deadline or until we've fuzzed for the requested number of
  // iterations.
  while (absl::Now() < deadline &&
         (!num_iterations.has_value() || iteration < *num_iterations)) {
    iteration++;
    absl::Time iteration_start_time = absl::Now();
    if (iteration % 100 == 1) LOG(INFO) << "Starting iteration " << iteration;

    // Generated fuzzed request.
    AnnotatedWriteRequest annotated_request = FuzzWriteRequest(
        &gen, config, *switch_state_, GetParam().max_batch_size);
    WriteRequest request = RemoveAnnotations(annotated_request);
    num_updates += request.updates_size();
    max_batch_size_seen = std::max(max_batch_size_seen, request.updates_size());

    ASSERT_OK(environment.AppendToTestArtifact(
        "requests_and_responses.txt",
        absl::StrCat("# Write request number ", iteration, "\n",
                     MakeReadable(annotated_request).DebugString())));
    ASSERT_OK(environment.AppendToTestArtifact("pi_write_request_trace.txt",
                                               request.DebugString()));

    // Send to switch.
    ASSERT_OK_AND_ASSIGN(pdpi::IrWriteRpcStatus response,
                         pdpi::SendPiUpdatesAndReturnPerUpdateStatus(
                             *session, request.updates()));

    ASSERT_OK(environment.AppendToTestArtifact(
        "requests_and_responses.txt",
        absl::StrCat("# Response to request number ", iteration, "\n",
                     response.DebugString())));

    // If there is an RPC-wide error, then the switch has gone into critical
    // state and we can no longer continue testing.
    ASSERT_TRUE(response.has_rpc_response())
        << "Expected proper response, but got: " << response.DebugString();

    ASSERT_TRUE(
        (response.rpc_response().statuses().size() == request.updates_size()))
        << "Expected number of responses to equal number of updates, but they "
           "differed. Updates: "
        << request.updates_size()
        << " Responses: " << response.rpc_response().statuses().size();

    ASSERT_OK(OutputInterleavedRequestAndResponseToArtifact(
        environment, /*artifact_name=*/"requests_and_responses_interleaved.txt",
        /*identifying_prefix=*/absl::StrCat("Iteration ", iteration),
        annotated_request, response));

    // Ensure that the responses from the switch correctly use fail-on-first
    // ordering.
    if (!GetParam().do_not_enforce_fail_on_first_switch_ordering) {
      bool encountered_first_error = false;
      for (const pdpi::IrUpdateStatus& status :
           response.rpc_response().statuses()) {
        if (status.code() == google::rpc::Code::OK &&
            !encountered_first_error) {
          continue;
        }
        ASSERT_TRUE(!encountered_first_error ||
                    status.code() == google::rpc::Code::ABORTED)
            << "Expected all responses after first failure to be ABORTED, but "
               "got: "
            << status.DebugString() << "\n\nFull Response:\n"
            << response.rpc_response().DebugString();
        encountered_first_error = true;
      }
    }

    // We update our internal view of the switch state incrementally and check
    // for resource exhaustion.
    for (int update_num = 0;
         update_num < response.rpc_response().statuses().size(); update_num++) {
      const pdpi::IrUpdateStatus& status =
          response.rpc_response().statuses(update_num);
      const p4::v1::Update& update = request.updates(update_num);

      EXPECT_NE(status.code(), google::rpc::Code::INTERNAL)
          << "Fuzzing should never cause an INTERNAL error, but got: "
          << status.DebugString();
      // Check resource exhaustion.
      // Check for invalid multicast resource exhaustion
      // once multicast resource are modeled.
      if (status.code() == google::rpc::Code::RESOURCE_EXHAUSTED &&
          update.entity().has_table_entry()) {
        int table_id = update.entity().table_entry().table_id();
        ASSERT_OK_AND_ASSIGN(
            const pdpi::IrTableDefinition& table,
            gutil::FindOrStatus(config.GetIrP4Info().tables_by_id(), table_id));

        // If this isn't a specifically masked resource, then check if resource
        // exhaustion is allowed.
        if (!IsMaskedResource(table.preamble().alias(), current_version)) {
          // Check that table is allowed to have exhausted resources.
          ASSERT_OK(switch_state_->ResourceExhaustedIsAllowed(update))
              << "\nUpdate = " << update.DebugString()
              << "\nState = " << switch_state_->SwitchStateSummary();
        }
      }
      // Collect error messages and update state.
      if (status.code() != google::rpc::Code::OK) {
        error_messages.insert(absl::StrCat(
            google::rpc::Code_Name(status.code()), ": ", status.message()));
      } else {
        ASSERT_OK(switch_state_->ApplyUpdate(update));
        num_ok_statuses += 1;
      }

      bool is_mutated =
          annotated_request.updates(update_num).mutations_size() > 0;

      // If the Fuzzer uses a mutation, then the update is likely to be
      // invalid.
      if (status.code() == google::rpc::Code::OK && is_mutated) {
        EXPECT_OK(environment.AppendToTestArtifact(
            "fuzzer_mutated_but_ok.txt",
            absl::StrCat("-------------------\n\nRequest = \n",
                         annotated_request.updates(update_num).DebugString())));
        num_ok_with_mutations++;
      }

      if (status.code() != google::rpc::Code::OK &&
          status.code() != google::rpc::Code::RESOURCE_EXHAUSTED &&
          status.code() != google::rpc::Code::ABORTED &&
          status.code() != google::rpc::Code::UNIMPLEMENTED) {
        if (!is_mutated) {
          // Switch did not consider update OK but fuzzer did not use a
          // mutation (i.e. thought the update should be valid).
          EXPECT_OK(environment.AppendToTestArtifact(
              "fuzzer_inaccuracies.txt",
              absl::StrCat("-------------------\n\nrequest = \n",
                           annotated_request.updates(update_num).DebugString(),
                           "\n\nstatus = \n", status.DebugString())));
          EXPECT_OK(environment.AppendToTestArtifact(
              "fuzzer_inaccuracies_short.txt",
              absl::StrCat(status.message(), "\n")));
          num_notok_without_mutations += 1;
        }
      }
    }

    if (!GetParam().milestone.has_value()) {
      // Read switch state (to check that reading never fails).
      ASSERT_OK_AND_ASSIGN(std::vector<p4::v1::TableEntry> table_entries,
                           pdpi::ReadPiTableEntries(session.get()));
      if (mask_known_failures) {
        ASSERT_OK(switch_state_->AssertEntriesAreEqualToState(
            table_entries, config.GetTreatAsEqualDuringReadDueToKnownBug()));
      } else {
        ASSERT_OK(switch_state_->AssertEntriesAreEqualToState(table_entries));
      }
    }

    if (absl::Duration current_duration = absl::Now() - iteration_start_time;
        current_duration > longest_iteration_duration) {
      longest_iteration = iteration;
      longest_iteration_duration = current_duration;
    }
  }

  if (num_iterations.has_value() && iteration < *num_iterations) {
    ADD_FAILURE()
        << "Iteration mode enabled. Fuzzer test ran out of time after "
        << iteration << " out of " << *num_iterations << " iterations."
        << " Fuzzer_Duration set to " << absl::GetFlag(FLAGS_fuzzer_duration)
        << " seconds.";
  }

  ASSERT_OK_AND_ASSIGN(std::vector<p4::v1::TableEntry> table_entries,
                       pdpi::ReadPiTableEntries(session.get()));
  EXPECT_OK(switch_state_->AssertEntriesAreEqualToState(
      table_entries, config.GetTreatAsEqualDuringReadDueToKnownBug()));

  LOG(INFO) << "Finished " << iteration << " iterations.";
  LOG(INFO) << "  num_updates:                 " << num_updates;
  // Expected value is 50, so if it's very far from that, we probably have a
  // problem.
  LOG(INFO) << "  Avg updates per request:     "
            << num_updates / static_cast<double>(iteration);
  LOG(INFO) << "  max updates in a request:    " << max_batch_size_seen;
  LOG(INFO) << "  num_ok_statuses:             " << num_ok_statuses;

  // These should be 0 if the fuzzer works optimally. These numbers do not
  // affect the soundness of the fuzzer, just the modularity, so it is a goal
  // that we are not 100% strict on as it would be incredibly challenging to
  // enforce. However, it is highly likely that bugs in the switch, which we
  // can't currently detect, are hidden in these numbers.
  LOG(INFO) << "  num_notok_without_mutations: " << num_notok_without_mutations;
  LOG(INFO) << "  num_ok_with_mutations: " << num_ok_with_mutations;

  LOG(INFO) << "Fuzzer Duration Limit: "
            << absl::GetFlag(FLAGS_fuzzer_duration);
  LOG(INFO) << "Test set up/tear down buffer: " << kEndOfTestBuffer;
  LOG(INFO) << "Time Spent Fuzzing: " << (absl::Now() - start_time);

  LOG(INFO) << "Longest Iteration: " << longest_iteration;
  LOG(INFO) << "Longest Iteration Duration: " << longest_iteration_duration;

  LOG(INFO) << "Final state:\n" << switch_state_->SwitchStateSummary();

  EXPECT_OK(environment.StoreTestArtifact("final_switch_state.txt",
                                          switch_state_->SwitchStateSummary()));

  EXPECT_OK(environment.StoreTestArtifact("error_messages.txt",
                                          absl::StrJoin(error_messages, "\n")));

  // Save switch logs at the `final_switch_state`.

  EXPECT_OK(GetParam().mirror_testbed->SaveSwitchLogs(
      /*save_prefix=*/"final_switch_state_before_clearing_"));

  // Unless we are testing a specific milestone, ensure that clearing all
  // tables succeeds. Can be safely skipped as we also clean up the switch
  // during TearDown, but is helpful to detect switch bugs.
  if (!GetParam().milestone.has_value() &&
      absl::GetFlag(FLAGS_fuzzer_clear_switch_at_end)) {
    ASSERT_OK_AND_ASSIGN(auto entities, pdpi::ReadPiEntities(session.get()));
    for (const auto& entity : entities) {
      EXPECT_OK(environment.AppendToTestArtifact(
          "clearing_pi_entities_read_from_switch.txt", entity));
    }

    // Replace sequencing and batching code with function
    // once it is available in sequencing library.

    // Sort by dependency order, then reverse since we will be deleting.
    ASSERT_OK(pdpi::StableSortEntities(config.GetIrP4Info(), entities));
    absl::c_reverse(entities);

    std::vector<p4::v1::Update> pi_updates =
        pdpi::CreatePiUpdates(entities, p4::v1::Update::DELETE);

    std::vector<WriteRequest> batched_clear_requests;
    WriteRequest request;

    std::optional<int> last_rank = std::nullopt;
    int current_rank = 0;
    // The P4 Runtime specification states that a good rule of thumb for the
    // size of request is "8192 + MAX_UPDATES_PER_WRITE * 100 bytes of
    // metadata". P4RuntimeSession uses a 1MB limit and 5000 updates falls
    // safely within those limits and is simultaneously more than we ever tend
    // to send.
    int max_batch_size = 5000;
    for (const p4::v1::Update& update : pi_updates) {
      // If the switch doesn't support fail-on-first, batch requests based on
      // rank AND number of updates.
      if (!GetParam().do_not_enforce_fail_on_first_switch_ordering) {
        ASSERT_OK_AND_ASSIGN(
            std::string table_name,
            pdpi::EntityToTableName(config.GetIrP4Info(), update.entity()));
        ASSERT_OK_AND_ASSIGN(
            current_rank,
            gutil::FindOrStatus(
                config.GetIrP4Info().dependency_rank_by_table_name(),
                table_name));
        // If we have reached a new entity rank or the limit of update size,
        // start a new request.
        if (last_rank.has_value() && *last_rank != current_rank) {
          batched_clear_requests.push_back(std::move(request));
          request = WriteRequest();
        }
      }
      if (request.updates_size() > max_batch_size) {
        batched_clear_requests.push_back(std::move(request));
        request = WriteRequest();
      }

      *request.add_updates() = update;
      last_rank = current_rank;
    }
    if (request.updates_size() > 0) {
      batched_clear_requests.push_back(std::move(request));
    }

    for (int i = 0; i < batched_clear_requests.size(); i++) {
      EXPECT_OK(environment.AppendToTestArtifact(
          "clearing_delete_write_requests.txt",
          absl::StrCat("# Delete write batch ", i + 1, ".\n")));
      EXPECT_OK(environment.AppendToTestArtifact(
          "clearing_delete_write_requests.txt", batched_clear_requests[i]));
    }
    ASSERT_OK(pdpi::SetMetadataAndSendPiWriteRequests(session.get(),
                                                      batched_clear_requests));
  }
}

bool AbslParseFlag(absl::string_view milestone_text, Milestone* milestone,
                   std::string* error) {
  for (auto& [milestone_, string] : MilestoneToStringMapping()) {
    if (string == milestone_text) {
      *milestone = milestone_;
      return true;
    }
  }
  absl::StrAppend(error, "unknown milestone: '", milestone_text, "'");
  return false;
}

std::string AbslUnparseFlag(Milestone milestone) {
  for (auto& [milestone_, string] : MilestoneToStringMapping()) {
    if (milestone_ == milestone) return string;
  }
  LOG(DFATAL) << "invalid milestone: " << static_cast<int>(milestone);
  return "<invalid_milestone>";
}

}  // namespace p4_fuzzer
