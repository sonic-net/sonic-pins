#include "p4_fuzzer/fuzzer_tests.h"

#include <algorithm>
#include <set>

#include "absl/container/flat_hash_set.h"
#include "absl/flags/flag.h"
#include "absl/random/random.h"
#include "absl/random/seed_sequences.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/substitute.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "lib/gnmi/gnmi_helper.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_fuzzer/annotation_util.h"
#include "p4_fuzzer/fuzz_util.h"
#include "p4_fuzzer/fuzzer.pb.h"
#include "p4_fuzzer/switch_state.h"
#include "p4_pdpi/connection_management.h"
#include "p4_pdpi/entity_management.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/sequencing.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "thinkit/mirror_testbed_fixture.h"
#include "thinkit/test_environment.h"

ABSL_FLAG(int, fuzzer_iterations, 1000,
          "Number of updates the fuzzer should generate.");

namespace p4_fuzzer {

using ::p4::v1::WriteRequest;

TEST_P(FuzzTest, P4rtWriteAndCheckNoInternalErrors) {
  thinkit::Switch& sut = GetMirrorTestbed().Sut();
  thinkit::TestEnvironment& environment = GetMirrorTestbed().Environment();

  pdpi::IrP4Info info = sai::GetIrP4Info(sai::SwitchRole::kMiddleblock);
  FuzzerConfig config = {
      .info = info,
      .ports = {"1"},
      .qos_queues = {"0x1"},
      .role = "sdn_controller",
  };

  bool mask_known_failures = environment.MaskKnownFailures();

  // Push the gnmi configuration.
  ASSERT_OK(
      pins_test::PushGnmiConfig(GetMirrorTestbed().Sut(), GetGnmiConfig()));
  ASSERT_OK(pins_test::PushGnmiConfig(GetMirrorTestbed().ControlSwitch(),
                                      GetGnmiConfig()));

  // Initialize connection.
  ASSERT_OK_AND_ASSIGN(auto stub, sut.CreateP4RuntimeStub());
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<pdpi::P4RuntimeSession> session,
      pdpi::P4RuntimeSession::Create(std::move(stub), sut.DeviceId()));
  ASSERT_OK(pdpi::SetForwardingPipelineConfig(
      session.get(), sai::GetP4Info(sai::SwitchRole::kMiddleblock)));

  // Clear switch state.
  ASSERT_OK(pdpi::ClearTableEntries(session.get(), info));

  absl::BitGen gen;

  // Run fuzzer.
  int num_updates = 0;
  int num_ok_statuses = 0;
  int num_notok_without_mutations = 0;
  int num_ok_with_mutations = 0;
  int max_batch_size = 0;
  std::set<std::string> error_messages;
  SwitchState state(info);
  int num_iterations = absl::GetFlag(FLAGS_fuzzer_iterations);
  for (int i = 0; i < num_iterations; i++) {
    if (i % 100 == 0) LOG(INFO) << "Starting iteration " << (i + 1);

    // Generated fuzzed request.
    AnnotatedWriteRequest annotated_request =
        FuzzWriteRequest(&gen, config, state);
    WriteRequest request = RemoveAnnotations(annotated_request);
    num_updates += request.updates_size();
    max_batch_size = std::max(max_batch_size, request.updates_size());
    // Set IDs.
    request.set_device_id(session->DeviceId());
    *request.mutable_election_id() = session->ElectionId();

    ASSERT_OK(environment.AppendToTestArtifact(
        "requests_and_responses.txt",
        absl::StrCat("# Write request number ", i + 1, "\n",
                     MakeReadable(annotated_request).DebugString())));
    ASSERT_OK(environment.AppendToTestArtifact("pi_write_request_trace.txt",
                                               request.DebugString()));

    // Send to switch.
    grpc::ClientContext context;
    p4::v1::WriteResponse pi_response;
    ASSERT_OK_AND_ASSIGN(
        pdpi::IrWriteRpcStatus response,
        pdpi::GrpcStatusToIrWriteRpcStatus(
            session->Stub().Write(&context, request, &pi_response),
            request.updates_size()));

    ASSERT_OK(environment.AppendToTestArtifact(
        "requests_and_responses.txt",
        absl::StrCat("# Response to request number ", i + 1, "\n",
                     response.DebugString())));

    // TODO: enable this once the switch actually returns a real reply
    // for all inputs.
    if (!mask_known_failures) {
      ASSERT_TRUE(response.has_rpc_response())
          << "Expected proper response, but got: " << response.DebugString();
    }
    if (response.has_rpc_response()) {
      for (int i = 0; i < response.rpc_response().statuses().size(); i++) {
        const pdpi::IrUpdateStatus& status =
            response.rpc_response().statuses(i);
        const p4::v1::Update& update = request.updates(i);

        // TODO: enable this once the switch stops returning INTERNAL
        // errors.
        if (!mask_known_failures) {
          EXPECT_NE(status.code(), google::rpc::Code::INTERNAL)
              << "Fuzzing should never cause an INTERNAL error, but got: "
              << status.DebugString();
        }
        // Check resource exhaustion.
        if (status.code() == google::rpc::Code::RESOURCE_EXHAUSTED) {
          int table_id = update.entity().table_entry().table_id();
          ASSERT_OK_AND_ASSIGN(
              const pdpi::IrTableDefinition& table,
              gutil::FindOrStatus(info.tables_by_id(), table_id));
          // TODO: acl_lookup_table has a resource limit problem.
          // TODO: router_interface_table, ipv4_table and
          // ipv6_table all have resource limit problems.
          // TODO: wcmp_group_table has a resource limit problem.
          if (!(mask_known_failures &&
                (table.preamble().alias() == "acl_lookup_table" ||
                 table.preamble().alias() == "router_interface_table" ||
                 table.preamble().alias() == "ipv4_table" ||
                 table.preamble().alias() == "ipv6_table" ||
                 table.preamble().alias() == "wcmp_group_table"))) {
            // Check that table was full before this status.
            ASSERT_TRUE(state.IsTableFull(table_id)) << absl::Substitute(
                "Switch reported RESOURCE_EXHAUSTED for table named '$0'. The "
                "table currently has $1 entries, but is supposed to support at "
                "least $2 entries.\nUpdate = $3\nState = $4",
                table.preamble().alias(), state.GetNumTableEntries(table_id),
                table.size(), update.DebugString(), state.SwitchStateSummary());
          }
        }
        // Collect error messages and update state.
        if (status.code() != google::rpc::Code::OK) {
          error_messages.insert(absl::StrCat(
              google::rpc::Code_Name(status.code()), ": ", status.message()));
        } else {
          ASSERT_OK(state.ApplyUpdate(update));
          num_ok_statuses += 1;
        }

        bool is_mutated = annotated_request.updates(i).mutations_size() > 0;

        // If the Fuzzer uses a mutation, then the update is likely to be
        // invalid.
        if (status.code() == google::rpc::Code::OK && is_mutated) {
          EXPECT_OK(environment.AppendToTestArtifact(
              "fuzzer_mutated_but_ok.txt",
              absl::StrCat("-------------------\n\nRequest = \n",
                           annotated_request.updates(i).DebugString())));
          num_ok_with_mutations++;
        }

        if (status.code() != google::rpc::Code::OK &&
            status.code() != google::rpc::Code::RESOURCE_EXHAUSTED &&
            status.code() != google::rpc::Code::UNIMPLEMENTED) {
          if (!is_mutated) {
            // Switch did not consider update OK but fuzzer did not use a
            // mutation (i.e. thought the update should be valid).
            EXPECT_OK(environment.AppendToTestArtifact(
                "fuzzer_inaccuracies.txt",
                absl::StrCat("-------------------\n\nrequest = \n",
                             annotated_request.updates(i).DebugString(),
                             "\n\nstatus = \n", status.DebugString())));
            EXPECT_OK(environment.AppendToTestArtifact(
                "fuzzer_inaccuracies_short.txt",
                absl::StrCat(status.message(), "\n")));
            num_notok_without_mutations += 1;
          }
        }
      }
    }
  }

  LOG(INFO) << "Finished " << num_iterations << " iterations.";
  LOG(INFO) << "  num_updates:                 " << num_updates;
  // Expected value is 50, so if it's very far from that, we probably have a
  // problem.
  LOG(INFO) << "  Avg updates per request:     "
            << num_updates / static_cast<double>(num_iterations);
  LOG(INFO) << "  max updates in a request:    " << max_batch_size;
  LOG(INFO) << "  num_ok_statuses:             " << num_ok_statuses;

  // These should be 0 if the fuzzer works optimally. These numbers do not
  // affect the soundness of the fuzzer, just the modularity, so it is a goal
  // that we are not 100% strict on as it would be incredibly challenging to
  // enforce. However, it is highly likely that bugs in the switch, which we
  // can't currently detect, are hidden in these numbers.
  LOG(INFO) << "  num_notok_without_mutations: " << num_notok_without_mutations;
  LOG(INFO) << "  num_ok_with_mutations: " << num_ok_with_mutations;

  LOG(INFO) << "Final state:";
  LOG(INFO) << state.SwitchStateSummary();

  EXPECT_OK(environment.StoreTestArtifact("final_switch_state.txt",
                                          state.SwitchStateSummary()));

  EXPECT_OK(environment.StoreTestArtifact("error_messages.txt",
                                          absl::StrJoin(error_messages, "\n")));

  // Leave the switch in a clean state and log the final state to help with
  // debugging.
  // TODO: Clean-up has a known bug where deletion of existing
  // table entries fails.
  if (!mask_known_failures) {
    ASSERT_OK_AND_ASSIGN(auto table_entries,
                         pdpi::ReadPiTableEntries(session.get()));
    for (const auto& entry : table_entries) {
      EXPECT_OK(environment.AppendToTestArtifact(
          "clearing__pi_entries_read_from_switch.txt", entry));
    }
    std::vector<p4::v1::Update> pi_updates =
        pdpi::CreatePiUpdates(table_entries, p4::v1::Update::DELETE);
    ASSERT_OK_AND_ASSIGN(
        std::vector<p4::v1::WriteRequest> sequenced_clear_requests,
        pdpi::SequencePiUpdatesIntoWriteRequests(info, pi_updates));

    for (int i = 0; i < sequenced_clear_requests.size(); i++) {
      EXPECT_OK(environment.AppendToTestArtifact(
          "clearing__delete_write_requests.txt",
          absl::StrCat("# Delete write batch ", i + 1, ".\n")));
      EXPECT_OK(environment.AppendToTestArtifact(
          "clearing__delete_write_requests.txt", sequenced_clear_requests[i]));
    }
    ASSERT_OK(pdpi::SetMetadataAndSendPiWriteRequests(
        session.get(), sequenced_clear_requests));
  }
}

}  // namespace p4_fuzzer
