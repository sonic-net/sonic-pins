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

#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "gutil/test_artifact_writer.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_symbolic/ir/ir.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/ir/parser.h"
#include "p4_symbolic/ir/table_entries.h"
#include "p4_symbolic/sai/sai.h"
#include "p4_symbolic/symbolic/context.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/symbolic/table.h"
#include "p4_symbolic/symbolic/values.h"
#include "p4_symbolic/test_util.h"
#include "p4_symbolic/z3_util.h"
#include "z3++.h"

namespace p4_symbolic {
namespace {

class SymbolicTableEntriesIPv4BasicTest : public testing::Test {
 public:
  void SetUp() override {
    constexpr absl::string_view bmv2_json_path =
        "p4_symbolic/testdata/ipv4-routing/"
        "basic.config.json";
    constexpr absl::string_view p4info_path =
        "p4_symbolic/testdata/ipv4-routing/"
        "basic.p4info.pb.txt";
    constexpr absl::string_view entries_path =
        "p4_symbolic/testdata/ipv4-routing/"
        "entries.pb.txt";
    ASSERT_OK_AND_ASSIGN(
        p4::v1::ForwardingPipelineConfig config,
        ParseToForwardingPipelineConfig(bmv2_json_path, p4info_path));
    ASSERT_OK_AND_ASSIGN(
        std::vector<p4::v1::TableEntry> pi_entries,
        GetPiTableEntriesFromPiUpdatesProtoTextFile(entries_path));
    ASSERT_OK_AND_ASSIGN(ir::Dataplane dataplane,
                         ir::ParseToIr(config, pi_entries));
    program_ = std::move(dataplane.program);
    ir_entries_ = std::move(dataplane.entries);
  }

 protected:
  gutil::BazelTestArtifactWriter artifact_writer_;
  ir::P4Program program_;
  ir::TableEntries ir_entries_;
};

TEST_F(SymbolicTableEntriesIPv4BasicTest, OneSymbolicEntryPerTable) {
  constexpr int kTableEntryIndex = 0;
  constexpr auto kTieBrakers = ir::TableEntryPriorityParams{
      .priority = 0,
      .prefix_length = 16,
  };

  // Remove all existing concrete table entries.
  ir_entries_.clear();

  // Create a symbolic IR entry for each table.
  for (const auto& [table_name, table] : program_.tables()) {
    // Skip tables that are not in the original P4 program.
    if (table.table_definition().preamble().id() == 0) continue;
    ASSERT_OK_AND_ASSIGN(
        *ir_entries_[table_name].emplace_back().mutable_symbolic_entry(),
        ir::CreateSymbolicIrTableEntry(kTableEntryIndex, table, kTieBrakers));
  }

  // Symbolically evaluate the program with symbolic table entries.
  std::vector<int> ports = {1, 2, 3, 4, 5};
  symbolic::TranslationPerType translations;
  translations[p4_symbolic::kPortIdTypeName] =
      symbolic::values::TranslationData{
          .static_mapping = {{"1", 1}, {"2", 2}, {"3", 3}, {"4", 4}, {"5", 5}},
          .dynamic_translation = false,
      };
  translations[p4_symbolic::kVrfIdTypeName] = symbolic::values::TranslationData{
      .static_mapping = {{"", 0}},
      .dynamic_translation = true,
  };
  LOG(INFO) << "Building model...";
  absl::Time start_time = absl::Now();
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<symbolic::SolverState> state,
      symbolic::EvaluateP4Program(program_, ir_entries_, ports, translations));
  LOG(INFO) << "-> done in " << (absl::Now() - start_time);

  // Dump solver state.
  for (const auto& [table_name, entries] : state->context.table_entries) {
    std::string banner =
        absl::StrCat("== ", table_name, " ",
                     std::string(80 - table_name.size() - 4, '='), "\n");
    EXPECT_OK(artifact_writer_.AppendToTestArtifact(
        "input_table_entries.textproto", banner));
    for (const auto& entry : entries) {
      EXPECT_OK(artifact_writer_.AppendToTestArtifact(
          "input_table_entries.textproto", entry));
    }
  }
  EXPECT_OK(
      artifact_writer_.StoreTestArtifact("program.textproto", state->program));
  EXPECT_OK(artifact_writer_.StoreTestArtifact(
      "all_smt_formulae.txt", state->GetHeadersAndSolverConstraintsSMT()));

  // Define criteria to hit the ipv4_lpm table and have the packet forwarded.
  constexpr absl::string_view table_name = "MyIngress.ipv4_lpm";
  ASSERT_OK_AND_ASSIGN(
      z3::expr egress_spec_of_ingress_packet,
      state->context.ingress_headers.Get("standard_metadata.egress_spec"));
  ASSERT_TRUE(state->context.trace.matched_entries.contains(table_name));
  const symbolic::SymbolicTableMatch& lpm_table =
      state->context.trace.matched_entries.at(table_name);
  symbolic::Assertion criteria =
      [&egress_spec_of_ingress_packet,
       &lpm_table](const symbolic::SymbolicContext& ctx) -> z3::expr {
    // TODO: Remove this once cl/550894398 is submitted.
    z3::expr ingress_constraint = (egress_spec_of_ingress_packet == 0);
    return lpm_table.matched && !ctx.trace.dropped && ctx.egress_port == 3 &&
           ingress_constraint;
  };
  EXPECT_OK(artifact_writer_.StoreTestArtifact(
      "criteria.smt.txt", symbolic::DebugSMT(state, criteria)));

  // Solve for a concrete solution given the criteria.
  ASSERT_OK_AND_ASSIGN(std::optional<symbolic::ConcreteContext> solution,
                       symbolic::Solve(*state, criteria));
  ASSERT_TRUE(solution.has_value());

  // Dump the concrete context.
  EXPECT_OK(artifact_writer_.StoreTestArtifact(
      "solution.txt", solution->to_string(/*verbose=*/true)));
  // Dump the table entries.
  for (const auto& [table_name, entries] : solution->table_entries) {
    std::string banner =
        absl::StrCat("== ", table_name, " ",
                     std::string(80 - table_name.size() - 4, '='), "\n");
    EXPECT_OK(artifact_writer_.AppendToTestArtifact(
        "concrete_table_entries.textproto", banner));
    for (const auto& entry : entries) {
      EXPECT_OK(artifact_writer_.AppendToTestArtifact(
           "concrete_table_entries.textproto", entry));
    }
  }

  // Check properties of the solution.
  EXPECT_EQ(Z3ValueStringToInt(solution->egress_port), 3);
  EXPECT_FALSE(solution->trace.dropped);
  ASSERT_EQ(solution->trace.matched_entries.size(), 1);
  ASSERT_TRUE(solution->trace.matched_entries.contains(table_name));
  EXPECT_TRUE(solution->trace.matched_entries.at(table_name).matched);
  EXPECT_EQ(solution->trace.matched_entries.at(table_name).entry_index, 0);
}

}  // namespace
}  // namespace p4_symbolic
