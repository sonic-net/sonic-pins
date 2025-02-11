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
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "gutil/test_artifact_writer.h"
#include "gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/internal/ordered_map.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_pdpi/pd.h"
#include "p4_pdpi/string_encodings/hex_string.h"
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
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_nonstandard_platforms.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "tests/forwarding/packet_at_port.h"
#include "z3++.h"

namespace p4_symbolic {
namespace {

using MatchType = ::p4::config::v1::MatchField::MatchType;

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
        config_, ParseToForwardingPipelineConfig(bmv2_json_path, p4info_path));
    ASSERT_OK_AND_ASSIGN(ir_p4info_, pdpi::CreateIrP4Info(config_.p4info()));
    ASSERT_OK_AND_ASSIGN(const std::vector<p4::v1::Entity> pi_entities,
                         GetPiEntitiesFromPiUpdatesProtoTextFile(entries_path));
    ASSERT_OK_AND_ASSIGN(ir::Dataplane dataplane,
                         ir::ParseToIr(config_, pi_entities));
    program_ = std::move(dataplane.program);
    ir_entries_ = std::move(dataplane.entries);
  }

 protected:
  gutil::BazelTestArtifactWriter artifact_writer_;
  p4::v1::ForwardingPipelineConfig config_;
  pdpi::IrP4Info ir_p4info_;
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
  constexpr absl::string_view kIpv4LpmTableName = "MyIngress.ipv4_lpm";
  ASSERT_TRUE(state->context.trace.matched_entries.contains(kIpv4LpmTableName));
  const symbolic::SymbolicTableMatch& lpm_table =
      state->context.trace.matched_entries.at(kIpv4LpmTableName);
  symbolic::Assertion criteria =
      [&lpm_table](const symbolic::SymbolicContext& ctx) -> z3::expr {
    return lpm_table.matched && !ctx.trace.dropped && ctx.egress_port == 3;
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
  ASSERT_TRUE(solution->trace.matched_entries.contains(kIpv4LpmTableName));
  EXPECT_TRUE(solution->trace.matched_entries.at(kIpv4LpmTableName).matched);
  EXPECT_EQ(solution->trace.matched_entries.at(kIpv4LpmTableName).entry_index,
            0);
}

}  // namespace
}  // namespace p4_symbolic
