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

#include "absl/log/log.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/test_artifact_writer.h"
#include "gutil/gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/pd.h"
#include "p4_infra/p4_runtime/p4_runtime_session.h"
#include "p4_infra/packetlib/packetlib.h"
#include "p4_infra/packetlib/packetlib.pb.h"
#include "p4_infra/string_encodings/hex_string.h"
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

constexpr absl::string_view kTableEntries = R"pb(
  entries {
    acl_pre_ingress_table_entry {
      match {
        is_ip { value: "0x1" }
        is_ipv4 { value: "0x1" }
        in_port { value: "3" }
        src_mac { value: "22:22:22:11:11:11" mask: "ff:ff:ff:ff:ff:ff" }
        dst_ip { value: "10.0.10.0" mask: "255.255.255.255" }
      }
      action { set_vrf { vrf_id: "vrf-80" } }
      priority: 1
    }
  }
  entries {
    ipv4_table_entry {
      match { vrf_id: "vrf-80" }
      action { set_nexthop_id { nexthop_id: "nexthop-1" } }
    }
  }
  entries {
    l3_admit_table_entry {
      match {
        dst_mac { value: "66:55:44:33:22:10" mask: "ff:ff:ff:ff:ff:ff" }
        in_port { value: "5" }
      }
      action { admit_to_l3 {} }
      priority: 1
    }
  }
  entries {
    nexthop_table_entry {
      match { nexthop_id: "nexthop-1" }
      action {
        set_ip_nexthop {
          router_interface_id: "router-interface-1"
          neighbor_id: "fe80::cebb:aaff:fe99:8877"
        }
      }
    }
  }
  entries {
    router_interface_table_entry {
      match { router_interface_id: "router-interface-1" }
      action { set_port_and_src_mac { port: "2" src_mac: "66:55:44:33:22:11" } }
    }
  }
  entries {
    neighbor_table_entry {
      match {
        router_interface_id: "router-interface-1"
        neighbor_id: "fe80::cebb:aaff:fe99:8877"
      }
      action { set_dst_mac { dst_mac: "cc:bb:aa:99:88:77" } }
    }
  }
)pb";

class SymbolicTableEntriesSaiTest : public testing::Test {
 public:
  static constexpr absl::string_view kAclPreIngressTableName =
      "ingress.acl_pre_ingress.acl_pre_ingress_table";
  static constexpr absl::string_view kIpv4TableName =
      "ingress.routing_lookup.ipv4_table";
  static constexpr absl::string_view kL3AdmitTableName =
      "ingress.l3_admit.l3_admit_table";
  static constexpr absl::string_view kNexthopTableName =
      "ingress.routing_resolution.nexthop_table";
  static constexpr absl::string_view kRouterInterfaceTableName =
      "ingress.routing_resolution.router_interface_table";
  static constexpr absl::string_view kNeighborTableName =
      "ingress.routing_resolution.neighbor_table";

  void SetUp() override {
    config_ = sai::GetNonstandardForwardingPipelineConfig(
        sai::Instantiation::kMiddleblock,
        sai::NonstandardPlatform::kP4Symbolic);
    ASSERT_OK_AND_ASSIGN(ir_p4info_, pdpi::CreateIrP4Info(config_.p4info()));
    auto pd_entries = gutil::ParseProtoOrDie<sai::TableEntries>(kTableEntries);
    ASSERT_OK_AND_ASSIGN(
        std::vector<p4::v1::Entity> pi_entities,
        pdpi::PdTableEntriesToPiEntities(ir_p4info_, pd_entries));

    ASSERT_OK_AND_ASSIGN(ir::Dataplane dataplane,
                         ir::ParseToIr(config_, pi_entities));
    program_ = std::move(dataplane.program);
    ir_entries_ = std::move(dataplane.entries);
  }

  absl::StatusOr<ir::TableEntry> CreateSymbolicIrTableEntryForSaiTests(
      const ir::Table& table) {
    // Just use index 0 for the purposes of these tests.
    constexpr int kTableEntryIndex = 0;
    // Detect the table priority type.
    auto priority_type = symbolic::table::GetTableEntryPriorityType(table);

    // Create a symbolic IR entry based on the table priority type.
    ir::TableEntry ir_entry;
    if (priority_type ==
        symbolic::table::TableEntryPriorityType::kPositivePriority) {
      ASSIGN_OR_RETURN(*ir_entry.mutable_symbolic_entry(),
                       ir::CreateSymbolicIrTableEntry(
                           kTableEntryIndex, table,
                           ir::TableEntryPriorityParams{.priority = 1}));
    } else if (priority_type == symbolic::table::TableEntryPriorityType::
                                    kPriorityZeroWithSingleLpm) {
      ASSIGN_OR_RETURN(*ir_entry.mutable_symbolic_entry(),
                       ir::CreateSymbolicIrTableEntry(
                           kTableEntryIndex, table,
                           ir::TableEntryPriorityParams{.prefix_length = 16}));
    } else {
      ASSIGN_OR_RETURN(*ir_entry.mutable_symbolic_entry(),
                       ir::CreateSymbolicIrTableEntry(kTableEntryIndex, table));
    }
    return ir_entry;
  }

 protected:
  gutil::BazelTestArtifactWriter artifact_writer_;
  p4::v1::ForwardingPipelineConfig config_;
  pdpi::IrP4Info ir_p4info_;
  ir::P4Program program_;
  ir::TableEntries ir_entries_;
};

// TODO: Remove when packet replication is supported.
bool SaiTableCouldSetMulticastGroup(absl::string_view table_name) {
  return table_name == "ingress.routing_lookup.ipv4_multicast_table" ||
         table_name == "ingress.routing_lookup.ipv6_multicast_table" ||
         table_name ==
             "ingress.acl_ingress.acl_ingress_mirror_and_redirect_table";
}

// TODO: Re-enable this test once LPM wildcard matching is
// supported for this test.
TEST_F(SymbolicTableEntriesSaiTest, DISABLED_OneSymbolicEntryPerTable) {
  // Create a symbolic IR entry for each table.
  for (const auto& [table_name, table] : program_.tables()) {
    // Skip tables that are not in the original P4 program.
    if (table.table_definition().preamble().id() == 0) continue;
    // Skip WCMP tables. Those tables will have no entry.
    if (table.table_definition().has_action_profile_id()) continue;
    // TODO: Stop ignoring multicast when packet replication is
    // supported.
    if (SaiTableCouldSetMulticastGroup(table_name)) continue;

    ASSERT_OK_AND_ASSIGN(ir::TableEntry ir_entry,
                         CreateSymbolicIrTableEntryForSaiTests(table));
    ir_entries_[table_name].clear();
    ir_entries_[table_name].push_back(std::move(ir_entry));
  }

  // Construct physical ports and P4Runtime translation mappings.
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

  // Symbolically evaluate the program with symbolic table entries.
  LOG(INFO) << "Building model...";
  absl::Time start_time = absl::Now();
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<symbolic::SolverState> state,
      symbolic::EvaluateP4Program(program_, ir_entries_, ports, translations));
  LOG(INFO) << "-> done in " << (absl::Now() - start_time);

  // Add constraints to respect entry restrictions.
  // Right now only the entry restrictions of "vrf_table" and
  // "acl_pre_ingress_table" are implemented.
  // TODO: Remove this when P4-Constraints is integrated with
  // P4-Symbolic.
  ASSERT_OK(AddConstraintsForP4ConstraintsAnnotations(*state));

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

  // Get symbolic table matches.
  ASSERT_TRUE(
      state->context.trace.matched_entries.contains(kAclPreIngressTableName));
  ASSERT_TRUE(state->context.trace.matched_entries.contains(kIpv4TableName));
  ASSERT_TRUE(state->context.trace.matched_entries.contains(kL3AdmitTableName));
  ASSERT_TRUE(
      state->context.trace.matched_entries.contains(kNeighborTableName));
  const symbolic::SymbolicTableMatch& acl_pre_ingress_table =
      state->context.trace.matched_entries.at(kAclPreIngressTableName);
  const symbolic::SymbolicTableMatch& ipv4_table =
      state->context.trace.matched_entries.at(kIpv4TableName);
  const symbolic::SymbolicTableMatch& l3_admit_table =
      state->context.trace.matched_entries.at(kL3AdmitTableName);
  const symbolic::SymbolicTableMatch& neighbor_table =
      state->context.trace.matched_entries.at(kNeighborTableName);

  // Define criteria to hit certain tables while having the packet forwarded.
  symbolic::Assertion criteria =
      [&](const symbolic::SymbolicContext& ctx) -> absl::StatusOr<z3::expr> {
    ASSIGN_OR_RETURN(
        z3::expr recirculated,
        ctx.egress_headers.Get(symbolic::kGotRecirculatedPseudoField));
    return acl_pre_ingress_table.matched &&
           acl_pre_ingress_table.entry_index == 0 && ipv4_table.matched &&
           ipv4_table.entry_index == 0 && l3_admit_table.matched &&
           l3_admit_table.entry_index == 0 && neighbor_table.matched &&
           neighbor_table.entry_index == 0 && !ctx.trace.dropped &&
           ctx.egress_port == 2 &&
           // Otherwise the drop expectation may be inconsistent with BMv2
           // (b/345589897).
           !recirculated;
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

  // Check some properties of the solution.
  EXPECT_EQ(Z3ValueStringToInt(solution->egress_port), 2);
  EXPECT_FALSE(solution->trace.dropped);

  ASSERT_TRUE(
      solution->trace.matched_entries.contains(kAclPreIngressTableName));
  EXPECT_TRUE(
      solution->trace.matched_entries.at(kAclPreIngressTableName).matched);
  EXPECT_EQ(
      solution->trace.matched_entries.at(kAclPreIngressTableName).entry_index,
      0);

  ASSERT_TRUE(solution->trace.matched_entries.contains(kIpv4TableName));
  EXPECT_TRUE(solution->trace.matched_entries.at(kIpv4TableName).matched);
  EXPECT_EQ(solution->trace.matched_entries.at(kIpv4TableName).entry_index, 0);

  ASSERT_TRUE(solution->trace.matched_entries.contains(kL3AdmitTableName));
  EXPECT_TRUE(solution->trace.matched_entries.at(kL3AdmitTableName).matched);
  EXPECT_EQ(solution->trace.matched_entries.at(kL3AdmitTableName).entry_index,
            0);

  ASSERT_TRUE(solution->trace.matched_entries.contains(kNexthopTableName));
  EXPECT_TRUE(solution->trace.matched_entries.at(kNexthopTableName).matched);
  EXPECT_EQ(solution->trace.matched_entries.at(kNexthopTableName).entry_index,
            0);

  ASSERT_TRUE(
      solution->trace.matched_entries.contains(kRouterInterfaceTableName));
  EXPECT_TRUE(
      solution->trace.matched_entries.at(kRouterInterfaceTableName).matched);
  EXPECT_EQ(
      solution->trace.matched_entries.at(kRouterInterfaceTableName).entry_index,
      0);

  ASSERT_TRUE(solution->trace.matched_entries.contains(kNeighborTableName));
  EXPECT_TRUE(solution->trace.matched_entries.at(kNeighborTableName).matched);
  EXPECT_EQ(solution->trace.matched_entries.at(kNeighborTableName).entry_index,
            0);
}

// TODO: Re-enable this test once LPM wildcard matching is
// supported for this test.
TEST_F(SymbolicTableEntriesSaiTest,
       DISABLED_MixtureOfSymbolicAndConcreteEntries) {
  // Create a symbolic IR entry for each empty table.
  for (const auto& [table_name, table] : program_.tables()) {
    // Skip tables that are not in the original P4 program.
    if (table.table_definition().preamble().id() == 0) continue;
    // Skip WCMP tables. Those tables will have no entry.
    if (table.table_definition().has_action_profile_id()) continue;
    // TODO: Stop ignoring multicast when packet replication is
    // supported.
    if (SaiTableCouldSetMulticastGroup(table_name)) continue;

    ASSERT_OK_AND_ASSIGN(ir::TableEntry ir_entry,
                         CreateSymbolicIrTableEntryForSaiTests(table));
    if (auto it = ir_entries_.find(table_name);
        it == ir_entries_.end() || it->second.empty()) {
      ir_entries_[table_name].push_back(std::move(ir_entry));
    }
  }

  // Construct physical ports and P4Runtime translation mappings.
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

  // Symbolically evaluate the program with symbolic table entries.
  LOG(INFO) << "Building model...";
  absl::Time start_time = absl::Now();
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<symbolic::SolverState> state,
      symbolic::EvaluateP4Program(program_, ir_entries_, ports, translations));
  LOG(INFO) << "-> done in " << (absl::Now() - start_time);

  // Add constraints to respect entry restrictions.
  // Right now only the entry restrictions of "vrf_table" and
  // "acl_pre_ingress_table" are implemented.
  // TODO: Remove this when P4-Constraints is integrated with
  // P4-Symbolic.
  ASSERT_OK(AddConstraintsForP4ConstraintsAnnotations(*state));

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

  // Get symbolic table matches.
  ASSERT_TRUE(
      state->context.trace.matched_entries.contains(kRouterInterfaceTableName));
  ASSERT_TRUE(
      state->context.trace.matched_entries.contains(kNeighborTableName));
  const symbolic::SymbolicTableMatch& router_interface_table =
      state->context.trace.matched_entries.at(kRouterInterfaceTableName);
  const symbolic::SymbolicTableMatch& neighbor_table =
      state->context.trace.matched_entries.at(kNeighborTableName);

  // Define criteria to hit all concrete entries while having the packet
  // forwarded.
  symbolic::Assertion criteria =
      [&](const symbolic::SymbolicContext& ctx) -> absl::StatusOr<z3::expr> {
    ASSIGN_OR_RETURN(
        z3::expr recirculated,
        ctx.egress_headers.Get(symbolic::kGotRecirculatedPseudoField));
    return router_interface_table.matched &&
           router_interface_table.entry_index == 0 && neighbor_table.matched &&
           neighbor_table.entry_index == 0 && !ctx.trace.dropped &&
           // Otherwise the drop expectation may be inconsistent with BMv2
           // (b/345589897).
           !recirculated;
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

  // Check some properties of the solution.
  EXPECT_EQ(Z3ValueStringToInt(solution->egress_port), 2);
  EXPECT_FALSE(solution->trace.dropped);

  ASSERT_TRUE(solution->trace.matched_entries.contains(kNexthopTableName));
  EXPECT_TRUE(solution->trace.matched_entries.at(kNexthopTableName).matched);
  EXPECT_EQ(solution->trace.matched_entries.at(kNexthopTableName).entry_index,
            0);

  ASSERT_TRUE(
      solution->trace.matched_entries.contains(kRouterInterfaceTableName));
  EXPECT_TRUE(
      solution->trace.matched_entries.at(kRouterInterfaceTableName).matched);
  EXPECT_EQ(
      solution->trace.matched_entries.at(kRouterInterfaceTableName).entry_index,
      0);

  ASSERT_TRUE(solution->trace.matched_entries.contains(kNeighborTableName));
  EXPECT_TRUE(solution->trace.matched_entries.at(kNeighborTableName).matched);
  EXPECT_EQ(solution->trace.matched_entries.at(kNeighborTableName).entry_index,
            0);
}

// TODO: Re-enable this test once LPM wildcard matching is
// supported for this test.
TEST_F(SymbolicTableEntriesSaiTest,
       DISABLED_OneSymbolicEntryPerTableWithTunnelDecap) {
  // Create a symbolic IR entry for each empty table.
  for (const auto& [table_name, table] : program_.tables()) {
    // Skip tables that are not in the original P4 program.
    if (table.table_definition().preamble().id() == 0) continue;
    // Skip WCMP tables. Those tables will have no entry.
    if (table.table_definition().has_action_profile_id()) continue;
    // TODO: Stop ignoring multicast when packet replication is
    // supported.
    if (SaiTableCouldSetMulticastGroup(table_name)) continue;

    ASSERT_OK_AND_ASSIGN(ir::TableEntry ir_entry,
                         CreateSymbolicIrTableEntryForSaiTests(table));
    ir_entries_[table_name].clear();
    ir_entries_[table_name].push_back(std::move(ir_entry));
  }

  // Construct physical ports and P4Runtime translation mappings.
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

  // Symbolically evaluate the program with symbolic table entries.
  LOG(INFO) << "Building model...";
  absl::Time start_time = absl::Now();
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<symbolic::SolverState> state,
      symbolic::EvaluateP4Program(program_, ir_entries_, ports, translations));
  LOG(INFO) << "-> done in " << (absl::Now() - start_time);

  // TODO: Remove this when P4-Constraints is integrated with
  // P4-Symbolic.
  ASSERT_OK(AddConstraintsForP4ConstraintsAnnotations(*state));

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

  // Define table names.
  constexpr absl::string_view tunnel_termination_table_name =
      "ingress.tunnel_termination.ipv6_tunnel_termination_table";
  ASSERT_TRUE(state->context.trace.matched_entries.contains(
      tunnel_termination_table_name));
  const symbolic::SymbolicTableMatch& tunnel_termination_table =
      state->context.trace.matched_entries.at(tunnel_termination_table_name);

  // Define criteria to hit certain tables while having the packet forwarded.
  symbolic::Assertion criteria =
      [&](const symbolic::SymbolicContext& ctx) -> absl::StatusOr<z3::expr> {
    ASSIGN_OR_RETURN(
        z3::expr recirculated,
        ctx.egress_headers.Get(symbolic::kGotRecirculatedPseudoField));
    return tunnel_termination_table.matched &&
           tunnel_termination_table.entry_index == 0 && !ctx.trace.dropped &&
           // Otherwise the drop expectation may be inconsistent with BMv2
           // (b/345589897).
           !recirculated;
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

  // Check some properties of the solution.
  EXPECT_FALSE(solution->trace.dropped);
  ASSERT_TRUE(
      solution->trace.matched_entries.contains(tunnel_termination_table_name));
  EXPECT_TRUE(solution->trace.matched_entries.at(tunnel_termination_table_name)
                  .matched);
  EXPECT_EQ(solution->trace.matched_entries.at(tunnel_termination_table_name)
                .entry_index,
            0);
}

}  // namespace
}  // namespace p4_symbolic
