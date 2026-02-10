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
#include <vector>

#include "absl/log/log.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/optional.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/netaddr/ipv4_address.h"
#include "p4_infra/p4_pdpi/netaddr/mac_address.h"
#include "p4_infra/p4_pdpi/pd.h"
#include "p4_symbolic/sai/sai.h"
#include "p4_symbolic/symbolic/context.h"
#include "p4_symbolic/symbolic/solver_state.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/symbolic/values.h"
#include "p4_symbolic/z3_util.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_nonstandard_platforms.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"
#include "thinkit/bazel_test_environment.h"
#include "z3++.h"

namespace p4_symbolic {
namespace {

using ::gutil::ParseProtoOrDie;
using ::testing::AnyOf;
using ::testing::Eq;
using ::testing::Not;

constexpr absl::string_view kTableEntries = R"pb(
  entries {
    acl_pre_ingress_table_entry {
      match {
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

constexpr absl::string_view kTableEntriesWithTunneling = R"pb(
  entries {
    acl_pre_ingress_table_entry {
      match { src_mac { value: "01:02:03:04:05:06" mask: "ff:ff:ff:ff:ff:ff" } }
      action { set_vrf { vrf_id: "vrf-1" } }
      priority: 1
    }
  }

  entries {
    ipv4_table_entry {
      match {
        vrf_id: "vrf-1"
        ipv4_dst { value: "10.0.0.5" prefix_length: 32 }
      }
      action {
        set_wcmp_group_id_and_metadata {
          wcmp_group_id: "group-1"
          route_metadata: "0x01"
        }
      }
    }
  }

  entries {
    wcmp_group_table_entry {
      match { wcmp_group_id: "group-1" }
      wcmp_actions {
        action { set_nexthop_id { nexthop_id: "nexthop-1" } }
        weight: 1
        watch_port: "2"
      }
      wcmp_actions {
        action { set_nexthop_id { nexthop_id: "nexthop-2" } }
        weight: 1
        watch_port: "4"
      }
    }
  }

  entries {
    nexthop_table_entry {
      match { nexthop_id: "nexthop-1" }
      action { set_p2p_tunnel_encap_nexthop { tunnel_id: "tunnel-1" } }
    }
  }

  entries {
    tunnel_table_entry {
      match { tunnel_id: "tunnel-1" }
      action {
        mark_for_p2p_tunnel_encap {
          encap_src_ip: "0001:0002:0003:0004::"
          encap_dst_ip: "0005:0006:0007:0008::"
          router_interface_id: "router-interface-1"
        }
      }
    }
  }

  entries {
    neighbor_table_entry {
      match {
        router_interface_id: "router-interface-1"
        neighbor_id: "fe80::508:09ff:fe0a:0b0c"
      }
      action { set_dst_mac { dst_mac: "07:08:09:0a:0b:0c" } }
    }
  }

  entries {
    router_interface_table_entry {
      match { router_interface_id: "router-interface-1" }
      action { set_port_and_src_mac { port: "2" src_mac: "0d:0e:0f:10:11:12" } }
    }
  }
)pb";

absl::StatusOr<std::string> GenerateSmtForSaiPiplelineWithSimpleEntries() {
  const auto config = sai::GetNonstandardForwardingPipelineConfig(
      sai::Instantiation::kMiddleblock, sai::NonstandardPlatform::kP4Symbolic);
  ASSIGN_OR_RETURN(const pdpi::IrP4Info ir_p4info,
                   pdpi::CreateIrP4Info(config.p4info()));
  auto pd_entries = ParseProtoOrDie<sai::TableEntries>(kTableEntries);
  ASSIGN_OR_RETURN(std::vector<p4::v1::Entity> pi_entities,
                   pdpi::PdTableEntriesToPiEntities(ir_p4info, pd_entries));

  ASSIGN_OR_RETURN(std::unique_ptr<symbolic::SolverState> solver,
                   symbolic::EvaluateP4Program(config, pi_entities));
  return solver->GetSolverSMT();
}

// Generate SMT constraints for the SAI pipeline from scratch multiple times and
// make sure the results remain the same.
TEST(P4SymbolicIntegrationTest, ConstraintGenerationIsDeterministicForSai) {
  constexpr int kNumberOfRuns = 5;
  ASSERT_OK_AND_ASSIGN(const std::string reference_smt_formula,
                       GenerateSmtForSaiPiplelineWithSimpleEntries());
  for (int run = 0; run < kNumberOfRuns; ++run) {
    LOG(INFO) << "Run " << run;
    ASSERT_OK_AND_ASSIGN(const std::string smt_formula,
                         GenerateSmtForSaiPiplelineWithSimpleEntries());
    ASSERT_THAT(smt_formula, Eq(reference_smt_formula));
  }
}

TEST(P4SymbolicIntegrationTest, CanGenerateTestPacketsForSimpleSaiP4Entries) {
  // Some constants.
  auto env = thinkit::BazelTestEnvironment(/*mask_known_failures=*/false);
  const auto config = sai::GetNonstandardForwardingPipelineConfig(
      sai::Instantiation::kMiddleblock, sai::NonstandardPlatform::kP4Symbolic);
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(config.p4info()));
  EXPECT_OK(env.StoreTestArtifact("ir_p4info.txtpb", ir_p4info));
  EXPECT_OK(env.StoreTestArtifact("p4_config.json", config.p4_device_config()));

  // Prepare hard-coded table entries.
  auto pd_entries = ParseProtoOrDie<sai::TableEntries>(kTableEntries);
  EXPECT_OK(env.StoreTestArtifact("pd_entries.txtpb", pd_entries));
  ASSERT_OK_AND_ASSIGN(std::vector<p4::v1::Entity> pi_entities,
                       pdpi::PdTableEntriesToPiEntities(ir_p4info, pd_entries));

  // Symbolically evaluate program.
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
  LOG(INFO) << "building model (this may take a while) ...";
  absl::Time start_time = absl::Now();
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<symbolic::SolverState> solver_state,
      symbolic::EvaluateP4Program(config, pi_entities, ports, translations));
  LOG(INFO) << "-> done in " << (absl::Now() - start_time);

  // Dump solver state.
  for (const auto& [name, entries] : solver_state->context.table_entries) {
    std::string banner = absl::StrCat(
        "== ", name, " ", std::string(80 - name.size() - 4, '='), "\n");
    EXPECT_OK(env.AppendToTestArtifact("p4symbolic_ir_entries.txtpb", banner));
    for (const auto& entry : entries) {
      EXPECT_OK(env.AppendToTestArtifact("p4symbolic_ir_entries.txtpb", entry));
    }
  }
  EXPECT_OK(env.StoreTestArtifact("program.txtpb", solver_state->program));

  // Define assertion to hit IPv4 table entry, and solve for it.
  symbolic::Assertion hit_ipv4_table_entry =
      [](const symbolic::SymbolicContext& ctx) -> z3::expr {
    CHECK_NE(
        ctx.trace.matched_entries.count("ingress.routing_lookup.ipv4_table"),
        0);
    auto ipv4_table =
        ctx.trace.matched_entries.at("ingress.routing_lookup.ipv4_table");
    return ipv4_table.matched && ipv4_table.entry_index == 0 &&
           !ctx.trace.dropped;
  };
  EXPECT_OK(env.StoreTestArtifact(
      "hit_ipv4_table_entry.smt",
      symbolic::DebugSMT(solver_state, hit_ipv4_table_entry)));
  ASSERT_OK_AND_ASSIGN(absl::optional<symbolic::ConcreteContext> solution,
                       symbolic::Solve(*solver_state, hit_ipv4_table_entry));
  ASSERT_THAT(solution, Not(Eq(absl::nullopt)));
  EXPECT_OK(env.StoreTestArtifact("hit_ipv4_table_entry.solution.txt",
                                  solution->to_string(/*verbose=*/true)));

  // Check some properties of the solution.
  const auto& ingress = solution->ingress_headers;
  const auto& egress = solution->egress_headers;
  // Check Ingress.
  EXPECT_EQ(ingress.at("ethernet.src_addr"), "#x222222111111");
  std::string ether_type = ingress.at("ethernet.ether_type");
  if (ether_type == "#x8100")
    ether_type = egress.at("vlan.ether_type");  
  EXPECT_EQ(ether_type, "#x0800");
  EXPECT_EQ(ingress.at("ipv4.dst_addr"), "#x0a000a00");
  // Check Egress.
  EXPECT_EQ(egress.at("ethernet.dst_addr"), "#xccbbaa998877");
  EXPECT_EQ(egress.at("ethernet.src_addr"), "#x665544332211");

  // Make sure local_metadata.ingress_port is as expected.
  ASSERT_OK_AND_ASSIGN(
      const std::string local_metadata_ingress_port,
      p4_symbolic::GetLocalMetadataIngressPortFromModel(*solver_state));
  EXPECT_THAT(local_metadata_ingress_port, Eq("3"));

  // Make sure standard_metadata.egress_port and standard_metadata.egress_spec
  // are as expected.
  EXPECT_EQ(Z3ValueStringToInt(egress.at("standard_metadata.egress_port")), 2);
  EXPECT_EQ(Z3ValueStringToInt(egress.at("standard_metadata.egress_spec")), 2);
}

// TODO: Re-enable this test once the timeout issue is fixed.
TEST(P4SymbolicIntegrationTest,
     DISABLED_CanGenerateTestPacketsForSimpleSaiP4EntriesForPathCoverage) {
  // Some constants.
  auto env = thinkit::BazelTestEnvironment(/*mask_known_failures=*/false);
  const auto config = sai::GetNonstandardForwardingPipelineConfig(
      sai::Instantiation::kMiddleblock, sai::NonstandardPlatform::kP4Symbolic);
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(config.p4info()));
  EXPECT_OK(env.StoreTestArtifact("ir_p4info.txtpb", ir_p4info));
  EXPECT_OK(env.StoreTestArtifact("p4_config.json", config.p4_device_config()));

  // Prepare hard-coded table entries.
  auto pd_entries = ParseProtoOrDie<sai::TableEntries>(kTableEntries);
  EXPECT_OK(env.StoreTestArtifact("pd_entries.txtpb", pd_entries));
  ASSERT_OK_AND_ASSIGN(std::vector<p4::v1::Entity> pi_entities,
                       pdpi::PdTableEntriesToPiEntities(ir_p4info, pd_entries));

  // Symbolically evaluate program.
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
  LOG(INFO) << "building model and synthesizing packets (this may take a "
               "while) ...";
  absl::Time start_time = absl::Now();
  ASSERT_OK_AND_ASSIGN(
      packet_synthesizer::PacketSynthesisResults results,
      symbolic::
          EvaluateP4ProgramAndSynthesizePacketsCoveringAllControlFlowPaths(
              config, pi_entities, ports, translations));
  LOG(INFO) << "-> done in " << (absl::Now() - start_time) << " with "
            << results.results_size() << " packets synthesized.";

  // the current number if 5847 but checking for GT 5000 to make the test
  // less brittle in face of SAI-P4 changes.
  ASSERT_GT(results.results_size(), 5000);
}

TEST(P4SymbolicIntegrationTest,
     CanGenerateTestPacketsForSimpleSaiP4EntriesWithTunneling) {
  // Some constants.
  auto env = thinkit::BazelTestEnvironment(/*mask_known_failures=*/false);
  const auto config = sai::GetNonstandardForwardingPipelineConfig(
      sai::Instantiation::kFabricBorderRouter,
      sai::NonstandardPlatform::kP4Symbolic);
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(config.p4info()));
  EXPECT_OK(env.StoreTestArtifact("ir_p4info.txtpb", ir_p4info));
  EXPECT_OK(env.StoreTestArtifact("p4_config.json", config.p4_device_config()));

  // Prepare hard-coded table entries.
  auto pd_entries =
      ParseProtoOrDie<sai::TableEntries>(kTableEntriesWithTunneling);
  EXPECT_OK(env.StoreTestArtifact("pd_entries.txtpb", pd_entries));
  ASSERT_OK_AND_ASSIGN(std::vector<p4::v1::Entity> pi_entities,
                       pdpi::PdTableEntriesToPiEntities(ir_p4info, pd_entries));

  // Symbolically evaluate program.
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
  LOG(INFO) << "building model (this may take a while) ...";
  absl::Time start_time = absl::Now();
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<symbolic::SolverState> solver_state,
      symbolic::EvaluateP4Program(config, pi_entities, ports, translations));
  LOG(INFO) << "-> done in " << (absl::Now() - start_time);

  // Dump solver state.
  for (auto& [name, entries] : solver_state->context.table_entries) {
    std::string banner = absl::StrCat(
        "== ", name, " ", std::string(80 - name.size() - 4, '='), "\n");
    EXPECT_OK(env.AppendToTestArtifact("p4symbolic_ir_entries.txtpb", banner));
    for (auto& entry : entries) {
      EXPECT_OK(env.AppendToTestArtifact("p4symbolic_ir_entries.txtpb", entry));
    }
  }
  EXPECT_OK(env.StoreTestArtifact("program.txtpb", solver_state->program));

  // Define assertion to hit the tunnel_table_entry.
  symbolic::Assertion hit_tunnel_table_entry =
      [](const symbolic::SymbolicContext& ctx) -> z3::expr {
    CHECK(ctx.trace.matched_entries.contains(
        "ingress.routing_resolution.tunnel_table"));
    auto tunnel_table =
        ctx.trace.matched_entries.at("ingress.routing_resolution.tunnel_table");
    return tunnel_table.matched && tunnel_table.entry_index == 0 &&
           !ctx.trace.dropped;
  };
  EXPECT_OK(env.StoreTestArtifact(
      "hit_tunnel_table_entry.smt",
      symbolic::DebugSMT(solver_state, hit_tunnel_table_entry)));
  ASSERT_OK_AND_ASSIGN(absl::optional<symbolic::ConcreteContext> solution,
                       symbolic::Solve(*solver_state, hit_tunnel_table_entry));
  ASSERT_THAT(solution, Not(Eq(absl::nullopt)));
  EXPECT_OK(env.StoreTestArtifact("hit_tunnel_table_entry.solution.txt",
                                  solution->to_string(/*verbose=*/true)));

  // Check some properties of the solution.
  auto& egress = solution->egress_headers;
}

TEST(P4SymbolicIntegrationTest,
     CanGenerateTestPacketsForSimpleSaiP4EntriesWithMulticast) {
  // Some constants.
  auto env = thinkit::BazelTestEnvironment(/*mask_known_failures=*/false);
  const auto config = sai::GetNonstandardForwardingPipelineConfig(
      sai::Instantiation::kMiddleblock, sai::NonstandardPlatform::kP4Symbolic);
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(config.p4info()));
  EXPECT_OK(env.StoreTestArtifact("ir_p4info.txtpb", ir_p4info));
  EXPECT_OK(env.StoreTestArtifact("p4_config.json", config.p4_device_config()));

  // Prepare hard-coded table entries.
  // Install table entries.
  constexpr absl::string_view kVrf = "vrf";
  constexpr auto kIngressDstIp = netaddr::Ipv4Address(232, 1, 2, 3);
  constexpr auto kEgressSrcMac = netaddr::MacAddress(6, 5, 4, 3, 2, 1);
  constexpr int kMulticastGroupId = 42;
  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::Entity> pi_entities,
      sai::EntryBuilder()
          .AddVrfEntry(kVrf)
          .AddEntryAdmittingAllPacketsToL3()
	  .AddPreIngressAclTableEntry(kVrf)
          .AddMulticastRoute(kVrf, kIngressDstIp, kMulticastGroupId)
          .AddMulticastGroupEntry(
              kMulticastGroupId,
              {
                  sai::Replica{.egress_port = "1", .instance = 0},
                  sai::Replica{.egress_port = "1", .instance = 1},
                  sai::Replica{.egress_port = "2", .instance = 20},
              })
	  .AddMrifEntryRewritingSrcMac(
              /*egress_port=*/"1", /*replica_instance=*/0,
              /*src_mac=*/kEgressSrcMac)
          .AddMrifEntryRewritingSrcMac(
              /*egress_port=*/"1", /*replica_instance=*/1,
              /*src_mac=*/kEgressSrcMac)
          .AddMrifEntryRewritingSrcMac(
              /*egress_port=*/"2", /*replica_instance=*/20,
              /*src_mac=*/kEgressSrcMac)
          .LogPdEntries()
          .GetDedupedPiEntities(ir_p4info));

  // Symbolically evaluate program.
  std::vector<int> ports = {1, 2, 3, 4, 5};
  symbolic::TranslationPerType translations;
  translations[p4_symbolic::kPortIdTypeName] =
      symbolic::values::TranslationData{
          .static_mapping = {{"1", 1},
                             {"2", 2},
                             {"3", 3},
                             {"4", 4},
                             {"5", 5},
                             {"DROP", symbolic::kDropPort},
                             {"CPU", symbolic::kCpuPort}},
          .dynamic_translation = false,
      };
  translations[p4_symbolic::kVrfIdTypeName] = symbolic::values::TranslationData{
      .static_mapping = {{"", 0}},
      .dynamic_translation = true,
  };
  LOG(INFO) << "building model (this may take a while) ...";
  absl::Time start_time = absl::Now();
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<symbolic::SolverState> solver_state,
      symbolic::EvaluateP4Program(config, pi_entities, ports, translations));
  LOG(INFO) << "-> done in " << (absl::Now() - start_time);

  // Dump solver state.
  for (auto& [name, entries] : solver_state->context.table_entries) {
    std::string banner = absl::StrCat(
        "== ", name, " ", std::string(80 - name.size() - 4, '='), "\n");
    EXPECT_OK(env.AppendToTestArtifact("p4symbolic_ir_entries.txtpb", banner));
    for (auto& entry : entries) {
      EXPECT_OK(env.AppendToTestArtifact("p4symbolic_ir_entries.txtpb", entry));
    }
  }
  EXPECT_OK(env.StoreTestArtifact("program.txtpb", solver_state->program));

  // Define assertion to hit the ipv4_multicast_table.
  symbolic::Assertion hit_multicast_route =
      [](const symbolic::SymbolicContext& ctx) -> z3::expr {
    CHECK(ctx.trace.matched_entries.contains(
        "ingress.routing_lookup.ipv4_multicast_table"));
    auto tunnel_table = ctx.trace.matched_entries.at(
        "ingress.routing_lookup.ipv4_multicast_table");
    return tunnel_table.matched && !ctx.trace.dropped;
  };
  EXPECT_OK(env.StoreTestArtifact(
      "hit_multicast_route.smt",
      symbolic::DebugSMT(solver_state, hit_multicast_route)));
  ASSERT_OK_AND_ASSIGN(absl::optional<symbolic::ConcreteContext> solution,
                       symbolic::Solve(*solver_state, hit_multicast_route));
  ASSERT_THAT(solution, Not(Eq(absl::nullopt)));
  EXPECT_OK(env.StoreTestArtifact("hit_multicast_route.solution.txt",
                                  solution->to_string(/*verbose=*/true)));

  // Check some properties of the solution.
  auto& ingress = solution->ingress_headers;
  auto& egress = solution->egress_headers;
  EXPECT_EQ(Z3ValueStringToInt(ingress["ipv4.dst_addr"]),
            kIngressDstIp.ToBitset().to_ulong());
  EXPECT_EQ(Z3ValueStringToInt(egress["ethernet.src_addr"]),
            kEgressSrcMac.ToBitset().to_ulong());
  EXPECT_THAT(Z3ValueStringToInt(solution->egress_port), AnyOf(Eq(1), Eq(2)));

}

}  // namespace
}  // namespace p4_symbolic
