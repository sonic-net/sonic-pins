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
// =============================================================================
// Integration test between SAI-P4 and the P4-Fuzzer library.

#include <vector>

#include "absl/log/log.h"
#include "absl/random/random.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_constraints/backend/interpreter.h"
#include "p4_fuzzer/constraints.h"
#include "p4_fuzzer/fuzz_util.h"
#include "p4_fuzzer/fuzzer_config.h"
#include "p4_fuzzer/switch_state.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"

namespace p4_fuzzer {
namespace {

using ::gutil::IsOkAndHolds;

// Adds entries that can be referred to by ACLs.
absl::Status AddReferenceableEntries(const FuzzerConfig& config,
                                     const pins_test::P4rtPortId& egress_port,
                                     SwitchState& switch_state,
                                     absl::BitGen& gen) {
  ASSIGN_OR_RETURN(std::vector<p4::v1::Entity> referable_entities,
                   sai::EntryBuilder()
                       .AddEntriesForwardingIpPacketsToGivenPort(
                           egress_port.GetP4rtEncoding())
                       .GetDedupedPiEntities(config.GetIrP4Info()));

  if (config.GetIrP4Info().tables_by_name().contains("mirror_session_table")) {
    pdpi::IrTableDefinition mirror_session_table =
        config.GetIrP4Info().tables_by_name().at("mirror_session_table");
    p4::v1::Entity mirror_session_entity;
    ASSIGN_OR_RETURN(
        *mirror_session_entity.mutable_table_entry(),
        FuzzValidTableEntry(&gen, config, switch_state, mirror_session_table));
    referable_entities.push_back(mirror_session_entity);
  }

  ASSIGN_OR_RETURN(pdpi::IrTableDefinition multicast_router_interface_table,
                   gutil::FindOrStatus(config.GetIrP4Info().tables_by_name(),
                                       "multicast_router_interface_table"));
  p4::v1::Update mrif_update;
  mrif_update.set_type(p4::v1::Update::INSERT);
  ASSIGN_OR_RETURN(*mrif_update.mutable_entity()->mutable_table_entry(),
                   FuzzValidTableEntry(&gen, config, switch_state,
                                       multicast_router_interface_table));
  RETURN_IF_ERROR(switch_state.ApplyUpdate(mrif_update));

  p4::v1::Entity multicast_group_entity;
  ASSIGN_OR_RETURN(
      *multicast_group_entity.mutable_packet_replication_engine_entry()
           ->mutable_multicast_group_entry(),
      FuzzValidMulticastGroupEntry(&gen, config, switch_state));
  referable_entities.push_back(multicast_group_entity);

  for (const p4::v1::Entity& entity : referable_entities) {
    p4::v1::Update update;
    *update.mutable_entity() = entity;
    update.set_type(p4::v1::Update::INSERT);
    RETURN_IF_ERROR(switch_state.ApplyUpdate(update));
  }
  return absl::OkStatus();
}

using SaiP4AndP4FuzzerIntegrationTest =
    testing::TestWithParam<sai::Instantiation>;

// Tests whether the fuzzer can generate valid entries for tables with
// p4-constraints.
TEST_P(SaiP4AndP4FuzzerIntegrationTest,
       FuzzValidEntryGeneratesValidEntryForTablesWithP4Constraints) {
  auto sai_instantiation = sai::Instantiation::kFabricBorderRouter;
  p4::config::v1::P4Info p4_info = sai::GetP4Info(sai_instantiation);
  auto port = pins_test::P4rtPortId::MakeFromOpenConfigEncoding(1);
  absl::BitGen gen;

  ASSERT_OK_AND_ASSIGN(
      FuzzerConfig config,
      FuzzerConfig::Create(
          p4_info, ConfigParams{
                       .ports = {port},
                       .qos_queues = {"0x1"},
                       .role = "sdn_controller",
                       .mutate_update_probability = 0,
                       // TODO: Remove once p4 constraints
                       // supports P4Runtime-translated types.
                       .ignore_constraints_on_tables =
                           {
                               "ingress.routing_lookup.vrf_table",
                               "ingress.ingress_cloning.ingress_clone_table",
                           },
                   }));
  SwitchState state(config.GetIrP4Info());

  // To ensure valid entries for tables with references even exist.
  ASSERT_OK(AddReferenceableEntries(config, port, state, gen));

  // Remove unsupported tables.
  pdpi::IrP4Info ir_p4info_without_unsupported = config.GetIrP4Info();
  pdpi::RemoveUnsupportedEntities(ir_p4info_without_unsupported);

  for (const auto& [table_name, test_table] :
       ir_p4info_without_unsupported.tables_by_name()) {
    if (!UsesP4Constraints(test_table, config)) continue;
    SCOPED_TRACE(absl::StrCat("when testing ", table_name));

    for (int i = 0; i < 10; ++i) {
      ASSERT_OK_AND_ASSIGN(
          p4::v1::TableEntry entry,
          FuzzValidTableEntry(&gen, config, state, test_table));
      ASSERT_OK_AND_ASSIGN(pdpi::IrTableEntry ir_entry,
                           pdpi::PiTableEntryToIr(config.GetIrP4Info(), entry));
      EXPECT_THAT(p4_constraints::ReasonEntryViolatesConstraint(
                      entry, config.GetConstraintInfo()),
                  IsOkAndHolds(""))
          << "in table " << table_name << " for entry:\n"
          << ir_entry.DebugString();
    }
  }
}

INSTANTIATE_TEST_SUITE_P(
    FuzzerWorksWithSaiInstantiation, SaiP4AndP4FuzzerIntegrationTest,
    testing::ValuesIn(sai::AllSaiInstantiations()),
    [](const testing::TestParamInfo<sai::Instantiation>& info) {
      return gutil::SnakeCaseToCamelCase(
          sai::InstantiationToString(info.param));
    });

}  // namespace
}  // namespace p4_fuzzer
