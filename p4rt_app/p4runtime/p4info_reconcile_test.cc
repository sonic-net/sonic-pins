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

#include "p4rt_app/p4runtime/p4info_reconcile.h"

#include <string>
#include <vector>

#include "absl/functional/any_invocable.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4rt_app/utils/ir_builder.h"

namespace p4rt_app {
namespace {
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::ExplainMatchResult;
using ::testing::UnorderedElementsAreArray;

std::string ToString(const P4InfoReconcileTransition& transition) {
  return absl::Substitute(
      R"({
  hashing_packet_field_configs_to_delete = {$0}
  hashing_packet_field_configs_to_set = {$1}
  upate_switch_table = $2
  acl_tables_to_delete = {$3}
  acl_tables_to_add = {$4}
  acl_tables_to_modify = {$5}
})",

      absl::StrJoin(transition.hashing_packet_field_configs_to_delete, ", "),
      absl::StrJoin(transition.hashing_packet_field_configs_to_set, ", "),
      (transition.update_switch_table ? "true" : "false"),
      absl::StrJoin(transition.acl_tables_to_delete, ", "),
      absl::StrJoin(transition.acl_tables_to_add, ", "),
      absl::StrJoin(transition.acl_tables_to_modify, ", "));
}

MATCHER_P(TransitionIsImpl, expected,
          absl::StrCat("matches ", ToString(expected))) {
  bool failed = false;
  *result_listener << "\n";
  if (!ExplainMatchResult(UnorderedElementsAreArray(
                              expected.hashing_packet_field_configs_to_delete),
                          arg.hashing_packet_field_configs_to_delete,
                          result_listener)) {
    *result_listener
        << (failed ? "and " : "where ")
        << "hashing_packet_field_configs_to_delete does not match\n";
    failed = true;
  }
  if (!ExplainMatchResult(UnorderedElementsAreArray(
                              expected.hashing_packet_field_configs_to_set),
                          arg.hashing_packet_field_configs_to_set,
                          result_listener)) {
    *result_listener << (failed ? "and " : "where ")
                     << "hashing_packet_field_configs_to_set does not match\n";
    failed = true;
  }

  if (arg.update_switch_table != expected.update_switch_table) {
    *result_listener << (failed ? "and " : "where ")
                     << "update_switch_table does not match\n";
    failed = true;
  }
  if (!ExplainMatchResult(
          UnorderedElementsAreArray(expected.acl_tables_to_delete),
          arg.acl_tables_to_delete, result_listener)) {
    *result_listener << (failed ? "and " : "where ")
                     << "acl_tables_to_delete does not match\n";
    failed = true;
  }
  if (!ExplainMatchResult(UnorderedElementsAreArray(expected.acl_tables_to_add),
                          arg.acl_tables_to_add, result_listener)) {
    *result_listener << (failed ? "and " : "where ")
                     << "acl_tables_to_add does not match\n";
    failed = true;
  }
  if (!ExplainMatchResult(
          UnorderedElementsAreArray(expected.acl_tables_to_modify),
          arg.acl_tables_to_modify, result_listener)) {
    *result_listener << (failed ? "and " : "where ")
                     << "acl_tables_to_modify does not match\n";
    failed = true;
  }
  *result_listener << "\nActual: " << ToString(arg);
  return !failed;
}

constexpr auto TransitionIs = TransitionIsImpl<P4InfoReconcileTransition>;

const pdpi::IrP4Info& GetIrP4Info() {
  static const auto* const kP4Info = new pdpi::IrP4Info(
      IrP4InfoBuilder()
          .table(IrTableDefinitionBuilder()
                     .name("fixed_table_a")
                     .match_field(R"pb(id: 1 name: "match_field_a")pb",
                                  pdpi::Format::STRING)
                     .match_field(R"pb(id: 2 name: "match_field_b")pb",
                                  pdpi::Format::STRING)
                     .const_default_action(
                         IrActionDefinitionBuilder().name("NoAction"))
                     .size(100))
          .table(IrTableDefinitionBuilder()
                     .name("fixed_table_b")
                     .match_field(R"pb(id: 1 name: "match_field_a")pb",
                                  pdpi::Format::STRING)
                     .match_field(R"pb(id: 2 name: "match_field_b")pb",
                                  pdpi::Format::STRING)
                     .match_field(R"pb(id: 2 name: "match_field_c")pb",
                                  pdpi::Format::STRING)
                     .const_default_action(
                         IrActionDefinitionBuilder().name("NoAction"))
                     .size(200))
          .table(
              IrTableDefinitionBuilder()
                  .preamble(R"pb(alias: "acl_ingress_table_a"
                                 annotations: "@sai_acl(INGRESS)")pb")
                  .match_field(
                      R"pb(id: 1
                           name: "ttl"
                           annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_TTL)"
                           bitwidth: 8
                           match_type: TERNARY)pb",
                      pdpi::Format::HEX_STRING)
                  .match_field(
                      R"pb(id: 2
                           name: "ip_protocol"
                           annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_IP_PROTOCOL)"
                           bitwidth: 8
                           match_type: TERNARY)pb",
                      pdpi::Format::HEX_STRING)
                  .match_field(
                      R"pb(id: 3
                           name: "icmp_type"
                           annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_ICMP_TYPE)"
                           bitwidth: 8
                           match_type: TERNARY)pb",
                      pdpi::Format::HEX_STRING)
                  .entry_action(IrActionDefinitionBuilder().preamble(
                      R"pb(alias: "acl_drop"
                           annotations: "@sai_action(SAI_PACKET_ACTION_DROP)")pb"))
                  .const_default_action(
                      IrActionDefinitionBuilder().name("NoAction"))
                  .meter_unit(p4::config::v1::MeterSpec::BYTES)
                  .counter_unit(p4::config::v1::CounterSpec::BOTH)
                  .size(128))
          .table(
              IrTableDefinitionBuilder()
                  .preamble(R"pb(alias: "acl_ingress_table_b"
                                 annotations: "@sai_acl(INGRESS)")pb")
                  .match_field(
                      R"pb(id: 1
                           name: "l4_dst_port"
                           annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_L4_DST_PORT)"
                           bitwidth: 16
                           match_type: TERNARY)pb",
                      pdpi::Format::HEX_STRING)
                  .match_field(
                      R"pb(id: 2
                           name: "ip_protocol"
                           annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_IP_PROTOCOL)"
                           bitwidth: 8
                           match_type: TERNARY)pb",
                      pdpi::Format::HEX_STRING)
                  .match_field(
                      R"pb(id: 3
                           name: "icmp_type"
                           annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_ICMP_TYPE)"
                           bitwidth: 8
                           match_type: TERNARY)pb",
                      pdpi::Format::HEX_STRING)
                  .entry_action(IrActionDefinitionBuilder().preamble(
                      R"pb(alias: "acl_drop"
                           annotations: "@sai_action(SAI_PACKET_ACTION_DROP)")pb"))
                  .const_default_action(
                      IrActionDefinitionBuilder().name("NoAction"))
                  .meter_unit(p4::config::v1::MeterSpec::BYTES)
                  .counter_unit(p4::config::v1::CounterSpec::BOTH)
                  .size(256))
          .table(
              IrTableDefinitionBuilder()
                  .preamble(R"pb(alias: "acl_ingress_table_c"
                                 annotations: "@sai_acl(INGRESS)")pb")
                  .match_field(
                      R"pb(id: 1
                           name: "l4_dst_port"
                           annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_L4_DST_PORT)"
                           bitwidth: 16
                           match_type: TERNARY)pb",
                      pdpi::Format::HEX_STRING)
                  .match_field(
                      R"pb(id: 2
                           name: "ip_protocol"
                           annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_IP_PROTOCOL)"
                           bitwidth: 8
                           match_type: TERNARY)pb",
                      pdpi::Format::HEX_STRING)
                  .entry_action(IrActionDefinitionBuilder().preamble(
                      R"pb(alias: "acl_drop"
                           annotations: "@sai_action(SAI_PACKET_ACTION_DROP)")pb"))
                  .const_default_action(
                      IrActionDefinitionBuilder().name("NoAction"))
                  .meter_unit(p4::config::v1::MeterSpec::BYTES)
                  .counter_unit(p4::config::v1::CounterSpec::BOTH)
                  .size(128))
          .table(
              IrTableDefinitionBuilder()
                  .preamble(R"pb(alias: "acl_ingress_table_d"
                                 annotations: "@sai_acl(INGRESS)")pb")
                  .match_field(
                      R"pb(id: 1
                           name: "is_ip"
                           annotations: "@sai_field(SAI_ACL_TABLE_ATTR_FIELD_ACL_IP_TYPE / IP)"
                           bitwidth: 1
                           match_type: OPTIONAL)pb",
                      pdpi::Format::HEX_STRING)
                  .entry_action(IrActionDefinitionBuilder().preamble(
                      R"pb(alias: "acl_drop"
                           annotations: "@sai_action(SAI_PACKET_ACTION_DROP)")pb"))
                  .const_default_action(
                      IrActionDefinitionBuilder().name("NoAction"))
                  .meter_unit(p4::config::v1::MeterSpec::BYTES)
                  .counter_unit(p4::config::v1::CounterSpec::BOTH)
                  .size(128))
          .action(IrActionDefinitionBuilder().preamble(
              R"pb(id: 100
                   name: "ingress.hashing.select_ecmp_hash_algorithm"
                   alias: "select_ecmp_hash_algorithm"
                   annotations: "@sai_hash_algorithm(SAI_HASH_ALGORITHM_CRC)"
                   annotations: "@sai_hash_seed(1)"
                   annotations: "@sai_hash_offset(2)")pb"))
          .action(IrActionDefinitionBuilder().preamble(
              R"pb(id: 101
                   name: "ingress.hashing.select_lag_hash_algorithm"
                   alias: "select_lag_hash_algorithm"
                   annotations: "@sai_hash_algorithm(SAI_HASH_ALGORITHM_CRC_32LO)"
                   annotations: "@sai_hash_seed(10)"
                   annotations: "@sai_hash_offset(20)")pb"))
          .action(IrActionDefinitionBuilder().preamble(
              R"pb(id: 102
                   name: "ingress.hashing.compute_ecmp_hash_ipv4"
                   alias: "compute_ecmp_hash_ipv4"
                   annotations: "@sai_ecmp_hash(SAI_SWITCH_ATTR_ECMP_HASH_IPV4)"
                   annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_SRC_IPV4)"
                   annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_DST_IPV4)")pb"))
          .action(IrActionDefinitionBuilder().preamble(
              R"pb(id: 103
                   name: "ingress.hashing.compute_lag_hash_ipv4"
                   alias: "compute_lag_hash_ipv4"
                   annotations: "@sai_lag_hash(SAI_SWITCH_ATTR_LAG_HASH_IPV4)"
                   annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_SRC_PORT)"
                   annotations: "@sai_native_hash_field(SAI_NATIVE_HASH_FIELD_L4_DST_PORT)"
              )pb"))());
  return *kP4Info;
}

TEST(CalculateTransition, NoTransitionForSameIrP4Info) {
  ASSERT_OK_AND_ASSIGN(auto transition,
                       CalculateTransition(GetIrP4Info(), GetIrP4Info()));
  EXPECT_THAT(transition, TransitionIs({}));
}

TEST(CalculateTransition, CalculatesHashingPacketFieldModification) {
  const pdpi::IrP4Info original = GetIrP4Info();
  auto with_hash_diff = original;
  *with_hash_diff.mutable_actions_by_name()
       ->at("compute_lag_hash_ipv4")
       .mutable_preamble()
       ->mutable_annotations(2) =
      "sai_native_hash_field(SAI_NATIVE_HASH_FIELD_SRC_IPV4)";

  EXPECT_THAT(
      CalculateTransition(original, with_hash_diff),
      IsOkAndHolds(TransitionIs({
          .hashing_packet_field_configs_to_set = {"compute_lag_hash_ipv4"},
          .update_switch_table = true,
      })));

  EXPECT_THAT(
      CalculateTransition(with_hash_diff, original),
      IsOkAndHolds(TransitionIs({
          .hashing_packet_field_configs_to_set = {"compute_lag_hash_ipv4"},
          .update_switch_table = true,
      })));
}

TEST(CalculateTransition, CalculatesHashingPacketFieldDeletion) {
  const pdpi::IrP4Info original = GetIrP4Info();
  auto with_hash_diff = original;
  int id = with_hash_diff.actions_by_name()
               .at("compute_lag_hash_ipv4")
               .preamble()
               .id();
  with_hash_diff.mutable_actions_by_name()->erase("compute_lag_hash_ipv4");
  with_hash_diff.mutable_actions_by_id()->erase(id);

  ASSERT_OK_AND_ASSIGN(auto transition,
                       CalculateTransition(original, with_hash_diff));
  EXPECT_THAT(
      transition,
      TransitionIs({
          .hashing_packet_field_configs_to_delete = {"compute_lag_hash_ipv4"},
          .update_switch_table = true,
      }));
}

TEST(CalculateTransition, CalculatesHashingPacketFieldAddition) {
  const pdpi::IrP4Info original = GetIrP4Info();
  auto with_hash_diff = original;
  int id = with_hash_diff.actions_by_name()
               .at("compute_lag_hash_ipv4")
               .preamble()
               .id();
  with_hash_diff.mutable_actions_by_name()->erase("compute_lag_hash_ipv4");
  with_hash_diff.mutable_actions_by_id()->erase(id);

  ASSERT_OK_AND_ASSIGN(auto transition,
                       CalculateTransition(with_hash_diff, original));
  EXPECT_THAT(
      transition,
      TransitionIs({
          .hashing_packet_field_configs_to_set = {"compute_lag_hash_ipv4"},
          .update_switch_table = true,
      }));
}

// Erases tables that match the predicate from the IrP4Info. Returns the names
// of the removed tables.
std::vector<std::string> EraseTables(
    pdpi::IrP4Info& ir_p4info,
    absl::AnyInvocable<bool(const pdpi::IrTableDefinition&)> predicate) {
  std::vector<std::string> erased_tables;

  auto& tables_by_id = *ir_p4info.mutable_tables_by_id();
  auto& tables_by_name = *ir_p4info.mutable_tables_by_name();
  for (auto iter = tables_by_id.begin(); iter != tables_by_id.end();) {
    if (predicate(iter->second)) {
      iter = tables_by_id.erase(iter);
    } else {
      ++iter;
    }
  }
  for (auto iter = tables_by_name.begin(); iter != tables_by_name.end();) {
    if (predicate(iter->second)) {
      erased_tables.push_back(iter->first);
      iter = tables_by_name.erase(iter);
    } else {
      ++iter;
    }
  }
  return erased_tables;
}

bool EraseTable(pdpi::IrP4Info& ir_p4info, absl::string_view table_name) {
  return !EraseTables(ir_p4info, [table_name](
                                     const pdpi::IrTableDefinition& table) {
            return table.preamble().alias() == table_name;
          }).empty();
}

TEST(CalculateTransition, IgnoresFixedTableDeletion) {
  const pdpi::IrP4Info original = GetIrP4Info();
  pdpi::IrP4Info without_fixed_tables = original;
  ASSERT_TRUE(EraseTable(without_fixed_tables, "fixed_table_a"));
  ASSERT_TRUE(EraseTable(without_fixed_tables, "fixed_table_b"));
  EXPECT_THAT(CalculateTransition(original, without_fixed_tables),
              IsOkAndHolds(TransitionIs({})));
}

TEST(CalculateTransition, IgnoresFixedTableAddition) {
  const pdpi::IrP4Info original = GetIrP4Info();
  pdpi::IrP4Info without_fixed_tables = original;
  ASSERT_TRUE(EraseTable(without_fixed_tables, "fixed_table_a"));
  ASSERT_TRUE(EraseTable(without_fixed_tables, "fixed_table_b"));
  EXPECT_THAT(CalculateTransition(without_fixed_tables, original),
              IsOkAndHolds(TransitionIs({})));
}

TEST(CalculateTransition, IgnoresFixedTableModification) {
  const pdpi::IrP4Info original = GetIrP4Info();
  pdpi::IrP4Info with_modified_fixed_tables = original;
  auto action = IrActionDefinitionBuilder().name("new_action")();
  *with_modified_fixed_tables.mutable_tables_by_name()
       ->at("fixed_table_a")
       .add_entry_actions()
       ->mutable_action() = action;
  *with_modified_fixed_tables.mutable_tables_by_id()
       ->at(with_modified_fixed_tables.tables_by_name()
                .at("fixed_table_a")
                .preamble()
                .id())
       .add_entry_actions()
       ->mutable_action() = action;

  EXPECT_THAT(CalculateTransition(with_modified_fixed_tables, original),
              IsOkAndHolds(TransitionIs({})));
}

TEST(CalculateTransition, CalculatesComplexTransition) {
  pdpi::IrP4Info original = GetIrP4Info();
  auto modified = original;

  // Erase some tables from the original IrP4Info. These will appear to be added
  // in the modified P4Info.
  ASSERT_TRUE(EraseTable(original, "acl_ingress_table_d"));
  ASSERT_TRUE(EraseTable(original, "fixed_table_a"));

  // Modify modified table.
  ASSERT_TRUE(EraseTable(modified, "acl_ingress_table_a"));
  ASSERT_TRUE(EraseTable(modified, "fixed_table_b"));
  modified.mutable_tables_by_name()
      ->at("acl_ingress_table_b")
      .mutable_entry_actions(0)
      ->mutable_action()
      ->mutable_preamble()
      ->set_alias("I am a different action");
  modified.mutable_tables_by_id()
      ->at(modified.tables_by_name().at("acl_ingress_table_b").preamble().id())
      .mutable_entry_actions(0)
      ->mutable_action()
      ->mutable_preamble()
      ->set_alias("I am a different action");
  modified.mutable_actions_by_id()->erase(
      modified.actions_by_name().at("compute_lag_hash_ipv4").preamble().id());
  modified.mutable_actions_by_name()->erase("compute_lag_hash_ipv4");

  EXPECT_THAT(
      CalculateTransition(original, modified),
      IsOkAndHolds(TransitionIs({
          .hashing_packet_field_configs_to_delete = {"compute_lag_hash_ipv4"},
          .update_switch_table = true,
          // .acl_tables_to_delete = {"acl_ingress_table_a"},
          // .acl_tables_to_add = {"acl_ingress_table_d"},
          // .acl_tables_to_modify = {"acl_ingress_table_b"},
      })));

  EXPECT_THAT(
      CalculateTransition(modified, original),
      IsOkAndHolds(TransitionIs({
          .hashing_packet_field_configs_to_set = {"compute_lag_hash_ipv4"},
          .update_switch_table = true,
          // .acl_tables_to_delete = {"acl_ingress_table_d"},
          // .acl_tables_to_add = {"acl_ingress_table_a"},
          // .acl_tables_to_modify = {"acl_ingress_table_b"},
      })));
}

TEST(CalculateTransition, ReturnsErrorForBadHashSetting) {
  const pdpi::IrP4Info original = GetIrP4Info();
  pdpi::IrP4Info modified = original;
  auto& action =
      modified.mutable_actions_by_name()->at("select_ecmp_hash_algorithm");
  action.mutable_preamble()->clear_annotations();
  action.mutable_preamble()->add_annotations("@sai_hash_algorithm(FakeAlg)");
  modified.mutable_actions_by_id()->at(action.preamble().id()) = action;

  EXPECT_THAT(CalculateTransition(original, modified),
              StatusIs(absl::StatusCode::kInvalidArgument));
  EXPECT_THAT(CalculateTransition(modified, original),
              StatusIs(absl::StatusCode::kInternal));
}

}  // namespace
}  // namespace p4rt_app
