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

#include "p4_symbolic/symbolic/table_entry.h"

#include <cstddef>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "google/protobuf/util/message_differencer.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_symbolic/ir/ir.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/ir/parser.h"
#include "p4_symbolic/ir/table_entries.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "p4_symbolic/test_util.h"
#include "z3++.h"

namespace p4_symbolic::symbolic {
namespace {

using MatchType = p4::config::v1::MatchField::MatchType;
using gutil::StatusIs;

// P4 source: p4_symbolic/testdata/ipv4-routing/basic.p4
// Table "MyIngress.ipv4_lpm" has exactly one LPM match.
class IPv4RoutingTableEntriesTest : public testing::Test {
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
    state_ = std::make_unique<SolverState>(dataplane.program);
    ir_entries_ = std::move(dataplane.entries);
  }

  absl::StatusOr<ir::Table> GetTable() const {
    // The P4 program should have exactly one table.
    if (state_->program.tables_size() != 1) {
      return gutil::InternalErrorBuilder()
             << "The program must have exactly 1 table. Found "
             << state_->program.tables_size() << " tables.";
    }

    return state_->program.tables().begin()->second;
  }

 protected:
  std::unique_ptr<SolverState> state_;
  ir::TableEntries ir_entries_;
};

TEST_F(IPv4RoutingTableEntriesTest, SymbolicEntryWithGetterFunctions) {
  constexpr int entry_index = 0;
  constexpr int priority = 0;
  constexpr int prefix_length = 16;

  // Construct a symbolic table entry.
  ASSERT_OK_AND_ASSIGN(ir::Table table, GetTable());
  ASSERT_OK_AND_ASSIGN(
      ir::TableEntry ir_entry,
      CreateSymbolicIrTableEntry(table, priority, prefix_length));
  TableEntry entry(entry_index, std::move(ir_entry));

  // Test all basic getter functions.
  EXPECT_EQ(entry.GetIndex(), entry_index);
  EXPECT_FALSE(entry.IsConcrete());
  EXPECT_TRUE(entry.IsSymbolic());
  EXPECT_EQ(entry.GetTableName(), "MyIngress.ipv4_lpm");
  EXPECT_TRUE(google::protobuf::util::MessageDifferencer::Equals(
      entry.GetP4SymbolicIrTableEntry().symbolic_entry().sketch(),
      entry.GetPdpiIrTableEntry()));
  EXPECT_EQ(entry.GetPdpiIrTableEntry().matches_size(), 1);
  EXPECT_TRUE(entry.GetPdpiIrTableEntry().matches(0).has_lpm());
  EXPECT_EQ(entry.GetPdpiIrTableEntry().matches(0).lpm().prefix_length(),
            prefix_length);
}

TEST_F(IPv4RoutingTableEntriesTest, MatchVariablesOfSymbolicEntry) {
  constexpr int entry_index = 0;
  constexpr int priority = 0;
  constexpr int prefix_length = 16;

  // Construct a symbolic table entry.
  ASSERT_OK_AND_ASSIGN(ir::Table table, GetTable());
  ASSERT_OK_AND_ASSIGN(
      ir::TableEntry ir_entry,
      CreateSymbolicIrTableEntry(table, priority, prefix_length));
  TableEntry entry(entry_index, std::move(ir_entry));

  // Test the symbolic variables of the symbolic LPM match.
  const std::string &match_name = entry.GetPdpiIrTableEntry().matches(0).name();
  int bitwidth = table.table_definition()
                     .match_fields_by_name()
                     .begin()
                     ->second.match_field()
                     .bitwidth();
  constexpr absl::string_view variable_prefix =
      "MyIngress.ipv4_lpm_entry_0_hdr.ipv4.dstAddr_lpm_";
  ASSERT_OK_AND_ASSIGN(SymbolicMatchVariables match_variables,
                       entry.GetMatchValues(match_name, table, state_->program,
                                            *state_->context.z3_context));
  EXPECT_EQ(match_variables.match_type, MatchType::MatchField_MatchType_LPM);
  z3::expr expected_value_expr = state_->context.z3_context->bv_const(
      absl::StrCat(variable_prefix, "value").c_str(), bitwidth);
  z3::expr expected_mask_expr = state_->context.z3_context->bv_const(
      absl::StrCat(variable_prefix, "mask").c_str(), bitwidth);
  EXPECT_TRUE(z3::eq(match_variables.value, expected_value_expr));
  EXPECT_TRUE(z3::eq(match_variables.mask, expected_mask_expr));
}

TEST_F(IPv4RoutingTableEntriesTest, ActionInvocationVariablesOfSymbolicEntry) {
  constexpr int entry_index = 0;
  constexpr int priority = 0;
  constexpr int prefix_length = 16;

  // Construct a symbolic table entry.
  ASSERT_OK_AND_ASSIGN(ir::Table table, GetTable());
  ASSERT_OK_AND_ASSIGN(
      ir::TableEntry ir_entry,
      CreateSymbolicIrTableEntry(table, priority, prefix_length));
  TableEntry entry(entry_index, std::move(ir_entry));

  // Test the symbolic variables of the symbolic action invocations.
  for (const auto &action_ref : table.table_definition().entry_actions()) {
    const std::string &action_name = action_ref.action().preamble().name();
    ASSERT_OK_AND_ASSIGN(z3::expr action_invocation,
                         entry.GetActionInvocation(
                             action_name, table, *state_->context.z3_context));
    z3::expr expected_action_invocation =
        state_->context.z3_context->bool_const(
            absl::StrCat("MyIngress.ipv4_lpm_entry_0_", action_name,
                         "_$chosen$")
                .c_str());
    EXPECT_TRUE(z3::eq(action_invocation, expected_action_invocation));
  }
}

TEST_F(IPv4RoutingTableEntriesTest, ActionParameterVariablesOfSymbolicEntry) {
  constexpr int entry_index = 0;
  constexpr int priority = 0;
  constexpr int prefix_length = 16;

  // Construct a symbolic table entry.
  ASSERT_OK_AND_ASSIGN(ir::Table table, GetTable());
  ASSERT_OK_AND_ASSIGN(
      ir::TableEntry ir_entry,
      CreateSymbolicIrTableEntry(table, priority, prefix_length));
  TableEntry entry(entry_index, std::move(ir_entry));

  // Test the symbolic variables of the symbolic action parameters.
  for (const auto &action_ref : table.table_definition().entry_actions()) {
    const std::string &action_name = action_ref.action().preamble().name();
    ASSERT_TRUE(state_->program.actions().contains(action_name));
    const ir::Action &action = state_->program.actions().at(action_name);

    for (const auto &[param_name, param_definition] :
         action_ref.action().params_by_name()) {
      ASSERT_OK_AND_ASSIGN(z3::expr param, entry.GetActionParameter(
                                               param_name, action, table,
                                               *state_->context.z3_context));
      z3::expr expected_param = state_->context.z3_context->bv_const(
          absl::StrCat("MyIngress.ipv4_lpm_entry_0_", action_name, "_",
                       param_name)
              .c_str(),
          param_definition.param().bitwidth());
      EXPECT_TRUE(z3::eq(param, expected_param));
    }
  }
}

TEST_F(IPv4RoutingTableEntriesTest, ErrorWithNonExistentMatch) {
  constexpr int entry_index = 0;
  constexpr int priority = 0;
  constexpr int prefix_length = 16;

  // Construct a symbolic table entry.
  ASSERT_OK_AND_ASSIGN(ir::Table table, GetTable());
  ASSERT_OK_AND_ASSIGN(
      ir::TableEntry ir_entry,
      CreateSymbolicIrTableEntry(table, priority, prefix_length));
  TableEntry entry(entry_index, std::move(ir_entry));

  // Test getting the symbolic variables of a non-existent match.
  constexpr absl::string_view non_existent_match_name = "non_existent_match";
  EXPECT_THAT(
      entry.GetMatchValues(non_existent_match_name, table, state_->program,
                           *state_->context.z3_context),
      StatusIs(absl::StatusCode::kNotFound,
               "Match 'non_existent_match' not found in table "
               "'MyIngress.ipv4_lpm'"));
}

TEST_F(IPv4RoutingTableEntriesTest, ErrorWithWildcardMatch) {
  constexpr int entry_index = 0;
  constexpr int priority = 0;
  constexpr int prefix_length = 16;

  // Construct a symbolic table entry with all wildcard matches.
  ASSERT_OK_AND_ASSIGN(ir::Table table, GetTable());
  ASSERT_OK_AND_ASSIGN(
      ir::TableEntry ir_entry,
      CreateSymbolicIrTableEntry(table, priority, prefix_length));
  TableEntry non_wildcard_entry(entry_index, ir_entry);
  ir_entry.mutable_symbolic_entry()->mutable_sketch()->clear_matches();
  TableEntry entry(entry_index, ir_entry);

  // Test getting the symbolic variables of an all-wildcard symbolic entry.
  constexpr absl::string_view match_name = "hdr.ipv4.dstAddr";
  EXPECT_THAT(
      entry.GetMatchValues(match_name, table, state_->program,
                           *state_->context.z3_context),
      StatusIs(absl::StatusCode::kInvalidArgument,
               testing::StartsWith(absl::StrCat(
                   "Match '", match_name, "' is an explicit wildcard."))));
}

TEST_F(IPv4RoutingTableEntriesTest, ErrorWithNonExistentAction) {
  constexpr int entry_index = 0;
  constexpr int priority = 0;
  constexpr int prefix_length = 16;

  // Construct a symbolic table entry.
  ASSERT_OK_AND_ASSIGN(ir::Table table, GetTable());
  ASSERT_OK_AND_ASSIGN(
      ir::TableEntry ir_entry,
      CreateSymbolicIrTableEntry(table, priority, prefix_length));
  TableEntry entry(entry_index, std::move(ir_entry));

  // Test getting the symbolic variables of a non-existent action.
  constexpr absl::string_view non_existent_action_name = "non_existent_action";
  EXPECT_THAT(entry.GetActionInvocation(non_existent_action_name, table,
                                        *state_->context.z3_context),
              StatusIs(absl::StatusCode::kNotFound,
                       "Action 'non_existent_action' not found in table "
                       "'MyIngress.ipv4_lpm'"));

  constexpr absl::string_view param_name = "dstAddr";
  const std::string &valid_action_name = table.table_definition()
                                             .entry_actions()
                                             .begin()
                                             ->action()
                                             .preamble()
                                             .name();
  ASSERT_TRUE(state_->program.actions().contains(valid_action_name));
  const ir::Action &valid_action =
      state_->program.actions().at(valid_action_name);
  ir::Action non_existent_action = valid_action;
  non_existent_action.mutable_action_definition()->mutable_preamble()->set_name(
      non_existent_action_name);
  EXPECT_THAT(entry.GetActionParameter(param_name, non_existent_action, table,
                                       *state_->context.z3_context),
              StatusIs(absl::StatusCode::kNotFound,
                       "Action 'non_existent_action' not found in table "
                       "'MyIngress.ipv4_lpm'"));
}

TEST_F(IPv4RoutingTableEntriesTest, ErrorWithNonExistentActionParameter) {
  constexpr int entry_index = 0;
  constexpr int priority = 0;
  constexpr int prefix_length = 16;

  // Construct a symbolic table entry.
  ASSERT_OK_AND_ASSIGN(ir::Table table, GetTable());
  ASSERT_OK_AND_ASSIGN(
      ir::TableEntry ir_entry,
      CreateSymbolicIrTableEntry(table, priority, prefix_length));
  TableEntry entry(entry_index, std::move(ir_entry));

  // Test getting the symbolic variables of a non-existent action parameter.
  constexpr absl::string_view non_existent_param_name = "non_existent_param";
  for (const auto &action_ref : table.table_definition().entry_actions()) {
    const std::string &action_name = action_ref.action().preamble().name();
    ASSERT_TRUE(state_->program.actions().contains(action_name));
    const ir::Action &action = state_->program.actions().at(action_name);
    EXPECT_THAT(
        entry.GetActionParameter(non_existent_param_name, action, table,
                                 *state_->context.z3_context),
        StatusIs(absl::StatusCode::kNotFound,
                 absl::StrCat("Action parameter 'non_existent_param' not found "
                              "in implementation of action '",
                              action_name, "'")));
  }
}

TEST_F(IPv4RoutingTableEntriesTest, ConcreteEntriesWithGetterFunctions) {
  for (const auto &[table_name, per_table_ir_entries] : ir_entries_) {
    for (size_t index = 0; index < per_table_ir_entries.size(); ++index) {
      // For each concrete IR entry, create a table entry object.
      const ir::TableEntry &ir_entry = per_table_ir_entries[index];
      TableEntry entry(index, ir_entry);

      // Test all basic getter functions.
      EXPECT_EQ(entry.GetIndex(), index);
      EXPECT_TRUE(entry.IsConcrete());
      EXPECT_FALSE(entry.IsSymbolic());
      EXPECT_EQ(entry.GetTableName(), table_name);
      EXPECT_EQ(entry.GetTableName(), "MyIngress.ipv4_lpm");
      EXPECT_TRUE(google::protobuf::util::MessageDifferencer::Equals(
          entry.GetP4SymbolicIrTableEntry().concrete_entry(),
          entry.GetPdpiIrTableEntry()));
      EXPECT_TRUE(google::protobuf::util::MessageDifferencer::Equals(
          entry.GetP4SymbolicIrTableEntry(), ir_entry));
      EXPECT_EQ(entry.GetPdpiIrTableEntry().matches_size(), 1);
      EXPECT_TRUE(entry.GetPdpiIrTableEntry().matches(0).has_lpm());
    }
  }
}

TEST_F(IPv4RoutingTableEntriesTest,
       ErrorGettingSymbolicVariablesWithConcreteEntries) {
  for (const auto &[table_name, per_table_ir_entries] : ir_entries_) {
    for (size_t index = 0; index < per_table_ir_entries.size(); ++index) {
      // For each concrete IR entry, create a table entry object.
      const ir::TableEntry &ir_entry = per_table_ir_entries[index];
      TableEntry entry(index, ir_entry);

      // Test getting the symbolic variables of a concrete entry.
      ASSERT_EQ(state_->program.tables_size(), 1);
      const ir::Table &table = state_->program.tables().begin()->second;
      ASSERT_EQ(entry.GetPdpiIrTableEntry().matches_size(), 1);
      const std::string &match_name =
          entry.GetPdpiIrTableEntry().matches(0).name();
      ASSERT_TRUE(entry.GetPdpiIrTableEntry().has_action());
      const std::string &action_name =
          entry.GetPdpiIrTableEntry().action().name();
      ASSERT_TRUE(state_->program.actions().contains(action_name));
      const ir::Action &action = state_->program.actions().at(action_name);

      EXPECT_THAT(
          entry.GetMatchValues(match_name, table, state_->program,
                               *state_->context.z3_context),
          StatusIs(
              absl::StatusCode::kInvalidArgument,
              absl::StrCat("Entry ", index,
                           " of table 'MyIngress.ipv4_lpm' is not symbolic.")));
      EXPECT_THAT(
          entry.GetActionInvocation(action_name, table,
                                    *state_->context.z3_context),
          StatusIs(
              absl::StatusCode::kInvalidArgument,
              absl::StrCat("Entry ", index,
                           " of table 'MyIngress.ipv4_lpm' is not symbolic.")));

      for (const auto &param : entry.GetPdpiIrTableEntry().action().params()) {
        EXPECT_THAT(
            entry.GetActionParameter(param.name(), action, table,
                                     *state_->context.z3_context),
            StatusIs(absl::StatusCode::kInvalidArgument,
                     absl::StrCat(
                         "Entry ", index,
                         " of table 'MyIngress.ipv4_lpm' is not symbolic.")));
      }
    }
  }
}

}  // namespace
}  // namespace p4_symbolic::symbolic
