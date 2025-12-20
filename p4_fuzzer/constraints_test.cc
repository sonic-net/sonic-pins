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

#include "p4_fuzzer/constraints.h"

#include <string>
#include <vector>

#include "absl/log/log.h"
#include "absl/random/random.h"
#include "absl/status/status.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/status.h"  // IWYU pragma: keep
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"  // IWYU pragma: keep
#include "gutil/gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_constraints/ast.pb.h"
#include "p4_constraints/backend/constraint_info.h"
#include "p4_constraints/backend/interpreter.h"
#include "p4_fuzzer/fuzz_util.h"
#include "p4_fuzzer/fuzzer_config.h"
#include "p4_fuzzer/switch_state.h"
#include "p4_fuzzer/test_utils.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"

namespace p4_fuzzer {
namespace {

using gutil::IsOk;
using testing::Not;
using ::testing::SizeIs;

using FuzzValidConstrainedTableEntryWithPartialConstraintTest =
    testing::TestWithParam<std::string>;

// Adds entries that can be referred to by the constrained table.
absl::Status AddReferenceableEntries(absl::BitGen* gen,
                                     const FuzzerConfig& config,
                                     SwitchState& switch_state) {
  ASSIGN_OR_RETURN(pdpi::IrTableDefinition referred_table,
                   gutil::FindOrStatus(config.GetIrP4Info().tables_by_name(),
                                       "one_match_field_table"));
  ASSIGN_OR_RETURN(
      p4::v1::TableEntry referred_table_entry,
      FuzzValidTableEntry(gen, config, switch_state, referred_table));
  p4::v1::Update update;
  *update.mutable_entity()->mutable_table_entry() = referred_table_entry;
  update.set_type(p4::v1::Update::INSERT);
  RETURN_IF_ERROR(switch_state.ApplyUpdate(update));
  return absl::OkStatus();
}

// A set of substrings that capture all interesting portions of the test
// P4Info's constrained_table's entry restrictions. Used individually with
// ExtractConstraintLinesContainingString to extract only a subset of the
// P4-constraint.
std::vector<std::string> GetSupportedConstraintSubstrings() {
  return {
      "normal", "field10bit", "ipv4", "ipv6", "priority", "mac", "val",
      // TODO: P4RT translated values are not yet supported.
      // "nonreferring_str",
      // "referring_str",
  };
}

// A set of substrings that are present in only unsupported portions of the test
// P4Info's constrained_table's entry restrictions. Used individually with
// DeleteConstraintLinesContainingString to avoid unsupported P4-constraints.
std::vector<std::string> GetUnsupportedConstraintPredicates() {
  return {
      // TODO: P4RT translated values are not yet supported.
      "nonreferring_str",
      "referring_str",
  };
}

// Deletes lines containing `string_to_delete` from the constraint on
// `table_id`.
// WARNING: If `string_to_delete` is a subsequence of `entry_restriction(`, this
// function will not work correctly.
absl::Status DeleteConstraintLinesContainingString(
    FuzzerConfig& config, int table_id, absl::string_view string_to_delete) {
  p4::config::v1::P4Info info = config.GetP4Info();
  for (auto& table : *info.mutable_tables()) {
    if (table.preamble().id() == table_id) {
      for (int i = 0; i < table.preamble().annotations_size(); i++) {
        if (absl::StartsWith(table.preamble().annotations(i),
                             "@entry_restriction")) {
          std::string constraint_without_string_to_delete_line = absl::StrJoin(
              // Split by line.
              absl::StrSplit(table.preamble().annotations(i), '\n'), "\n",
              // Filter out lines with `string_to_delete` when joining.
              [&string_to_delete](std::string* out,
                                  absl::string_view constraint) {
                if (!absl::StrContains(constraint, string_to_delete)) {
                  absl::StrAppend(out, constraint);
                }
              });
          table.mutable_preamble()->set_annotations(
              i, constraint_without_string_to_delete_line);
        }
      }
    }
  }

  return config.SetP4Info(info);
}

// Replaces the constraint on `table_id` with only the lines containing
// `string_to_keep`.
// WARNING: If `string_to_keep` is a subsequence of `entry_restriction(`, this
// function will not work correctly.
absl::Status ExtractConstraintLinesContainingString(
    FuzzerConfig& config, int table_id, absl::string_view string_to_keep) {
  p4::config::v1::P4Info info = config.GetP4Info();
  for (auto& table : *info.mutable_tables()) {
    if (table.preamble().id() == table_id) {
      for (int i = 0; i < table.preamble().annotations_size(); i++) {
        if (absl::StartsWith(table.preamble().annotations(i),
                             "@entry_restriction")) {
          std::string constraint_lines_with_string_to_keep = absl::StrJoin(
              // Split by line.
              absl::StrSplit(table.preamble().annotations(i), '\n'), "\n",
              // Keep only lines with `string_to_keep` when joining.
              [&string_to_keep](std::string* out,
                                absl::string_view constraint) {
                if (absl::StrContains(constraint, string_to_keep)) {
                  absl::StrAppend(out, constraint);
                }
              });
          table.mutable_preamble()->set_annotations(
              i, absl::StrCat("@entry_restriction(\"",
                              constraint_lines_with_string_to_keep, "\")"));
        }
      }
    }
  }

  return config.SetP4Info(info);
}

// Removes conjuncts from `config` for `table_id` that relate to P4-Constraints
// which are not yet supported by FuzzValidConstrainedTableEntry. These are
// explicitly listed in `GetUnsupportedConstraintPredicates` above.
absl::Status ApplyUnsupportedFeatureWorkaround(FuzzerConfig& config,
                                               int table_id) {
  LOG(WARNING) << "Removing conjuncts with substrings: \""
               << absl::StrJoin(GetUnsupportedConstraintPredicates(), "\", \"")
               << "\".";
  for (absl::string_view unsupported_constraint_string :
       GetUnsupportedConstraintPredicates()) {
    RETURN_IF_ERROR(DeleteConstraintLinesContainingString(
        config, table_id, unsupported_constraint_string));
  }
  return absl::OkStatus();
}

TEST(UsesP4ConstraintsTest, ReturnsTrueIfTableHasConstraint) {
  p4::config::v1::P4Info p4info =
      gutil::ParseProtoOrDie<p4::config::v1::P4Info>(
          R"pb(tables {
                 preamble {
                   id: 1
                   name: "table1"
                   annotations: "@entry_restriction(\"true\")"
                 }
                 action_refs { id: 1 annotations: "@proto_id(1)" }
               }
               actions { preamble { id: 1 name: "action1" } }
          )pb");
  ASSERT_OK_AND_ASSIGN(FuzzerConfig config,
                       FuzzerConfig::Create(p4info, ConfigParams{}));
  EXPECT_TRUE(UsesP4Constraints(/*table_id=*/1, config));
}

TEST(UsesP4ConstraintsTest, ReturnsFalseIfTableDoesNotHaveConstraint) {
  p4::config::v1::P4Info p4info =
      gutil::ParseProtoOrDie<p4::config::v1::P4Info>(
          R"pb(tables {
                 preamble { id: 1 name: "table1" }
                 action_refs { id: 1 annotations: "@proto_id(1)" }
               }
               actions { preamble { id: 1 name: "action1" } }
          )pb");
  ASSERT_OK_AND_ASSIGN(FuzzerConfig config,
                       FuzzerConfig::Create(p4info, ConfigParams{}));
  EXPECT_FALSE(UsesP4Constraints(/*table_id=*/1, config));
}

TEST(UsesP4ConstraintsTest, ReturnsTrueIffTableHasConstraint) {
  FuzzerTestState fuzzer_state = ConstructStandardFuzzerTestState();
  // Used to ensure that the relevant branches for coverage are taken at least
  // once.
  bool true_branch_taken = false;
  bool false_branch_taken = false;

  for (const auto& [table_id, table] :
       fuzzer_state.config.GetIrP4Info().tables_by_id()) {
    auto* table_info = p4_constraints::GetTableInfoOrNull(
        fuzzer_state.config.GetConstraintInfo(), table_id);
    ASSERT_NE(table_info, nullptr);
    if (table_info->constraint.has_value()) {
      true_branch_taken = true;
      EXPECT_TRUE(UsesP4Constraints(table, fuzzer_state.config));
    } else {
      false_branch_taken = true;
      EXPECT_FALSE(UsesP4Constraints(table, fuzzer_state.config));
    }
  }
  ASSERT_TRUE(true_branch_taken && false_branch_taken);
}

TEST(UsesP4ConstraintsTest, FalseOnNonExistentTable) {
  FuzzerTestState fuzzer_state = ConstructStandardFuzzerTestState();
  pdpi::IrTableDefinition bad_table_definition;
  EXPECT_FALSE(UsesP4Constraints(bad_table_definition, fuzzer_state.config));
}

// Generates a valid entry for a version of 'constrained_table' that does not
// contain unsupported constraints.
TEST(FuzzValidConstrainedTableEntryTest,
     GeneratesValidEntryWithAllSupportedConstraints) {
  FuzzerTestState fuzzer_state = ConstructStandardFuzzerTestState();

  // Get constrained table.
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrTableDefinition constrained_table,
      gutil::FindOrStatus(fuzzer_state.config.GetIrP4Info().tables_by_name(),
                          "constrained_table"));

  // Removes features that are not yet supported by
  // FuzzValidConstrainedTableEntry from `constrained_table`.
  ASSERT_OK(ApplyUnsupportedFeatureWorkaround(
      fuzzer_state.config, constrained_table.preamble().id()));

  // To ensure valid entries for tables with references even exist.
  ASSERT_OK(AddReferenceableEntries(&fuzzer_state.gen, fuzzer_state.config,
                                    fuzzer_state.switch_state));

  // Generate 10 entries and ensure they all meet the constraints.
  for (int i = 0; i < 10; ++i) {
    ASSERT_OK_AND_ASSIGN(p4::v1::TableEntry entry,
                         FuzzValidConstrainedTableEntry(
                             fuzzer_state.config, fuzzer_state.switch_state,
                             constrained_table, fuzzer_state.gen));
    ASSERT_OK_AND_ASSIGN(
        pdpi::IrTableEntry ir_entry,
        pdpi::PiTableEntryToIr(fuzzer_state.config.GetIrP4Info(), entry));
    ASSERT_OK_AND_ASSIGN(std::string failure_reason,
                         p4_constraints::ReasonEntryViolatesConstraint(
                             entry, fuzzer_state.config.GetConstraintInfo()));
    EXPECT_EQ(failure_reason, "")
        << "for ir entry:\n"
        << ir_entry.DebugString() << "\nAnd pi entry:\n"
        << entry.DebugString();
  }
}

TEST(FuzzValidConstrainedTableEntryTest, FailsWithNonExistentTable) {
  FuzzerTestState fuzzer_state = ConstructStandardFuzzerTestState();
  pdpi::IrTableDefinition bad_table_definition;

  EXPECT_THAT(FuzzValidConstrainedTableEntry(
                  fuzzer_state.config, fuzzer_state.switch_state,
                  bad_table_definition, fuzzer_state.gen),
              Not(IsOk()));
}

TEST(FuzzValidConstrainedTableEntryTest, FailsWithUnconstrainedTableTest) {
  p4::config::v1::P4Info p4info =
      gutil::ParseProtoOrDie<p4::config::v1::P4Info>(
          R"pb(tables {
                 preamble { id: 1 name: "unconstrained_table" }
                 action_refs { id: 1 annotations: "@proto_id(1)" }
               }
               actions { preamble { id: 1 name: "action1" } }
          )pb");
  ASSERT_OK_AND_ASSIGN(FuzzerConfig config,
                       FuzzerConfig::Create(p4info, ConfigParams{}));

  // Get the unconstrained table.
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrTableDefinition unconstrained_table,
      gutil::FindOrStatus(config.GetIrP4Info().tables_by_id(), 1));
  absl::BitGen gen;

  EXPECT_THAT(
      FuzzValidConstrainedTableEntry(config, SwitchState(config.GetIrP4Info()),
                                     unconstrained_table, gen),
      Not(IsOk()));
}

TEST(FuzzValidConstrainedTableEntryTest,
     FailsWithUnconstrainedTablesComponentTest) {
  FuzzerTestState fuzzer_state = ConstructStandardFuzzerTestState();
  // Used to ensure that the branch necessary for coverage is taken at least
  // once.
  bool test_was_successfully_executed = false;

  for (const auto& [table_id, table] :
       fuzzer_state.config.GetIrP4Info().tables_by_id()) {
    auto* table_info = p4_constraints::GetTableInfoOrNull(
        fuzzer_state.config.GetConstraintInfo(), table_id);
    ASSERT_NE(table_info, nullptr);
    if (!table_info->constraint.has_value()) {
      test_was_successfully_executed = true;
      EXPECT_THAT(FuzzValidConstrainedTableEntry(fuzzer_state.config,
                                                 fuzzer_state.switch_state,
                                                 table, fuzzer_state.gen),
                  Not(IsOk()));
    }
  }
  ASSERT_TRUE(test_was_successfully_executed);
}

TEST(FuzzValidConstrainedTableEntryTest, FailsWithUnsatisfiableConstraint) {
  p4::config::v1::P4Info p4info =
      gutil::ParseProtoOrDie<p4::config::v1::P4Info>(
          R"pb(tables {
                 preamble {
                   id: 1
                   name: "table1"
                   annotations: "@entry_restriction(\"false\")"
                 }
                 action_refs { id: 1 annotations: "@proto_id(1)" }
               }
               actions { preamble { id: 1 name: "action1" } }
          )pb");
  ASSERT_OK_AND_ASSIGN(FuzzerConfig config,
                       FuzzerConfig::Create(p4info, ConfigParams{}));

  // Get the table with the unsatisfiable constraint.
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrTableDefinition table1,
      gutil::FindOrStatus(config.GetIrP4Info().tables_by_id(), 1));
  absl::BitGen gen;

  EXPECT_THAT(FuzzValidConstrainedTableEntry(
                  config, SwitchState(config.GetIrP4Info()), table1, gen),
              Not(IsOk()));
}

TEST(DisabledConstraintTest, FuzzerDoesNotFuzzDisabledFields) {
  p4::config::v1::P4Info p4info = gutil::ParseProtoOrDie<
      p4::config::v1::P4Info>(
      R"pb(tables {
             preamble {
               id: 1
               name: "table1"
               alias: "table1"
               annotations: "@entry_restriction(\"optional_match_field::mask!=0;lpm_match_field::prefix_length!=0\")"
             }
             match_fields {
               id: 1
               name: "exact_match_field"
               match_type: EXACT
               bitwidth: 16
             }
             match_fields {
               id: 2
               name: "optional_match_field"
               match_type: OPTIONAL
               bitwidth: 16
             }
             match_fields {
               id: 3
               name: "lpm_match_field"
               match_type: LPM
               bitwidth: 16
             }
             action_refs { id: 1 annotations: "@proto_id(1)" }
           }
           actions { preamble { id: 1 name: "action1" } }
      )pb");
  ASSERT_OK_AND_ASSIGN(FuzzerConfig config,
                       FuzzerConfig::Create(p4info, ConfigParams{}));

  // Disable fuzzing on `lpm_match_field` and `optional_match_field`. This
  // makes the fuzzer not generate those match fields.
  ASSERT_OK_AND_ASSIGN(std::string fully_qualified_name_lpm_match_field,
                       GetFullyQualifiedMatchFieldName(
                           config.GetIrP4Info(), "table1", "lpm_match_field"));
  ASSERT_OK_AND_ASSIGN(
      std::string fully_qualified_name_optional_match_field,
      GetFullyQualifiedMatchFieldName(config.GetIrP4Info(), "table1",
                                      "optional_match_field"));

  config.SetDisabledFullyQualifiedNames({
      fully_qualified_name_lpm_match_field,
      fully_qualified_name_optional_match_field,
  });
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrTableDefinition table1,
      gutil::FindOrStatus(config.GetIrP4Info().tables_by_id(), 1));
  absl::BitGen gen;

  for (int i = 0; i < 100; ++i) {
    ASSERT_OK_AND_ASSIGN(
        p4::v1::TableEntry entry,
        FuzzValidConstrainedTableEntry(
            config, SwitchState(config.GetIrP4Info()), table1, gen));
    // The fuzzer should generate only `exact_match_field`.
    ASSERT_THAT(entry.match(), SizeIs(1));
    EXPECT_EQ(entry.match(0).field_id(), /*ID of exact_match_field*/ 1);
  }
}

TEST(FuzzValidConstrainedTableEntryTest,
     SucceedsIfMatchFieldsAreUnconstrained) {
  p4::config::v1::P4Info p4info =
      gutil::ParseProtoOrDie<p4::config::v1::P4Info>(
          R"pb(tables {
                 preamble {
                   id: 1
                   name: "table1"
                   annotations: "@entry_restriction(\"true\")"
                 }
                 match_fields {
                   id: 1
                   name: "exact_match_field"
                   match_type: EXACT
                   bitwidth: 16
                 }
                 action_refs { id: 1 annotations: "@proto_id(1)" }
               }
               actions { preamble { id: 1 name: "action1" } }
          )pb");
  ASSERT_OK_AND_ASSIGN(FuzzerConfig config,
                       FuzzerConfig::Create(p4info, ConfigParams{}));

  // Get the table with the P4Runtime translated match.
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrTableDefinition table1,
      gutil::FindOrStatus(config.GetIrP4Info().tables_by_id(), 1));
  absl::BitGen gen;

  EXPECT_OK(FuzzValidConstrainedTableEntry(
      config, SwitchState(config.GetIrP4Info()), table1, gen));
}

TEST(FuzzValidConstrainedTableEntryTest,
     SucceedsIfTableHasUnconstrainedExactP4runtimeTranslatedMatch) {
  p4::config::v1::P4Info p4info =
      gutil::ParseProtoOrDie<p4::config::v1::P4Info>(
          R"pb(tables {
                 preamble {
                   id: 1
                   name: "table1"
                   annotations: "@entry_restriction(\"true\")"
                 }
                 match_fields {
                   id: 1
                   name: "exact_p4runtime_translated"
                   match_type: EXACT
                   type_name { name: "p4runtime_translated_type" }
                 }
                 action_refs { id: 1 annotations: "@proto_id(1)" }
               }
               actions { preamble { id: 1 name: "action1" } }
               type_info {
                 new_types {
                   key: "p4runtime_translated_type"
                   value { translated_type { sdn_string {} } }
                 }
               }
          )pb");
  ASSERT_OK_AND_ASSIGN(FuzzerConfig config,
                       FuzzerConfig::Create(p4info, ConfigParams{}));

  // Get the table with the P4Runtime translated match.
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrTableDefinition table1,
      gutil::FindOrStatus(config.GetIrP4Info().tables_by_id(), 1));
  absl::BitGen gen;

  EXPECT_OK(FuzzValidConstrainedTableEntry(
      config, SwitchState(config.GetIrP4Info()), table1, gen));
}

TEST(FuzzValidConstrainedTableEntryTest,
     SucceedsIfTableHasConstrainedOptionalP4runtimeTranslatedMatch) {
  p4::config::v1::P4Info p4info =
      gutil::ParseProtoOrDie<p4::config::v1::P4Info>(
          R"pb(tables {
                 preamble {
                   id: 1
                   name: "table1"
                   annotations: "@entry_restriction(\"true\")"
                 }
                 match_fields {
                   id: 1
                   name: "exact_p4runtime_translated"
                   match_type: OPTIONAL
                   type_name { name: "p4runtime_translated_type" }
                 }
                 action_refs { id: 1 annotations: "@proto_id(1)" }
               }
               actions { preamble { id: 1 name: "action1" } }
               type_info {
                 new_types {
                   key: "p4runtime_translated_type"
                   value { translated_type { sdn_string {} } }
                 }
               }
          )pb");
  ASSERT_OK_AND_ASSIGN(FuzzerConfig config,
                       FuzzerConfig::Create(p4info, ConfigParams{}));

  // Get the table with the P4Runtime translated match.
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrTableDefinition table1,
      gutil::FindOrStatus(config.GetIrP4Info().tables_by_id(), 1));
  absl::BitGen gen;

  EXPECT_OK(FuzzValidConstrainedTableEntry(
      config, SwitchState(config.GetIrP4Info()), table1, gen));
}

// Generates a valid entry for a version of 'constrained_table' that is only
// constrained by a conjunct containing the given string parameter.
// Provides more granular coverage for easier debugging.
TEST_P(FuzzValidConstrainedTableEntryWithPartialConstraintTest,
       GenerateValidEntry) {
  FuzzerTestState fuzzer_state = ConstructStandardFuzzerTestState();

  // Get constrained table.
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrTableDefinition constrained_table,
      gutil::FindOrStatus(fuzzer_state.config.GetIrP4Info().tables_by_name(),
                          "constrained_table"));

  // Modify constraints to only contain the sub-constraints we want to test.
  ASSERT_OK(ExtractConstraintLinesContainingString(
      fuzzer_state.config, constrained_table.preamble().id(), GetParam()));

  // To ensure valid entries for tables with references even exist.
  ASSERT_OK(AddReferenceableEntries(&fuzzer_state.gen, fuzzer_state.config,
                                    fuzzer_state.switch_state));

  // Generate 10 entries and ensure they all meet the constraints.
  for (int i = 0; i < 10; ++i) {
    ASSERT_OK_AND_ASSIGN(p4::v1::TableEntry entry,
                         FuzzValidConstrainedTableEntry(
                             fuzzer_state.config, fuzzer_state.switch_state,
                             constrained_table, fuzzer_state.gen));
    ASSERT_OK_AND_ASSIGN(
        pdpi::IrTableEntry ir_entry,
        pdpi::PiTableEntryToIr(fuzzer_state.config.GetIrP4Info(), entry));
    ASSERT_OK_AND_ASSIGN(std::string failure_reason,
                         p4_constraints::ReasonEntryViolatesConstraint(
                             entry, fuzzer_state.config.GetConstraintInfo()));
    EXPECT_EQ(failure_reason, "")
        << "for ir entry:\n"
        << ir_entry.DebugString() << "\nAnd pi entry:\n"
        << entry.DebugString();
  }
}

INSTANTIATE_TEST_SUITE_P(
    PartialConstraintTestForSupportedConstraints,
    FuzzValidConstrainedTableEntryWithPartialConstraintTest,
    testing::ValuesIn(GetSupportedConstraintSubstrings()),
    [](const testing::TestParamInfo<std::string>& info) {
      return gutil::SnakeCaseToCamelCase(info.param);
    });

}  // namespace
}  // namespace p4_fuzzer
