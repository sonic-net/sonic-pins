#include "p4_pdpi/reference_annotations.h"

#include <optional>
#include <string>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "gmock/gmock.h"
#include "google/protobuf/repeated_ptr_field.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/testing/test_p4info.h"
#include "p4rt_app/utils/ir_builder.h"

namespace pdpi {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::gutil::ParseProtoOrDie;
using ::gutil::StatusIs;
using ::p4rt_app::IrActionDefinitionBuilder;
using ::p4rt_app::IrP4InfoBuilder;
using ::p4rt_app::IrTableDefinitionBuilder;
using ::testing::ElementsAre;
using ::testing::Eq;
using ::testing::IsEmpty;

// -- Matchers -----------------------------------------------------------------

MATCHER_P2(HasTableAndField, table, field,
           absl::Substitute("Matches: [table: $0, field: $1]", table, field)) {
  return arg.table == table && arg.field == field;
}

// -- Parse Annotation Tests ---------------------------------------------------

TEST(ParseAllRefersToAnnotationArgs, ReturnsAllRefersToAnnotations) {
  google::protobuf::RepeatedPtrField<std::string> annotations;
  annotations.Add("@refers_to(a,b)");
  annotations.Add("@referenced_by(c,d)");
  annotations.Add("@refers_to(\n        e,f  \t)");
  EXPECT_THAT(ParseAllRefersToAnnotations(annotations),
              IsOkAndHolds(ElementsAre(HasTableAndField("a", "b"),
                                       HasTableAndField("e", "f"))));
}

TEST(ParseAllRefersToAnnotationArgs,
     FailsWithRefersToWithMoreThanTwoArguments) {
  google::protobuf::RepeatedPtrField<std::string> annotations;
  annotations.Add("@refers_to(a,b,c)");
  EXPECT_THAT(ParseAllRefersToAnnotations(annotations),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(ParseAllReferencedByAnnotationArgs, ReturnsAllRefersToAnnotations) {
  google::protobuf::RepeatedPtrField<std::string> annotations;
  annotations.Add("@referenced_by(a,b)");
  annotations.Add("@refers_to(c,d)");
  annotations.Add("@referenced_by(\n        e,f  \t)");
  EXPECT_THAT(ParseAllReferencedByAnnotations(annotations),
              IsOkAndHolds(ElementsAre(HasTableAndField("a", "b"),
                                       HasTableAndField("e", "f"))));
}

TEST(ParseAllReferencedByAnnotationArgs,
     FailsWithReferencedByWithMoreThanTwoArguments) {
  google::protobuf::RepeatedPtrField<std::string> annotations;
  annotations.Add("@referenced_by(a,b,c)");
  EXPECT_THAT(ParseAllReferencedByAnnotations(annotations),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

// -- CreateIrTable Tests ------------------------------------------------------

TEST(CreateIrTable, WorksForBuiltInTable) {
  EXPECT_THAT(
      CreateIrTable("builtin::multicast_group_table", GetTestIrP4Info()),
      IsOkAndHolds(EqualsProto(ParseProtoOrDie<IrTable>(
          R"pb(
            built_in_table: BUILT_IN_TABLE_MULTICAST_GROUP_TABLE
          )pb"))));
}

TEST(CreateIrTable, WorksForBuiltInTableWithEmptyP4Info) {
  EXPECT_THAT(CreateIrTable("builtin::multicast_group_table", IrP4Info()),
              IsOkAndHolds(EqualsProto(ParseProtoOrDie<IrTable>(
                  R"pb(
                    built_in_table: BUILT_IN_TABLE_MULTICAST_GROUP_TABLE
                  )pb"))));
}

TEST(CreateIrTable, WorksForP4Table) {
  // Setup: Grab P4 table from test program and populate proto.
  IrP4Info info = GetTestIrP4Info();
  ASSERT_TRUE(!info.tables_by_name().empty());
  pdpi::IrTableDefinition table = info.tables_by_name().begin()->second;
  IrTable expected_ir_table;
  expected_ir_table.mutable_p4_table()->set_table_name(
      table.preamble().alias());
  expected_ir_table.mutable_p4_table()->set_table_id(table.preamble().id());

  // Execute and Test:
  EXPECT_THAT(CreateIrTable(table.preamble().alias(), info),
              IsOkAndHolds(EqualsProto(expected_ir_table)));
}

TEST(CreateIrTable, FailsForUnknownTable) {
  EXPECT_THAT(CreateIrTable("dragon_table", IrP4Info()),
              StatusIs(absl::StatusCode::kNotFound));
}

// -- CreateIrField Tests ------------------------------------------------------

TEST(CreateIrBuiltInField, WorksForBuiltInField) {
  EXPECT_THAT(CreateIrBuiltInField("builtin::multicast_group_table",
                                   "multicast_group_id"),
              IsOkAndHolds(Eq(BUILT_IN_FIELD_MULTICAST_GROUP_ID)));
}

TEST(CreateIrBuiltInField, FailsForUnknownTable) {
  EXPECT_THAT(CreateIrBuiltInField("dragon_table", "multicast_group_id"),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(CreateIrBuiltInField, FailsForUnknownField) {
  EXPECT_THAT(
      CreateIrBuiltInField("builtin::multicast_group_table", "dragon_field"),
      StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(CreateIrMatchField, WorksForExactMatchField) {
  // Setup: Grab an existing table and match field from the p4 info such that
  // the field is of type exact and belongs to the table.
  IrP4Info info = GetTestIrP4Info();
  ASSERT_TRUE(!info.tables_by_name().empty());
  std::optional<pdpi::IrTableDefinition> table;
  std::optional<pdpi::IrMatchFieldDefinition> match_field;
  for (const auto& [name, table_def] : info.tables_by_name()) {
    for (const auto& [name, match_field_def] :
         table_def.match_fields_by_name()) {
      if (match_field_def.match_field().match_type() ==
          p4::config::v1::MatchField::EXACT) {
        table = table_def;
        match_field = match_field_def;
      }
    }
  }
  ASSERT_TRUE(table.has_value() && match_field.has_value());
  // Populate proto with the match_field info.
  IrMatchField expected_ir_field;
  expected_ir_field.set_field_name(match_field->match_field().name());
  expected_ir_field.set_field_id(match_field->match_field().id());

  // Execute and Test:
  EXPECT_THAT(CreateIrMatchField(table->preamble().alias(),
                                 match_field->match_field().name(), info),
              IsOkAndHolds(EqualsProto(expected_ir_field)));
}

TEST(CreateIrMatchField, FailsForNonExactMatchField) {
  // Setup: Grab a table and match field such that the field is NOT of type
  // exact and belongs to the table.
  IrP4Info info = GetTestIrP4Info();
  ASSERT_TRUE(!info.tables_by_name().empty());
  std::optional<pdpi::IrTableDefinition> table;
  std::optional<pdpi::IrMatchFieldDefinition> match_field;
  for (const auto& [name, table_def] : info.tables_by_name()) {
    for (const auto& [name, match_field_def] :
         table_def.match_fields_by_name()) {
      if (match_field_def.match_field().match_type() !=
          p4::config::v1::MatchField::EXACT) {
        table = table_def;
        match_field = match_field_def;
      }
    }
  }
  ASSERT_TRUE(table.has_value() && match_field.has_value());

  // Execute and Test:
  EXPECT_THAT(CreateIrMatchField(table->preamble().alias(),
                                 match_field->match_field().name(), info),
              StatusIs(absl::StatusCode::kUnimplemented));
}

TEST(CreateIrMatchField, FailsForUnknownTable) {
  EXPECT_THAT(CreateIrMatchField("dragon_table", "dragon_field", IrP4Info()),
              StatusIs(absl::StatusCode::kNotFound));
}

TEST(CreateIrMatchField, FailsForUnknownField) {
  // Setup: Grab some known table to avoid unknown table failure.
  IrP4Info info = GetTestIrP4Info();
  ASSERT_TRUE(!info.tables_by_name().empty());
  absl::string_view table_name =
      info.tables_by_name().begin()->second.preamble().alias();

  // Execute and Test:
  EXPECT_THAT(CreateIrMatchField(table_name, "dragon_field", info),
              StatusIs(absl::StatusCode::kNotFound));
}

TEST(CreateIrActionField, WorksForActionField) {
  // Setup: Grab an existing action and parameter from the p4 info.
  IrP4Info info = GetTestIrP4Info();
  ASSERT_TRUE(!info.tables_by_name().empty());
  std::optional<pdpi::IrActionDefinition> action;
  for (const auto& [name, action_def] : info.actions_by_name()) {
    if (!action_def.params_by_name().empty()) {
      action = action_def;
    }
  }
  ASSERT_TRUE(action.has_value());
  pdpi::IrActionDefinition::IrActionParamDefinition param =
      action->params_by_name().begin()->second;
  // Populate proto with action and parameter information.
  IrActionField expected_ir_field;
  expected_ir_field.set_action_name(action->preamble().alias());
  expected_ir_field.set_action_id(action->preamble().id());
  expected_ir_field.set_parameter_name(param.param().name());
  expected_ir_field.set_parameter_id(param.param().id());

  // Execute and Test:
  EXPECT_THAT(CreateIrActionField(action->preamble().alias(),
                                  param.param().name(), info),
              IsOkAndHolds(EqualsProto(expected_ir_field)));
}

TEST(CreateIrActionField, FailsForUnknownAction) {
  EXPECT_THAT(CreateIrActionField("dragon_action", "dragon_param", IrP4Info()),
              StatusIs(absl::StatusCode::kNotFound));
}

TEST(CreateIrActionField, FailsForUnknownParam) {
  // Setup: Grab some known action to avoid unknown action failure.
  IrP4Info info = GetTestIrP4Info();
  ASSERT_TRUE(!info.tables_by_name().empty());
  absl::string_view action_name =
      info.actions_by_name().begin()->second.preamble().alias();

  // Execute and Test:
  EXPECT_THAT(CreateIrActionField(action_name, "dragon_param", info),
              StatusIs(absl::StatusCode::kNotFound));
}

// -- Reference Annotation Tests -----------------------------------------------

// The implementation of CreateIrFieldFromRefersTo/ReferencedBy uses the
// CreateIr*Field functions which have thorough coverage above, so this coverage
// will only include the failures unique to each function and one passing
// example.

TEST(CreateIrFieldFromRefersTo, WorksForMatchField) {
  // Setup: Grab an existing table and match field from the p4 info such that
  // the field is of type exact and belongs to the table.
  IrP4Info info = GetTestIrP4Info();
  ASSERT_TRUE(!info.tables_by_name().empty());
  std::optional<pdpi::IrTableDefinition> table;
  std::optional<pdpi::IrMatchFieldDefinition> match_field;
  for (const auto& [name, table_def] : info.tables_by_name()) {
    for (const auto& [name, match_field_def] :
         table_def.match_fields_by_name()) {
      if (match_field_def.match_field().match_type() ==
          p4::config::v1::MatchField::EXACT) {
        table = table_def;
        match_field = match_field_def;
      }
    }
  }
  ASSERT_TRUE(table.has_value() && match_field.has_value());
  // Populate proto with info.
  IrField expected_ir_field;
  expected_ir_field.mutable_match_field()->set_field_name(
      match_field->match_field().name());
  expected_ir_field.mutable_match_field()->set_field_id(
      match_field->match_field().id());

  // Execute And Test:
  EXPECT_THAT(CreateIrFieldFromRefersTo(
                  ParsedRefersToAnnotation{
                      .table = table->preamble().alias(),
                      .field = match_field->match_field().name(),
                  },
                  info),
              IsOkAndHolds(EqualsProto(expected_ir_field)));
}

TEST(CreateIrFieldFromRefersTo, FailsForAction) {
  // Setup: Grab known action and param for annotation.
  IrP4Info info = GetTestIrP4Info();
  ASSERT_TRUE(!info.actions_by_name().empty());
  std::optional<pdpi::IrActionDefinition> action;
  for (const auto& [name, action_def] : info.actions_by_name()) {
    if (!action_def.params_by_name().empty()) {
      action = action_def;
    }
  }
  ASSERT_TRUE(action.has_value());
  pdpi::IrActionDefinition::IrActionParamDefinition param =
      action->params_by_name().begin()->second;

  // Execute and Test:
  EXPECT_THAT(CreateIrFieldFromRefersTo(
                  ParsedRefersToAnnotation{
                      .table = action->preamble().alias(),
                      .field = param.param().name(),
                  },
                  info),
              StatusIs(absl::StatusCode::kUnimplemented));
}

TEST(CreateIrFieldFromReferencedBy, WorksForBuiltInField) {
  EXPECT_THAT(CreateIrFieldFromReferencedBy(
                  ParsedReferencedByAnnotation{
                      .table = "builtin::multicast_group_table",
                      .field = "multicast_group_id",
                  },
                  IrP4Info()),
              IsOkAndHolds(EqualsProto(ParseProtoOrDie<IrField>(
                  R"pb(
                    built_in_field: BUILT_IN_FIELD_MULTICAST_GROUP_ID
                  )pb"))));
}

TEST(CreateIrFieldFromReferencedBy, FailsForMatchField) {
  // Setup: Grab an existing table and match field from the p4 info such that
  // the field is of type exact and belongs to the table.
  IrP4Info info = GetTestIrP4Info();
  ASSERT_TRUE(!info.tables_by_name().empty());

  std::optional<pdpi::IrTableDefinition> table;
  std::optional<pdpi::IrMatchFieldDefinition> match_field;
  for (const auto& [name, table_def] : info.tables_by_name()) {
    for (const auto& [name, match_field_def] :
         table_def.match_fields_by_name()) {
      if (match_field_def.match_field().match_type() ==
          p4::config::v1::MatchField::EXACT) {
        table = table_def;
        match_field = match_field_def;
      }
    }
  }
  ASSERT_TRUE(table.has_value() && match_field.has_value());

  // Execute and Test:
  EXPECT_THAT(CreateIrFieldFromReferencedBy(
                  ParsedReferencedByAnnotation{
                      .table = table->preamble().alias(),
                      .field = match_field->match_field().name(),
                  },
                  info),
              StatusIs(absl::StatusCode::kUnimplemented));
}

TEST(CreateIrFieldFromReferencedBy, FailsWhenReferencedByAction) {
  // Setup: Grab an existing action and parameter from the p4 info.
  IrP4Info info = GetTestIrP4Info();
  ASSERT_TRUE(!info.tables_by_name().empty());

  std::optional<pdpi::IrActionDefinition> action;
  for (const auto& [name, action_def] : info.actions_by_name()) {
    if (!action_def.params_by_name().empty()) {
      action = action_def;
    }
  }
  ASSERT_TRUE(action.has_value());
  pdpi::IrActionDefinition::IrActionParamDefinition param =
      action->params_by_name().begin()->second;

  // Execute and Test:
  EXPECT_THAT(CreateIrFieldFromReferencedBy(
                  ParsedReferencedByAnnotation{
                      .table = action->preamble().alias(),
                      .field = param.param().name(),
                  },
                  info),
              StatusIs(absl::StatusCode::kUnimplemented));
}

// -- ParseIrTableReferencesTest ------------------------------------------

TEST(ParseIrTableReferences, CreateEmptyListWhenNoReferenceAnnotationsExist) {
  EXPECT_THAT(ParseIrTableReferences(IrP4Info()), IsOkAndHolds(IsEmpty()));
}

TEST(ParseIrTableReferences, SucceedsWithMatchToMatchReference) {
  // Setup: Create p4 info.
  auto src_table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(id: 2)pb")
          .name("src_table")
          .match_field(
              R"pb(
                id: 1
                name: "src_match_field"
                match_type: EXACT
                annotations: "@refers_to(dst_table, dst_match_field)"
              )pb",
              pdpi::Format::STRING)();
  auto dst_table = IrTableDefinitionBuilder()
                       .preamble(R"pb(id: 3)pb")
                       .name("dst_table")
                       .match_field(
                           R"pb(
                             id: 1 name: "dst_match_field" match_type: EXACT
                           )pb",
                           pdpi::Format::STRING)();
  auto info = IrP4InfoBuilder().table(src_table).table(dst_table)();

  // Execute and Test:
  EXPECT_THAT(
      ParseIrTableReferences(info),
      IsOkAndHolds(
          ElementsAre(EqualsProto(ParseProtoOrDie<IrTableReference>(R"pb(
            source_table { p4_table { table_name: "src_table" table_id: 2 } }
            destination_table {
              p4_table { table_name: "dst_table" table_id: 3 }
            }
            field_references {
              source {
                match_field { field_name: "src_match_field" field_id: 1 }
              }
              destination {
                match_field { field_name: "dst_match_field" field_id: 1 }
              }
            }
          )pb")))));
}

TEST(ParseIrTableReferences, SucceedsWithActionToMatchReference) {
  // Setup: Create p4 info.
  auto src_action =
      IrActionDefinitionBuilder()
          .preamble(R"pb(id: 1)pb")
          .name("src_action")
          .param(
              R"pb(
                id: 1
                name: "src_param"
                annotations: "@refers_to(dst_table, dst_match_field)"
              )pb")();
  auto src_table = IrTableDefinitionBuilder()
                       .preamble(R"pb(id: 2)pb")
                       .name("src_table")
                       .match_field(
                           R"pb(
                             id: 1 name: "src_match_field" match_type: EXACT
                           )pb",
                           pdpi::Format::STRING)
                       .entry_action(src_action)();
  auto dst_table = IrTableDefinitionBuilder()
                       .preamble(R"pb(id: 3)pb")
                       .name("dst_table")
                       .match_field(
                           R"pb(
                             id: 1 name: "dst_match_field" match_type: EXACT
                           )pb",
                           pdpi::Format::STRING)();
  auto info =
      IrP4InfoBuilder().action(src_action).table(src_table).table(dst_table)();

  // Execute and Test:
  EXPECT_THAT(
      ParseIrTableReferences(info),
      IsOkAndHolds(
          ElementsAre(EqualsProto(ParseProtoOrDie<IrTableReference>(R"pb(
            source_table { p4_table { table_name: "src_table" table_id: 2 } }
            destination_table {
              p4_table { table_name: "dst_table" table_id: 3 }
            }
            field_references {
              source {
                action_field {
                  action_name: "src_action"
                  action_id: 1
                  parameter_name: "src_param"
                  parameter_id: 1
                }
              }
              destination {
                match_field { field_name: "dst_match_field" field_id: 1 }
              }
            }
          )pb")))));
}

TEST(ParseIrTableReferences, SucceedsWithMatchToBuiltInReference) {
  // Setup: Create p4 info.
  auto src_table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(id: 2)pb")
          .name("src_table")
          .match_field(
              R"pb(
                id: 1
                name: "src_match_field"
                match_type: EXACT
                annotations: "@refers_to(builtin::multicast_group_table, multicast_group_id)"
              )pb",
              pdpi::Format::STRING)();
  auto info = IrP4InfoBuilder().table(src_table)();

  // Execute and Test:
  EXPECT_THAT(
      ParseIrTableReferences(info),
      IsOkAndHolds(
          ElementsAre(EqualsProto(ParseProtoOrDie<IrTableReference>(R"pb(
            source_table { p4_table { table_name: "src_table" table_id: 2 } }
            destination_table {
              built_in_table: BUILT_IN_TABLE_MULTICAST_GROUP_TABLE
            }
            field_references {
              source {
                match_field { field_name: "src_match_field" field_id: 1 }
              }
              destination { built_in_field: BUILT_IN_FIELD_MULTICAST_GROUP_ID }
            }
          )pb")))));
}

TEST(ParseIrTableReferences, SucceedsWithActionToBuiltInReference) {
  // Setup: Create p4 info.
  auto src_action =
      IrActionDefinitionBuilder()
          .preamble(R"pb(id: 1)pb")
          .name("src_action")
          .param(
              R"pb(
                id: 1
                name: "src_param"
                annotations: "@refers_to(builtin::multicast_group_table, multicast_group_id)"
              )pb")();
  auto src_table = IrTableDefinitionBuilder()
                       .preamble(R"pb(id: 2)pb")
                       .name("src_table")
                       .match_field(
                           R"pb(
                             id: 1 name: "src_match_field" match_type: EXACT
                           )pb",
                           pdpi::Format::STRING)
                       .entry_action(src_action)();
  auto info = IrP4InfoBuilder().action(src_action).table(src_table)();

  // Execute and Test:
  EXPECT_THAT(
      ParseIrTableReferences(info),
      IsOkAndHolds(
          ElementsAre(EqualsProto(ParseProtoOrDie<IrTableReference>(R"pb(
            source_table { p4_table { table_name: "src_table" table_id: 2 } }
            destination_table {
              built_in_table: BUILT_IN_TABLE_MULTICAST_GROUP_TABLE
            }
            field_references {
              source {
                action_field {
                  action_name: "src_action"
                  action_id: 1
                  parameter_name: "src_param"
                  parameter_id: 1
                }
              }
              destination { built_in_field: BUILT_IN_FIELD_MULTICAST_GROUP_ID }
            }
          )pb")))));
}

TEST(ParseIrTableReferences, SucceedsWithBuiltInToMatchReference) {
  // Setup: Create p4 info.
  auto dst_table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(id: 3)pb")
          .name("dst_table")
          .match_field(
              R"pb(
                id: 1
                name: "dst_match_field"
                match_type: EXACT
                annotations: "@referenced_by(builtin::multicast_group_table, replica.instance)"
              )pb",
              pdpi::Format::STRING)();
  auto info = IrP4InfoBuilder().table(dst_table)();

  // Execute and Test:
  EXPECT_THAT(
      ParseIrTableReferences(info),
      IsOkAndHolds(
          ElementsAre(EqualsProto(ParseProtoOrDie<IrTableReference>(R"pb(
            source_table {
              built_in_table: BUILT_IN_TABLE_MULTICAST_GROUP_TABLE
            }
            destination_table {
              p4_table { table_name: "dst_table" table_id: 3 }
            }
            field_references {
              source { built_in_field: BUILT_IN_FIELD_REPLICA_INSTANCE }
              destination {
                match_field { field_name: "dst_match_field" field_id: 1 }
              }
            }
          )pb")))));
}

TEST(ParseIrTableReferences, FailsWithRefersToUnknown) {
  // Setup: Create p4 info.
  auto src_table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(id: 2)pb")
          .name("src_table")
          .match_field(
              R"pb(
                id: 1
                name: "src_match_field"
                match_type: EXACT
                annotations: "@refers_to(dragon_table, dragon_field)"
              )pb",
              pdpi::Format::STRING)();
  auto info = IrP4InfoBuilder().table(src_table)();

  // Execute and Test:
  EXPECT_THAT(ParseIrTableReferences(info),
              StatusIs(absl::StatusCode::kNotFound));
}

TEST(ParseIrTableReferences, FailsWithRefersToAction) {
  // Setup: Create p4 info.
  auto dst_action = IrActionDefinitionBuilder()
                        .preamble(R"pb(id: 1)pb")
                        .name("dst_action")
                        .param(
                            R"pb(
                              id: 1 name: "dst_param"
                            )pb")();
  auto src_table = IrTableDefinitionBuilder()
                       .preamble(R"pb(id: 2)pb")
                       .name("src_table")
                       .match_field(
                           R"pb(
                             id: 1
                             name: "src_match_field"
                             match_type: EXACT
                             annotations: "@refers_to(dst_action, dst_param)"
                           )pb",
                           pdpi::Format::STRING)();
  auto info = IrP4InfoBuilder().action(dst_action).table(src_table)();

  // Execute and Test:
  EXPECT_THAT(ParseIrTableReferences(info),
              StatusIs(absl::StatusCode::kUnimplemented));
}

TEST(ParseIrTableReferences, FailsWithReferencedByOnAction) {
  // Setup: Create p4 info.
  auto dst_action =
      IrActionDefinitionBuilder()
          .preamble(R"pb(id: 1)pb")
          .name("dst_action")
          .param(
              R"pb(
                id: 1
                name: "dst_param"
                annotations: "@referenced_by(src_table, src_match_field)"
              )pb")();
  auto src_table = IrTableDefinitionBuilder()
                       .preamble(R"pb(id: 2)pb")
                       .name("src_table")
                       .match_field(
                           R"pb(
                             id: 1 name: "src_match_field" match_type: EXACT
                           )pb",
                           pdpi::Format::STRING)();
  auto info = IrP4InfoBuilder().action(dst_action).table(src_table)();

  // Execute and Test:
  EXPECT_THAT(ParseIrTableReferences(info),
              StatusIs(absl::StatusCode::kUnimplemented));
}

TEST(ParseIrTableReferences, FailsWithTypeOptional) {
  // Setup: Create p4 info.
  auto src_table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(id: 2)pb")
          .name("src_table")
          .match_field(
              R"pb(
                id: 1
                name: "src_match_field"
                match_type: OPTIONAL
                annotations: "@refers_to(dst_table, dst_match_field)"
              )pb",
              pdpi::Format::STRING)();
  auto dst_table = IrTableDefinitionBuilder()
                       .preamble(R"pb(id: 3)pb")
                       .name("dst_table")
                       .match_field(
                           R"pb(
                             id: 1 name: "dst_match_field" match_type: EXACT
                           )pb",
                           pdpi::Format::STRING)();
  auto info = IrP4InfoBuilder().table(src_table).table(dst_table)();

  // Execute and Test:
  EXPECT_THAT(ParseIrTableReferences(info),
              StatusIs(absl::StatusCode::kUnimplemented));
}

TEST(ParseIrTableReferences, FailsWithReferenceByThanCanBeRefersTo) {
  // Setup: Create p4 info.
  auto src_table = IrTableDefinitionBuilder()
                       .preamble(R"pb(id: 2)pb")
                       .name("src_table")
                       .match_field(
                           R"pb(
                             id: 1 name: "src_match_field" match_type: EXACT
                           )pb",
                           pdpi::Format::STRING)();
  auto dst_table =
      IrTableDefinitionBuilder()
          .preamble(R"pb(id: 3)pb")
          .name("dst_table")
          .match_field(
              R"pb(
                id: 1
                name: "dst_match_field"
                match_type: EXACT
                annotations: "@referenced_by(src_table, src_match_field)"
              )pb",
              pdpi::Format::STRING)();
  auto info = IrP4InfoBuilder().table(src_table).table(dst_table)();

  // Execute and Test:
  EXPECT_THAT(ParseIrTableReferences(info),
              StatusIs(absl::StatusCode::kUnimplemented));
}

TEST(ParseIrTableReferences, FailsWithReferenceOnDefaultAction) {
  // Setup: Create p4 info.
  auto src_action =
      IrActionDefinitionBuilder()
          .preamble(R"pb(id: 1)pb")
          .name("src_action")
          .param(
              R"pb(
                id: 1
                name: "src_param"
                annotations: "@refers_to(builtin::multicast_group_table, multicast_group_id)"
              )pb")();
  auto src_table = IrTableDefinitionBuilder()
                       .preamble(R"pb(id: 2)pb")
                       .name("src_table")
                       .match_field(
                           R"pb(
                             id: 1 name: "src_match_field" match_type: EXACT
                           )pb",
                           pdpi::Format::STRING)
                       .default_only_action(src_action)();
  auto info = IrP4InfoBuilder().action(src_action).table(src_table)();

  // Execute and Test:
  EXPECT_THAT(ParseIrTableReferences(info),
              StatusIs(absl::StatusCode::kUnimplemented));
}

}  // namespace
}  // namespace pdpi
