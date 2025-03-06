#include "p4_fuzzer/fuzzer_config.h"

#include <string>

#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"

namespace p4_fuzzer {
namespace {

using ::gutil::ParseProtoOrDie;
using ::gutil::StatusIs;
using ::p4::config::v1::MatchField;
using ::p4::config::v1::P4Info;
using ::p4::config::v1::Table;

// A P4info that contains a table with 2 keys:
//  1) EXACT key with bitstring<16> type (HEX_STRING format)
//  2) EXACT key with P4Runtime translated type (STRING format)
// and another table with a single key of type bitstring<2> (HEX_STRING format).
p4::config::v1::P4Info SimpleP4Info() {
  return ParseProtoOrDie<P4Info>(
      R"pb(
        tables {
          preamble { id: 1 name: "ingress.simple_table" alias: "simple_table" }
          match_fields { id: 1 name: "hex_key" bitwidth: 16 match_type: EXACT }
          match_fields {
            id: 2
            name: "string_key"
            match_type: EXACT
            type_name { name: "string_id_t" }
          }
          size: 1024
        }
        tables {
          preamble {
            id: 2
            name: "ingress.simpler_table"
            alias: "simpler_table"
          }
          match_fields {
            id: 1
            name: "simple_hex_key"
            bitwidth: 2
            match_type: EXACT
          }
          size: 1
        }
        type_info {
          new_types {
            key: "string_id_t"
            value { translated_type { sdn_string {} } }
          }
        }
      )pb");
}

TEST(CreateTest, SucceedsForSimpleP4Info) {
  EXPECT_OK(FuzzerConfig::Create(SimpleP4Info(), ConfigParams{}));
}

// The two functions for getting fully qualified match field names should
// return the same result with the same/equivalent inputs.
TEST(GetFullyQualifiedMatchFieldNameTest, TwoFunctionsReturnSameResult) {
  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(SimpleP4Info()));
  ASSERT_OK_AND_ASSIGN(std::string fully_qualified_name_via_string,
                       GetFullyQualifiedMatchFieldName(
                           ir_p4info, "ingress.simple_table", "hex_key"));
  ASSERT_OK_AND_ASSIGN(std::string fully_qualified_name_via_defn,
                       GetFullyQualifiedMatchFieldName(
                           ir_p4info.tables_by_name().at("simple_table"),
                           ir_p4info.tables_by_name()
                               .at("simple_table")
                               .match_fields_by_name()
                               .at("hex_key")));
  EXPECT_EQ(fully_qualified_name_via_string, fully_qualified_name_via_defn);

  ASSERT_OK_AND_ASSIGN(fully_qualified_name_via_string,
                       GetFullyQualifiedMatchFieldName(
                           ir_p4info, "ingress.simple_table", "string_key"));
  ASSERT_OK_AND_ASSIGN(fully_qualified_name_via_defn,
                       GetFullyQualifiedMatchFieldName(
                           ir_p4info.tables_by_name().at("simple_table"),
                           ir_p4info.tables_by_name()
                               .at("simple_table")
                               .match_fields_by_name()
                               .at("string_key")));
  EXPECT_EQ(fully_qualified_name_via_string, fully_qualified_name_via_defn);
}

TEST(GetFullyQualifiedMatchFieldNameTest, ReturnsNotFoundForNonExistingTable) {
  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(SimpleP4Info()));
  EXPECT_THAT(GetFullyQualifiedMatchFieldName(
                  ir_p4info, "ingress.non_existing_table", "hex_key"),
              StatusIs(absl::StatusCode::kNotFound));
}

TEST(GetFullyQualifiedMatchFieldNameTest,
     ReturnsNotFoundForNonExistingMatchField) {
  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(SimpleP4Info()));
  EXPECT_THAT(GetFullyQualifiedMatchFieldName(ir_p4info, "ingress.simple_table",
                                              "non_existing_match_field"),
              StatusIs(absl::StatusCode::kNotFound));
}

TEST(GetFullyQualifiedMatchFieldNameViaDefinitionsTest,
     ReturnsNotFoundForMatchFieldInWrongTable) {
  ASSERT_OK_AND_ASSIGN(pdpi::IrP4Info ir_p4info,
                       pdpi::CreateIrP4Info(SimpleP4Info()));
  EXPECT_THAT(GetFullyQualifiedMatchFieldName(ir_p4info, "ingress.simple_table",
                                              "simple_hex_key"),
              StatusIs(absl::StatusCode::kNotFound));
}

TEST(GetFullyQualifiedMatchFieldNameViaDefinitionsTest,
     ReturnsNotFoundForInvalidInput) {
  EXPECT_THAT(GetFullyQualifiedMatchFieldName(pdpi::IrTableDefinition(),
                                              pdpi::IrMatchFieldDefinition()),
              StatusIs(absl::StatusCode::kNotFound));

  pdpi::IrTableDefinition table_def;
  table_def.mutable_preamble()->set_name("table");
  pdpi::IrMatchFieldDefinition match_field_def;
  match_field_def.mutable_match_field()->set_name("match_field");

  EXPECT_THAT(GetFullyQualifiedMatchFieldName(table_def, match_field_def),
              StatusIs(absl::StatusCode::kNotFound));
}

TEST(CreateTest, SucceedsOnFieldWithConstraintAndReference) {
  p4::config::v1::P4Info simple_p4info = SimpleP4Info();
  Table& simple_table = *simple_p4info.mutable_tables(0);
  simple_table.mutable_preamble()->add_annotations(
      R"(@entry_restriction("hex_key != 0"))");
  MatchField& hex_key = *simple_table.mutable_match_fields(0);
  hex_key.add_annotations(
      "@refers_to(builtin::multicast_group_table, multicast_group_id)");

  EXPECT_OK(FuzzerConfig::Create(simple_p4info, ConfigParams{}));
}

TEST(CreateTest,
     FailsOnExactP4RuntimeTranslationTypeWithConstraintUnlessIgnored) {
  p4::config::v1::P4Info simple_p4info = SimpleP4Info();
  Table& simple_table = *simple_p4info.mutable_tables(0);
  simple_table.mutable_preamble()->add_annotations(
      R"(@entry_restriction("string_key != 0"))");

  EXPECT_THAT(FuzzerConfig::Create(simple_p4info, ConfigParams{}),
              StatusIs(absl::StatusCode::kUnimplemented));

  EXPECT_OK(FuzzerConfig::Create(
      simple_p4info,
      ConfigParams{
          .ignore_constraints_on_tables = {"ingress.simple_table"},
      }));
}

TEST(CreateTest, SucceedsOnOptionalP4RuntimeTranslationTypeWithConstraint) {
  p4::config::v1::P4Info simple_p4info = SimpleP4Info();
  Table& simple_table = *simple_p4info.mutable_tables(0);
  simple_table.mutable_preamble()->add_annotations(
      R"(@entry_restriction("string_key != 0"))");
  MatchField& string_key = *simple_table.mutable_match_fields(1);
  string_key.set_match_type(MatchField::OPTIONAL);

  EXPECT_OK(FuzzerConfig::Create(simple_p4info, ConfigParams{}));
}

}  // namespace
}  // namespace p4_fuzzer
