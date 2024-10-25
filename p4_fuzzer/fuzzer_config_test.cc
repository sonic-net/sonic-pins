#include "p4_fuzzer/fuzzer_config.h"

#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "gutils/parse_text_proto.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/ir.pb.h"

namespace p4_fuzzer {
namespace {

using gutil::StatusIs;
using gutils::ParseTextProtoOrDie;
using p4::config::v1::MatchField;
using p4::config::v1::P4Info;
using p4::config::v1::Table;

// TODO: b/324078937 - Remove once a nicer way to build custom p4infos exists.
// A P4info that contains a single table with 2 keys:
//  1) EXACT key with bitstring<16> type (HEX_STRING format)
//  2) EXACT key with P4Runtime translated type (STRING format)
p4::config::v1::P4Info SimpleP4Info() {
  return ParseTextProtoOrDie<P4Info>(
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
