#include "p4_pdpi/ir_tools.h"

#include <vector>

#include "absl/container/flat_hash_set.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto.h"
#include "gutil/proto_matchers.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4/config/v1/p4types.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/pd.h"
#include "p4_pdpi/testing/main_p4_pd.pb.h"
#include "p4_pdpi/testing/test_p4info.h"

namespace pdpi {
namespace {

using ::gutil::EqualsProto;
using ::testing::UnorderedElementsAreArray;

absl::StatusOr<std::string> AddAnotherToString(absl::string_view initial) {
  return absl::StrCat("another_", initial);
}

// Rewrites a string (with named type `string_id_t`) in a single entry's match
// field.
TEST(TransformValuesOfTypeTest, RewriteMatchString) {
  const IrP4Info info = GetTestIrP4Info();
  p4::config::v1::P4NamedType target_type;
  target_type.set_name("string_id_t");

  ASSERT_OK_AND_ASSIGN(
      IrTableEntry original_entry,
      PdTableEntryToIr(info, gutil::ParseProtoOrDie<TableEntry>(R"pb(
                         referred_table_entry {
                           match { id: "string" }
                           action { do_thing_4 {} }
                         }
                       )pb")));

  ASSERT_OK_AND_ASSIGN(
      IrTableEntry goal_entry,
      PdTableEntryToIr(info, gutil::ParseProtoOrDie<TableEntry>(R"pb(
                         referred_table_entry {
                           match { id: "another_string" }
                           action { do_thing_4 {} }
                         }
                       )pb")));

  ASSERT_OK(TransformValuesOfType(info, target_type, original_entry,
                                  /*transformer=*/AddAnotherToString));
  EXPECT_THAT(original_entry, EqualsProto(goal_entry));
}

// Rewrites strings (with named type `string_id_t`) in a single entry's action
// parameters.
TEST(TransformValuesOfTypeTest, RewriteActionStrings) {
  const IrP4Info info = GetTestIrP4Info();
  p4::config::v1::P4NamedType target_type;
  target_type.set_name("string_id_t");

  ASSERT_OK_AND_ASSIGN(
      IrTableEntry original_entry,
      PdTableEntryToIr(info, gutil::ParseProtoOrDie<TableEntry>(R"pb(
                         referring_table_entry {
                           match { val: "0x001" }
                           action {
                             referring_action {
                               referring_id_1: "string1",
                               referring_id_2: "string2",
                             }
                           }
                         }
                       )pb")));

  ASSERT_OK_AND_ASSIGN(
      IrTableEntry goal_entry,
      PdTableEntryToIr(info, gutil::ParseProtoOrDie<TableEntry>(R"pb(
                         referring_table_entry {
                           match { val: "0x001" }
                           action {
                             referring_action {
                               referring_id_1: "another_string1",
                               referring_id_2: "another_string2",
                             }
                           }
                         }
                       )pb")));

  ASSERT_OK(TransformValuesOfType(info, target_type, original_entry,
                                  /*transformer=*/AddAnotherToString));
  EXPECT_THAT(original_entry, EqualsProto(goal_entry));
}

// Collects all the strings (with named type `string_id_t`) in a list of
// entries' match fields and action parameters.
TEST(VisitValuesOfTypeTest, CollectStrings) {
  const IrP4Info info = GetTestIrP4Info();
  p4::config::v1::P4NamedType target_type;
  target_type.set_name("string_id_t");

  ASSERT_OK_AND_ASSIGN(
      IrTableEntry entry1,
      PdTableEntryToIr(info, gutil::ParseProtoOrDie<TableEntry>(R"pb(
                         referred_table_entry {
                           match { id: "string1" }
                           action { do_thing_4 {} }
                         }
                       )pb")));
  ASSERT_OK_AND_ASSIGN(
      IrTableEntry entry2,
      PdTableEntryToIr(info, gutil::ParseProtoOrDie<TableEntry>(R"pb(
                         referring_table_entry {
                           match { val: "0x001" }
                           action {
                             referring_action {
                               referring_id_1: "string2",
                               referring_id_2: "string3",
                             }
                           }
                         }
                       )pb")));

  std::vector<IrTableEntry> entries{entry1, entry2};
  absl::flat_hash_set<std::string> string_collection;

  ASSERT_OK(VisitValuesOfType(info, target_type, entries,
                              /*visitor=*/[&](absl::string_view input) {
                                string_collection.insert(std::string(input));
                                return absl::OkStatus();
                              }));

  EXPECT_THAT(string_collection,
              UnorderedElementsAreArray({"string1", "string2", "string3"}));
}

}  // namespace
}  // namespace pdpi
