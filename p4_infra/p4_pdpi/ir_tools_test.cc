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

#include "p4_infra/p4_pdpi/ir_tools.h"

#include <vector>

#include "absl/container/flat_hash_set.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "p4/config/v1/p4types.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/pd.h"
#include "p4_infra/p4_pdpi/testing/main_p4_pd.pb.h"
#include "p4_infra/p4_pdpi/testing/test_p4info.h"

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

  ASSERT_OK_AND_ASSIGN(IrTableEntry original_entry,
                       PartialPdTableEntryToIrTableEntry(
                           info, gutil::ParseProtoOrDie<TableEntry>(R"pb(
                             one_match_field_table_entry {
                               match { id: "string" }
                               action { do_thing_4 {} }
                             }
                           )pb")));

  ASSERT_OK_AND_ASSIGN(IrTableEntry goal_entry,
                       PartialPdTableEntryToIrTableEntry(
                           info, gutil::ParseProtoOrDie<TableEntry>(R"pb(
                             one_match_field_table_entry {
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

  ASSERT_OK_AND_ASSIGN(IrTableEntry original_entry,
                       PartialPdTableEntryToIrTableEntry(
                           info, gutil::ParseProtoOrDie<TableEntry>(R"pb(
                             referring_by_action_table_entry {
                               match { val: "0x001" }
                               action {
                                 referring_to_two_match_fields_action {
                                   referring_id_1: "string1",
                                   referring_id_2: "0x004",
                                 }
                               }
                             }
                           )pb")));

  ASSERT_OK_AND_ASSIGN(IrTableEntry goal_entry,
                       PartialPdTableEntryToIrTableEntry(
                           info, gutil::ParseProtoOrDie<TableEntry>(R"pb(
                             referring_by_action_table_entry {
                               match { val: "0x001" }
                               action {
                                 referring_to_two_match_fields_action {
                                   referring_id_1: "another_string1",
                                   referring_id_2: "0x004",
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

  ASSERT_OK_AND_ASSIGN(IrTableEntry entry1,
                       PartialPdTableEntryToIrTableEntry(
                           info, gutil::ParseProtoOrDie<TableEntry>(R"pb(
                             one_match_field_table_entry {
                               match { id: "string1" }
                               action { do_thing_4 {} }
                             }
                           )pb")));
  ASSERT_OK_AND_ASSIGN(IrTableEntry entry2,
                       PartialPdTableEntryToIrTableEntry(
                           info, gutil::ParseProtoOrDie<TableEntry>(R"pb(
                             referring_by_action_table_entry {
                               match { val: "0x001" }
                               action {
                                 referring_to_two_match_fields_action {
                                   referring_id_1: "string2",
                                   referring_id_2: "0x003",
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

  EXPECT_THAT(string_collection, UnorderedElementsAreArray({
                                     "string1",
                                     "string2",
                                 }));
}

}  // namespace
}  // namespace pdpi
