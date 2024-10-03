// Copyright 2021 Google LLC
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
#include "p4_fuzzer/fuzz_util.h"

#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "absl/container/flat_hash_set.h"
#include "absl/random/distributions.h"
#include "absl/random/random.h"
#include "absl/random/seed_sequences.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_split.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/collections.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_fuzzer/fuzzer.pb.h"
#include "p4_fuzzer/test_utils.h"
#include "p4_pdpi/ir.pb.h"

namespace p4_fuzzer {
namespace {

using ::gutil::EqualsProto;
using ::testing::AnyOfArray;
using ::testing::Not;

TEST(FuzzUtilTest, SetUnusedBitsToZeroInThreeBytes) {
  std::string data("\xff\xff\xff", 3);
  EXPECT_EQ(SetUnusedBitsToZero(24, data), std::string("\xff\xff\xff", 3));
  EXPECT_EQ(SetUnusedBitsToZero(23, data), std::string("\x7f\xff\xff", 3));
  EXPECT_EQ(SetUnusedBitsToZero(22, data), std::string("\x3f\xff\xff", 3));
  EXPECT_EQ(SetUnusedBitsToZero(21, data), std::string("\x1f\xff\xff", 3));
  EXPECT_EQ(SetUnusedBitsToZero(20, data), std::string("\x0f\xff\xff", 3));
  EXPECT_EQ(SetUnusedBitsToZero(16, data), std::string("\x00\xff\xff", 3));
  EXPECT_EQ(SetUnusedBitsToZero(15, data), std::string("\x00\x7f\xff", 3));
  EXPECT_EQ(SetUnusedBitsToZero(14, data), std::string("\x00\x3f\xff", 3));
  EXPECT_EQ(SetUnusedBitsToZero(13, data), std::string("\x00\x1f\xff", 3));
  EXPECT_EQ(SetUnusedBitsToZero(12, data), std::string("\x00\x0f\xff", 3));
  EXPECT_EQ(SetUnusedBitsToZero(3, data), std::string("\x00\x00\x07", 3));
  EXPECT_EQ(SetUnusedBitsToZero(2, data), std::string("\x00\x00\x03", 3));
  EXPECT_EQ(SetUnusedBitsToZero(1, data), std::string("\x00\x00\x01", 3));
  EXPECT_EQ(SetUnusedBitsToZero(0, data), std::string("\x00\x00\x00", 3));
}

TEST(FuzzUtilTest, SetUnusedBitsToZeroInNineBytes) {
  std::string data("\xff\xff\xff\xff\xff\xff\xff\xff\xff", 9);
  EXPECT_EQ(SetUnusedBitsToZero(72, data),
            std::string("\xff\xff\xff\xff\xff\xff\xff\xff\xff", 9));
  EXPECT_EQ(SetUnusedBitsToZero(71, data),
            std::string("\x7f\xff\xff\xff\xff\xff\xff\xff\xff", 9));
  EXPECT_EQ(SetUnusedBitsToZero(65, data),
            std::string("\x01\xff\xff\xff\xff\xff\xff\xff\xff", 9));
  EXPECT_EQ(SetUnusedBitsToZero(64, data),
            std::string("\x00\xff\xff\xff\xff\xff\xff\xff\xff", 9));
  EXPECT_EQ(SetUnusedBitsToZero(63, data),
            std::string("\x00\x7f\xff\xff\xff\xff\xff\xff\xff", 9));
  EXPECT_EQ(SetUnusedBitsToZero(33, data),
            std::string("\x00\x00\x00\x00\x01\xff\xff\xff\xff", 9));
  EXPECT_EQ(SetUnusedBitsToZero(32, data),
            std::string("\x00\x00\x00\x00\x00\xff\xff\xff\xff", 9));
  EXPECT_EQ(SetUnusedBitsToZero(31, data),
            std::string("\x00\x00\x00\x00\x00\x7f\xff\xff\xff", 9));
  EXPECT_EQ(SetUnusedBitsToZero(9, data),
            std::string("\x00\x00\x00\x00\x00\x00\x00\x01\xff", 9));
  EXPECT_EQ(SetUnusedBitsToZero(8, data),
            std::string("\x00\x00\x00\x00\x00\x00\x00\x00\xff", 9));
  EXPECT_EQ(SetUnusedBitsToZero(7, data),
            std::string("\x00\x00\x00\x00\x00\x00\x00\x00\x7f", 9));
  EXPECT_EQ(SetUnusedBitsToZero(0, data),
            std::string("\x00\x00\x00\x00\x00\x00\x00\x00\x00", 9));
}

TEST(FuzzUtilTest, ZeroNLeastSignificantBits) {
  std::string data("\xff\xff\xff", 3);
  EXPECT_EQ(ZeroNLeastSignificantBits(0, data), std::string("\xff\xff\xff", 3));
  EXPECT_EQ(ZeroNLeastSignificantBits(1, data), std::string("\xff\xff\xfe", 3));
  EXPECT_EQ(ZeroNLeastSignificantBits(4, data), std::string("\xff\xff\xf0", 3));
  EXPECT_EQ(ZeroNLeastSignificantBits(8, data), std::string("\xff\xff\x00", 3));
  EXPECT_EQ(ZeroNLeastSignificantBits(9, data), std::string("\xff\xfe\x00", 3));
  EXPECT_EQ(ZeroNLeastSignificantBits(16, data),
            std::string("\xff\x00\x00", 3));
  EXPECT_EQ(ZeroNLeastSignificantBits(24, data),
            std::string("\x00\x00\x00", 3));
}

TEST(FuzzUtilTest, BitsToUint64) {
  EXPECT_EQ(BitsToUint64(std::string("\0\0\0\0\0\0\0\x63", 8)), 0x63);
  EXPECT_EQ(BitsToUint64(std::string("\0\0\0\0\0\0\x30\x63", 8)), 0x3063);
  EXPECT_EQ(BitsToUint64(std::string("\x01\x02\x03\x04\x05\x06\x07\x08", 8)),
            0x0102030405060708);
}

TEST(FuzzUtilTest, FuzzBitsStringSize) {
  struct TestCase {
    int bits;
    int bytes;
  } test_cases[] = {{1, 1},  {5, 1},  {7, 1},  {8, 1},    {9, 2},
                    {10, 2}, {16, 2}, {17, 3}, {128, 16}, {129, 17}};

  absl::BitGen gen;
  for (auto test_case : test_cases) {
    std::string data = FuzzBits(&gen, test_case.bits);
    EXPECT_EQ(data.size(), test_case.bytes)
        << "bits: " << test_case.bits << " data: '" << data << "'";
  }
}

TEST(FuzzUtilTest, FuzzBitsStringPaddingWorks) {
  absl::BitGen gen;
  for (int i = 0; i < 100; ++i) {
    std::string data = FuzzBits(&gen, /*bits=*/3);
    ASSERT_EQ(data.size(), 1);
    EXPECT_EQ(data[0] & 0xf8, 0);
  }
}

TEST(FuzzUtilTest, FuzzUint64SmallInRange) {
  absl::BitGen gen;
  for (int i = 0; i < 10; ++i) {
    EXPECT_LE(FuzzUint64(&gen, /*bits=*/1), 1);
  }
}

TEST(FuzzUtilTest, FuzzUint64LargeInRange) {
  absl::BitGen gen;
  for (int i = 0; i < 10000; ++i) {
    EXPECT_LT(FuzzUint64(&gen, /*bits=*/10), 1024);
  }
}

// Test that FuzzActionProfileActionSet correctly generates an ActionProfile
// Action Set of acceptable weights and size (derived from max_group_size and
// kActionProfileActionSetMaxCardinality).
TEST(FuzzActionProfileActionSetTest,
     StaysWithinMaxGroupSizeAndCardinalityParameters) {
  // As implied by the name, 1000 is basically arbitrarily chosen and anything
  // above that would be just as good. Lower is probably worse though.
  const int kGroupSizeArbitraryUpperBound = 1000;
  FuzzerTestState fuzzer_state = ConstructStandardFuzzerTestState();
  ASSERT_OK_AND_ASSIGN(const pdpi::IrTableDefinition& table_definition,
                       GetAOneShotTableDefinition(fuzzer_state.config.info));
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrActionProfileDefinition action_profile_definition,
      GetActionProfileImplementingTable(fuzzer_state.config.info,
                                        table_definition));
  for (int i = 0; i < 1000; ++i) {
    // Tests a broad enough band of max weights to give us interesting
    // coverage while being narrow enough to likely catch issues when they
    // happen.
    int max_group_size = absl::Uniform<int>(
        fuzzer_state.gen, kActionProfileActionSetMaxCardinality,
        kGroupSizeArbitraryUpperBound);

    SetMaxGroupSizeInActionProfile(fuzzer_state.config.info,
                                   action_profile_definition, max_group_size);

    // Fuzz an ActionProfileActionSet.
    ASSERT_OK_AND_ASSIGN(auto action_profile_action_set,
                         FuzzActionProfileActionSet(
                             &fuzzer_state.gen, fuzzer_state.config,
                             fuzzer_state.switch_state, table_definition));

    // The number of actions should always be less than or equal to the max
    // cardinality.
    EXPECT_LE(action_profile_action_set.action_profile_actions_size(),
              kActionProfileActionSetMaxCardinality);

    int total_weight = 0;
    for (auto& action : action_profile_action_set.action_profile_actions()) {
      total_weight += action.weight();
    }
    EXPECT_LE(total_weight, max_group_size);
  }
}

// Test that FuzzActionProfileActionSet correctly generates an ActionProfile
// Action Set of acceptable weights and size when max_group_size is set to 0.
TEST(FuzzActionProfileActionSetTest, HandlesZeroMaxGroupSizeCorrectly) {
  FuzzerTestState fuzzer_state = ConstructStandardFuzzerTestState();
  ASSERT_OK_AND_ASSIGN(const pdpi::IrTableDefinition& table_definition,
                       GetAOneShotTableDefinition(fuzzer_state.config.info));
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrActionProfileDefinition action_profile_definition,
      GetActionProfileImplementingTable(fuzzer_state.config.info,
                                        table_definition));
  SetMaxGroupSizeInActionProfile(fuzzer_state.config.info,
                                 action_profile_definition,
                                 /*max_group_size=*/0);
  for (int i = 0; i < 1000; ++i) {
    // Fuzz an ActionProfileActionSet.
    ASSERT_OK_AND_ASSIGN(auto action_profile_action_set,
                         FuzzActionProfileActionSet(
                             &fuzzer_state.gen, fuzzer_state.config,
                             fuzzer_state.switch_state, table_definition));

    // The number of actions should always be less than or equal to the max
    // cardinality.
    EXPECT_LE(action_profile_action_set.action_profile_actions_size(),
              kActionProfileActionSetMaxCardinality);

    int total_weight = 0;
    for (auto& action : action_profile_action_set.action_profile_actions()) {
      total_weight += action.weight();
    }
    // When max_group_size is set to 0, size is the upperbound for weight.
    EXPECT_LE(total_weight, action_profile_definition.action_profile().size());
  }
}

// Test that FuzzActionProfileActionSet correctly handles a request with low
// max group size (in particular, lower than the max number of actions).
TEST(FuzzActionProfileActionSetTest, HandlesLowMaxGroupSizeCorrectly) {
  FuzzerTestState fuzzer_state = ConstructStandardFuzzerTestState();
  ASSERT_OK_AND_ASSIGN(const pdpi::IrTableDefinition& table_definition,
                       GetAOneShotTableDefinition(fuzzer_state.config.info));
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrActionProfileDefinition action_profile_definition,
      GetActionProfileImplementingTable(fuzzer_state.config.info,
                                        table_definition));
  for (int i = 0; i < 1000; ++i) {
    // Set up.
    const int max_group_size = absl::Uniform<int>(
        fuzzer_state.gen, 1, kActionProfileActionSetMaxCardinality);

    SetMaxGroupSizeInActionProfile(fuzzer_state.config.info,
                                   action_profile_definition, max_group_size);

    ASSERT_OK_AND_ASSIGN(auto action_profile_action_set,
                         FuzzActionProfileActionSet(
                             &fuzzer_state.gen, fuzzer_state.config,
                             fuzzer_state.switch_state, table_definition));

    // The number of actions must be less than max_group_size since every
    // action has at least weight 1.
    EXPECT_LE(action_profile_action_set.action_profile_actions_size(),
              max_group_size);

    int total_weight = 0;
    for (auto& action : action_profile_action_set.action_profile_actions()) {
      total_weight += action.weight();
    }
    EXPECT_LE(total_weight, max_group_size);
  }
}

TEST(FuzzUtilTest, FuzzWriteRequestRespectMaxBatchSize) {
  FuzzerTestState fuzzer_state = ConstructStandardFuzzerTestState();

  // Create 200 instances of, in expectation, ~50 updates each without the
  // max_batch_size parameter and verify that they all have batches smaller
  // than max_batch_size.
  for (int i = 0; i < 200; ++i) {
    int max_batch_size = absl::Uniform<int>(fuzzer_state.gen, 0, 50);
    EXPECT_LE(FuzzWriteRequest(&fuzzer_state.gen, fuzzer_state.config,
                               fuzzer_state.switch_state, max_batch_size)
                  .updates_size(),
              max_batch_size)
        << absl::StrCat(" using max_batch_size=", max_batch_size);
  }
}

TEST(FuzzUtilTest, FuzzWriteRequestRespectsDisallowList) {
  FuzzerTestState fuzzer_state = ConstructStandardFuzzerTestState();
  fuzzer_state.config.disabled_fully_qualified_names = {
      "ingress.id_test_table", "ingress.exact_table", "ingress.ternary_table"};

  absl::flat_hash_set<uint32_t> disallowed_ids;
  for (const auto& path : fuzzer_state.config.disabled_fully_qualified_names) {
    std::vector<std::string> parts = absl::StrSplit(path, '.');
    ASSERT_OK_AND_ASSIGN(
        const pdpi::IrTableDefinition& table,
        gutil::FindOrStatus(fuzzer_state.config.info.tables_by_name(),
                            parts[parts.size() - 1]));
    disallowed_ids.insert(table.preamble().id());
  }

  for (int i = 0; i < 1000; i++) {
    AnnotatedWriteRequest request =
        FuzzWriteRequest(&fuzzer_state.gen, fuzzer_state.config,
                         fuzzer_state.switch_state, /*max_batch_size=*/1);
    if (request.updates_size() > 0) {
      EXPECT_THAT(request.updates(0).pi().entity().table_entry().table_id(),
                  Not(AnyOfArray(disallowed_ids)));
    }
  }
}

TEST(FuzzUtilTest, FuzzValidTableEntryRespectsDisallowList) {
  FuzzerTestState fuzzer_state = ConstructStandardFuzzerTestState();
  fuzzer_state.config.disabled_fully_qualified_names = {
      "ingress.ternary_table.ipv6_upper_64_bits",
      "ingress.ternary_table.normal",
      "ingress.ternary_table.mac",
      "ingress.ternary_table.unsupported_field",
  };

  ASSERT_OK_AND_ASSIGN(
      const pdpi::IrTableDefinition& ternary_table,
      gutil::FindOrStatus(fuzzer_state.config.info.tables_by_name(),
                          "ternary_table"));

  absl::flat_hash_set<uint32_t> disallowed_ids;
  for (const auto& path : fuzzer_state.config.disabled_fully_qualified_names) {
    std::vector<std::string> parts = absl::StrSplit(path, '.');
    ASSERT_OK_AND_ASSIGN(
        const pdpi::IrMatchFieldDefinition& match,
        gutil::FindOrStatus(ternary_table.match_fields_by_name(),
                            parts[parts.size() - 1]));
    disallowed_ids.insert(match.match_field().id());
  }

  for (int i = 0; i < 1000; i++) {
    ASSERT_OK_AND_ASSIGN(
        p4::v1::TableEntry entry,
        FuzzValidTableEntry(&fuzzer_state.gen, fuzzer_state.config,
                            fuzzer_state.switch_state,
                            ternary_table.preamble().id()));
    for (const auto& match : entry.match()) {
      EXPECT_THAT(match.field_id(), Not(AnyOfArray(disallowed_ids)));
    }
  }
}

TEST(FuzzUtilTest, FuzzActionRespectsDisallowList) {
  FuzzerTestState fuzzer_state = ConstructStandardFuzzerTestState();
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrActionDefinition do_thing_action,
      gutil::FindOrStatus(fuzzer_state.config.info.actions_by_name(),
                          "do_thing_1"));
  fuzzer_state.config.disabled_fully_qualified_names = {
      do_thing_action.preamble().name()};

  ASSERT_OK_AND_ASSIGN(
      const pdpi::IrTableDefinition& id_test_table,
      gutil::FindOrStatus(fuzzer_state.config.info.tables_by_name(),
                          "id_test_table"));

  for (int i = 0; i < 1000; i++) {
    ASSERT_OK_AND_ASSIGN(p4::v1::TableAction action,
                         FuzzAction(&fuzzer_state.gen, fuzzer_state.config,
                                    fuzzer_state.switch_state, id_test_table));
    EXPECT_NE(action.action().action_id(), do_thing_action.preamble().id());
  }
}

// TODO: Add a direct test for FuzzValue that either sometimes
// generates something for non-standard match fields, or, if that is never
// correct, makes sure it still works with that possibility removed.

}  // namespace
}  // namespace p4_fuzzer
