#include "p4_fuzzer/fuzz_util.h"

#include <memory>
#include <string>

#include "absl/random/distributions.h"
#include "absl/random/seed_sequences.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/collections.h"
#include "gutil/proto.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_fuzzer/fuzzer.pb.h"
#include "p4_fuzzer/mutation.h"
#include "p4_fuzzer/test_utils.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/pd.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace p4_fuzzer {
namespace {

using ::gutil::EqualsProto;

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

TEST(FuzzUtilTest, FuzzWriteRequestAreReproducible) {
  ASSERT_OK_AND_ASSIGN(const FuzzerTestState fuzzer_state,
                       ConstructFuzzerTestState(TestP4InfoOptions()));

  // Use the same sequence seed for both generators.
  absl::SeedSeq seed;
  absl::BitGen gen_0(seed);
  absl::BitGen gen_1(seed);

  // Create 20 instances (of, in expectation, ~50 updates each), and verify that
  // they are identical.
  for (int i = 0; i < 20; ++i) {
    ASSERT_THAT(FuzzWriteRequest(&gen_0, fuzzer_state.config,
                                 fuzzer_state.switch_state),
                EqualsProto(FuzzWriteRequest(&gen_1, fuzzer_state.config,
                                             fuzzer_state.switch_state)));
  }
}

// Test that FuzzActionProfileActionSet correctly generates an ActionProfile
// Action Set of acceptable weights and size (derived from max_group_size and
// kActionProfileActionSetMaxCardinality).
TEST(FuzzActionProfileActionSetTest,
     StaysWithinMaxGroupSizeAndCardinalityParameters) {
  absl::BitGen gen;
  for (int i = 0; i < 1000; ++i) {
    // Tests a broad enough band of max weights to give us interesting coverage
    // while being narrow enough to likely catch issues when they happen.
    int max_group_size =
        absl::Uniform<int>(gen, kActionProfileActionSetMaxCardinality, 10000);
    auto options =
        TestP4InfoOptions{.action_profile_max_group_size = max_group_size};
    ASSERT_OK_AND_ASSIGN(FuzzerTestState fuzzer_state,
                         ConstructFuzzerTestState(options));
    const pdpi::IrTableDefinition& table_definition =
        fuzzer_state.config.info.tables_by_id().at(
            options.action_selector_table_id);

    // Fuzz an ActionProfileActionSet.
    ASSERT_OK_AND_ASSIGN(auto action_profile_set,
                         FuzzActionProfileActionSet(
                             &fuzzer_state.gen, fuzzer_state.config,
                             fuzzer_state.switch_state, table_definition));

    // The number of actions should always be less than or equal to the max
    // cardinality.
    EXPECT_LE(action_profile_set.action_profile_actions_size(),
              kActionProfileActionSetMaxCardinality);

    int total_weight = 0;
    for (auto& action : action_profile_set.action_profile_actions()) {
      total_weight += action.weight();
    }
    EXPECT_LE(total_weight, max_group_size);
  }
}

// Test that FuzzActionProfileActionSet correctly generates an ActionProfile
// Action Set of acceptable weights and size when max_group_size is set to 0.
TEST(FuzzActionProfileActionSetTest, HandlesZeroMaxGroupSizeCorrectly) {
  auto options = TestP4InfoOptions{.action_profile_max_group_size = 0};
  for (int i = 0; i < 1000; ++i) {
    ASSERT_OK_AND_ASSIGN(FuzzerTestState fuzzer_state,
                         ConstructFuzzerTestState(options));
    const pdpi::IrTableDefinition& table_definition =
        fuzzer_state.config.info.tables_by_id().at(
            options.action_selector_table_id);

    // Fuzz an ActionProfileActionSet.
    ASSERT_OK_AND_ASSIGN(auto action_profile_set,
                         FuzzActionProfileActionSet(
                             &fuzzer_state.gen, fuzzer_state.config,
                             fuzzer_state.switch_state, table_definition));

    // The number of actions should always be less than or equal to the max
    // cardinality.
    EXPECT_LE(action_profile_set.action_profile_actions_size(),
              kActionProfileActionSetMaxCardinality);

    int total_weight = 0;
    for (auto& action : action_profile_set.action_profile_actions()) {
      total_weight += action.weight();
    }
    // When max_group_size is set to 0, size is the upperbound for weight.
    EXPECT_LE(total_weight, options.action_profile_size);
  }
}

// Test that FuzzActionProfileActionSet correctly handles a request with low max
// group size (in particular, lower than the max number of actions).
TEST(FuzzActionProfileActionSetTest, HandlesLowMaxGroupSizeCorrectly) {
  absl::BitGen gen;
  for (int i = 0; i < 1000; ++i) {
    // Set up.
    int max_group_size =
        absl::Uniform<int>(gen, 1, kActionProfileActionSetMaxCardinality);
    auto options =
        TestP4InfoOptions{.action_profile_max_group_size = max_group_size};
    ASSERT_OK_AND_ASSIGN(FuzzerTestState fuzzer_state,
                         ConstructFuzzerTestState(options));
    const pdpi::IrTableDefinition& table_definition =
        fuzzer_state.config.info.tables_by_id().at(
            options.action_selector_table_id);

    ASSERT_OK_AND_ASSIGN(auto action_profile_set,
                         FuzzActionProfileActionSet(
                             &fuzzer_state.gen, fuzzer_state.config,
                             fuzzer_state.switch_state, table_definition));

    // The number of actions must be less than max_group_size since every
    // action has at least weight 1.
    EXPECT_LE(action_profile_set.action_profile_actions_size(), max_group_size);

    int total_weight = 0;
    for (auto& action : action_profile_set.action_profile_actions()) {
      total_weight += action.weight();
    }
    EXPECT_LE(total_weight, max_group_size);
  }
}

// TODO: Add a direct test for FuzzValue that either sometimes
// generates something for non-standard match fields, or, if that is never
// correct, makes sure it still works with that possibility removed.

}  // namespace
}  // namespace p4_fuzzer
