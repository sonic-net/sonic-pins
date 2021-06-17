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
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/pd.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace p4_fuzzer {
namespace {

using ::gutil::EqualsProto;

// Table, table actions, and corresponding action profile IDs.
constexpr int kTableId = 100;
constexpr int kActionId = 200;
constexpr int kActionNoOpId = 201;
constexpr int kActionProfileId = 300;
constexpr int kActionProfileSize = 65536;

absl::StatusOr<pdpi::IrP4Info> ConstructIrInfo(int max_group_size = 256) {
  auto p4info = gutil::ParseProtoOrDie<p4::config::v1::P4Info>(
      R"pb(
        tables {
          preamble {
            # id : kTableId
            name: "ingress.routing.wcmp_group_table"
            alias: "wcmp_group_table"
            annotations: "@p4runtime_role(\"sdn_controller\")"
            annotations: "@oneshot"
          }
          match_fields { id: 1 name: "wcmp_group_id" match_type: EXACT }
          action_refs {
            # id: kActionId
            annotations: "@proto_id(1)"
          }
          action_refs {
            # id: kActionNoOpId
            annotations: "@defaultonly"
            scope: DEFAULT_ONLY
          }
          # const_default_action_id: kActionNoOpId
          # implementation_id: kActionProfileId
          size: 4096
        }
        actions {
          preamble {
            # id: kActionId
            name: "ingress.routing.set_nexthop_id"
            alias: "set_nexthop_id"
          }
          params { id: 1 name: "nexthop_id" }
        }
        actions {
          preamble {
            # id: kActionNoOpId
            name: "NoAction"
            alias: "NoAction"
          }
        }
        action_profiles {
          preamble {
            # id: kActionProfileId
            name: "ingress.routing.wcmp_group_selector"
            alias: "wcmp_group_selector"
          }
          # table_ids: kTableId
          with_selector: true
          # size: kActionProfileSize
        }
      )pb");
  // Set up table, action, and action profile Ids appropriately.
  p4info.mutable_tables(0)->mutable_preamble()->set_id(kTableId);
  p4info.mutable_tables(0)->mutable_action_refs(0)->set_id(kActionId);
  p4info.mutable_tables(0)->mutable_action_refs(1)->set_id(kActionNoOpId);
  p4info.mutable_tables(0)->set_const_default_action_id(kActionNoOpId);
  p4info.mutable_tables(0)->set_implementation_id(kActionProfileId);
  p4info.mutable_actions(0)->mutable_preamble()->set_id(kActionId);
  p4info.mutable_actions(1)->mutable_preamble()->set_id(kActionNoOpId);
  p4info.mutable_action_profiles(0)->mutable_preamble()->set_id(
      kActionProfileId);
  p4info.mutable_action_profiles(0)->add_table_ids(kTableId);
  p4info.mutable_action_profiles(0)->set_size(kActionProfileSize);

  if (max_group_size != 0) {
    p4info.mutable_action_profiles(0)->set_max_group_size(max_group_size);
  }
  return pdpi::CreateIrP4Info(p4info);
}

absl::StatusOr<p4::v1::ActionProfileActionSet>
FuzzActionProfileActionSetForHardcodedConfig(int max_group_size = 256) {
  // Initialize required state.
  absl::BitGen gen;
  ASSIGN_OR_RETURN(const pdpi::IrP4Info ir_info,
                   ConstructIrInfo(max_group_size));
  const SwitchState switch_state(ir_info);
  const FuzzerConfig config{
      .info = ir_info,
      .ports = {"1"},
      .qos_queues = {"0x1"},
      .role = "sdn_controller",
  };
  const pdpi::IrTableDefinition& table_definition =
      ir_info.tables_by_id().at(kTableId);

  // Get an ActionProfileActionSet.
  auto action_profile_set =
      FuzzActionProfileActionSet(&gen, config, switch_state, table_definition);
  // Due to a bug in FuzzValue, FuzzActionProfileActionSet is currently flaky
  // and may require several attempts to succeed.
  // TODO: Remove once the bug is fixed.
  while (!action_profile_set.ok()) {
    action_profile_set = FuzzActionProfileActionSet(&gen, config, switch_state,
                                                    table_definition);
  }
  return action_profile_set;
}

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
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_info, ConstructIrInfo());
  const SwitchState switch_state(ir_info);
  const FuzzerConfig config{
      .info = ir_info,
      .ports = {"1"},
      .qos_queues = {"0x1"},
      .role = "sdn_controller",
  };

  // Use the same sequence seed for both generators.
  absl::SeedSeq seed;
  absl::BitGen gen_0(seed);
  absl::BitGen gen_1(seed);

  // Create 1000 instances, and verify that they are identical.
  for (int i = 0; i < 1000; ++i) {
    ASSERT_THAT(FuzzWriteRequest(&gen_0, config, switch_state),
                EqualsProto(FuzzWriteRequest(&gen_1, config, switch_state)));
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
    ASSERT_OK_AND_ASSIGN(
        auto action_profile_set,
        FuzzActionProfileActionSetForHardcodedConfig(max_group_size));

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
  for (int i = 0; i < 1000; ++i) {
    ASSERT_OK_AND_ASSIGN(
        auto action_profile_set,
        FuzzActionProfileActionSetForHardcodedConfig(/*max_group_size=*/0));

    // The number of actions should always be less than or equal to the max
    // cardinality.
    EXPECT_LE(action_profile_set.action_profile_actions_size(),
              kActionProfileActionSetMaxCardinality);

    int total_weight = 0;
    for (auto& action : action_profile_set.action_profile_actions()) {
      total_weight += action.weight();
    }
    EXPECT_LE(total_weight, kActionProfileSize);
  }
}

// Test that FuzzActionProfileActionSet correctly handles a request with low max
// group size (in particular, lower than the max number of actions).
TEST(FuzzActionProfileActionSetTest, HandlesLowMaxGroupSizeCorrectly) {
  absl::BitGen gen;
  for (int i = 0; i < 1000; ++i) {
    int max_group_size =
        absl::Uniform<int>(gen, 1, kActionProfileActionSetMaxCardinality);

    ASSERT_OK_AND_ASSIGN(
        auto action_profile_set,
        FuzzActionProfileActionSetForHardcodedConfig(max_group_size));
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
