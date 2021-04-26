#include "p4_fuzzer/fuzz_util.h"

#include <memory>

#include "absl/random/seed_sequences.h"
#include "absl/status/statusor.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/collections.h"
#include "gutil/proto.h"
#include "gutil/proto_matchers.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
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

absl::StatusOr<pdpi::IrP4Info> ConstructIrInfo(int max_group_size = 256) {
  auto p4info = gutil::ParseProtoOrDie<p4::config::v1::P4Info>(
      R"pb(
        tables {
          preamble {
            id: 200
            name: "ingress.routing.wcmp_group_table"
            alias: "wcmp_group_table"
            annotations: "@p4runtime_role(\"sdn_controller\")"
            annotations: "@oneshot"
          }
          match_fields { id: 1 name: "wcmp_group_id" match_type: EXACT }
          action_refs { id: 300 annotations: "@proto_id(1)" }
          action_refs {
            id: 301
            annotations: "@defaultonly"
            scope: DEFAULT_ONLY
          }
          const_default_action_id: 301
          implementation_id: 100
          size: 4096
        }
        actions { preamble { id: 301 name: "NoAction" alias: "NoAction" } }
        actions {
          preamble {
            id: 300
            name: "ingress.routing.set_nexthop_id"
            alias: "set_nexthop_id"
          }
          params { id: 1 name: "nexthop_id" }
        }
        action_profiles {
          preamble {
            id: 100
            name: "ingress.routing.wcmp_group_selector"
            alias: "wcmp_group_selector"
          }
          table_ids: 200
          with_selector: true
          size: 65536
        }
      )pb");
  p4info.mutable_action_profiles(0)->set_max_group_size(max_group_size);
  return pdpi::CreateIrP4Info(p4info);
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
// Action Set of acceptable weights and size.
TEST(FuzzUtilTest, FuzzActionProfileActionSetWithinParameters) {
  // Initialize required state.
  absl::BitGen gen;
  ASSERT_OK_AND_ASSIGN(const pdpi::IrP4Info ir_info, ConstructIrInfo());
  const SwitchState switch_state(ir_info);
  const FuzzerConfig config{
      .info = ir_info,
      .ports = {"1"},
      .qos_queues = {"0x1"},
      .role = "sdn_controller",
  };
  const pdpi::IrTableDefinition& table_definition =
      ir_info.tables_by_id().at(200);

  // Main logic.
  for (int i = 0; i < 1000; ++i) {
    auto action_profile_set = FuzzActionProfileActionSet(
        &gen, config, switch_state, table_definition);

    // Due to a bug in FuzzValue, FuzzActionProfileActionSet is currently flaky
    // and may require several attempts to succeed.
    // TODO: Remove once the bug is fixed.
    while (!action_profile_set.ok() ||
           action_profile_set->action_profile_actions_size() == 0) {
      action_profile_set = FuzzActionProfileActionSet(
          &gen, config, switch_state, table_definition);
    }

    // The number of actions should always be less than or equal to the max
    // cardinality.
    EXPECT_LE(action_profile_set->action_profile_actions_size(),
              kActionProfileActionSetMaxCardinality);

    int total_weight = 0;
    for (auto& action : action_profile_set->action_profile_actions()) {
      total_weight += action.weight();
    }
    EXPECT_LE(total_weight, kActionProfileActionSetMaxWeight);
  }
}

// TODO: When we use max_group_size:
// Test FuzzActionProfileActionSet with max weight set to 0 (correct action
// appears to be to either generate whatever we want, or do a binary search or
// something to determine a rough max weight for the switch).

// TODO: When we use max_group_size:
// Test that FuzzActionProfileActionSet correctly handles a request for too
// many actions with too low weight

}  // namespace
}  // namespace p4_fuzzer
