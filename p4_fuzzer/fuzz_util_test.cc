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
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_fuzzer/fuzzer.pb.h"
#include "p4_fuzzer/fuzzer_config.h"
#include "p4_fuzzer/test_utils.h"
#include "p4_infra/p4_pdpi/built_ins.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/test_p4info.h"

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
    ASSERT_OK_AND_ASSIGN(std::string data, FuzzBits(&gen, test_case.bits));
    EXPECT_EQ(data.size(), test_case.bytes)
        << "bits: " << test_case.bits << " data: '" << data << "'";
  }
}

TEST(FuzzUtilTest, FuzzBitsStringPaddingWorks) {
  absl::BitGen gen;
  for (int i = 0; i < 100; ++i) {
    ASSERT_OK_AND_ASSIGN(std::string data, FuzzBits(&gen, /*bits=*/3));
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
  FuzzerTestState fuzzer_state = ConstructStandardFuzzerTestState();
  // Ensure multicast entries can be fuzzed.
  fuzzer_state.config.SetFuzzMulticastGroupEntryProbability(0.1);

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

TEST(FuzzUtilTest, FuzzWriteRequestAreReproducibleWithState) {
  FuzzerTestState fuzzer_state = ConstructStandardFuzzerTestState();
  // Ensure multicast entries can be fuzzed.
  fuzzer_state.config.SetFuzzMulticastGroupEntryProbability(0.1);

  absl::BitGen init_gen;
  // Generate some random table entries:
  for (int i = 0; i < 10; ++i) {
    auto request = FuzzWriteRequest(&init_gen, fuzzer_state.config,
                                    fuzzer_state.switch_state);
    for (auto update : request.updates()) {
      // If an update is not successfully added to the state, we ignore it.
      fuzzer_state.switch_state.ApplyUpdate(update.pi()).IgnoreError();
    }
  }

  LOG(INFO) << "State size = "
            << fuzzer_state.switch_state.GetNumTableEntries();

  // Use the same sequence seed for both generators.
  absl::SeedSeq seed;
  absl::BitGen gen_0(seed);
  absl::BitGen gen_1(seed);

  // TODO: If we could randomize the ordering of maps for the info in the
  // second config, we could check that the fuzzer is deterministic regardless.
  auto fuzzer_config2 = fuzzer_state.config;

  // Create 20 instances (of, in expectation, ~50 updates each), and verify that
  // they are identical.
  for (int i = 0; i < 20; ++i) {
    ASSERT_THAT(FuzzWriteRequest(&gen_0, fuzzer_state.config,
                                 fuzzer_state.switch_state),
                EqualsProto(FuzzWriteRequest(&gen_1, fuzzer_config2,
                                             fuzzer_state.switch_state)));
  }
}

TEST(FuzzUtilTest, FuzzWriteRequestCanFuzzMulticastGroupEntry) {
  FuzzerTestState fuzzer_state = ConstructStandardFuzzerTestState();
  absl::BitGen gen;
  // Ensure a multicast entity is fuzzed.
  fuzzer_state.config.SetFuzzMulticastGroupEntryProbability(1.0);

  AnnotatedWriteRequest write_request;
  // Because there is a non-zero chance to fuzz no updates.
  while (write_request.updates().empty()) {
    write_request =
        FuzzWriteRequest(&gen, fuzzer_state.config, fuzzer_state.switch_state,
                         /*max_batch_size=*/1);
  }

  EXPECT_TRUE(write_request.updates(0)
                  .pi()
                  .entity()
                  .packet_replication_engine_entry()
                  .has_multicast_group_entry());
}

// This test uses behavior specific to the main.p4 program. In main.p4,
// `refers_to_multicast_by_action_table` is a table that uses an action whose
// parameter refers to multicast group id.
TEST(FuzzUtilTest, FuzzTableFailsWhenNoMulticastReferenceIsAvailable) {
  FuzzerTestState fuzzer_state = ConstructStandardFuzzerTestState();

  // Generate entry referring to multicast and fail due to no references.
  pdpi::IrTableDefinition multicast_dependent_definition =
      gutil::FindOrDie(fuzzer_state.config.GetIrP4Info().tables_by_name(),
                       "refers_to_multicast_by_action_table");
  absl::BitGen gen;
  EXPECT_THAT(
      FuzzValidTableEntry(&gen, fuzzer_state.config, fuzzer_state.switch_state,
                          multicast_dependent_definition),
      gutil::StatusIs(absl::StatusCode::kFailedPrecondition));
}

// This test uses behavior specific to the main.p4 program. In main.p4,
// `refers_to_multicast_by_action_table` is a table that uses an action whose
// parameter refers to multicast group id.
TEST(FuzzUtilTest, FuzzTableRespectsMulticastReferences) {
  FuzzerTestState fuzzer_state = ConstructStandardFuzzerTestState();

  // Store multicast group entry being referenced.
  ASSERT_OK(fuzzer_state.switch_state.ApplyUpdate(
      gutil::ParseProtoOrDie<p4::v1::Update>(R"pb(
        type: INSERT
        entity {
          packet_replication_engine_entry {
            multicast_group_entry { multicast_group_id: 0x86 }
          }
        }
      )pb")));

  // Generate entry referring to multicast and ensure the action references
  // multicast group id.
  pdpi::IrTableDefinition multicast_dependent_definition =
      gutil::FindOrDie(fuzzer_state.config.GetIrP4Info().tables_by_name(),
                       "refers_to_multicast_by_action_table");
  absl::BitGen gen;
  EXPECT_THAT(
      FuzzValidTableEntry(&gen, fuzzer_state.config, fuzzer_state.switch_state,
                          multicast_dependent_definition),
      IsOkAndHolds(Partially(EqualsProto(R"pb(
        action {
          action {
            # Action id for `refers_to_multicast_action`.
            action_id: 18598416
            params { param_id: 1 value: "\x86" }
          }
        }
      )pb"))));
}

// This test uses behavior specific to the main.p4 program. In main.p4,
// built-in multicast group table replicas refer to fields in
// `referenced_by_multicast_replica_table`.
TEST(FuzzUtilTest, FuzzMulticastRespectsReplicaReferences) {
  FuzzerTestState fuzzer_state = ConstructStandardFuzzerTestState();

  // Store table entry being referenced.
  ASSERT_OK(fuzzer_state.switch_state.ApplyUpdate(
      gutil::ParseProtoOrDie<p4::v1::Update>(R"pb(
        type: INSERT
        entity {
          table_entry {
            table_id: 49197097
            # Port
            match {
              field_id: 1
              exact { value: "sample_port" }
            }
            # Instance
            match {
              field_id: 2
              exact { value: "\x86" }
            }
            action { action { action_id: 16777221 } }
          }
        }
      )pb")));

  absl::BitGen gen;
  p4::v1::MulticastGroupEntry multicast_entry;
  // Fuzz until multicast group entry has the one replica.
  while (multicast_entry.replicas().empty()) {
    ASSERT_OK_AND_ASSIGN(multicast_entry, FuzzValidMulticastGroupEntry(
                                              &gen, fuzzer_state.config,
                                              fuzzer_state.switch_state));
  }

  // Multicast group cannot be 0.
  EXPECT_NE(multicast_entry.multicast_group_id(), 0);

  // Ensure the one replica references values in table entry.
  ASSERT_EQ(multicast_entry.replicas_size(), 1);
  EXPECT_THAT(multicast_entry, Partially(EqualsProto(R"pb(
                replicas { instance: 0x86 port: "sample_port" }
              )pb")));
}

// This test uses behavior specific to the main.p4 program. In main.p4,
// built-in multicast group table replicas refer to fields in
// `referenced_by_multicast_replica_table`.
TEST(FuzzUtilTest, FuzzMulticastAreReproducibleWithState) {
  FuzzerTestState fuzzer_state = ConstructStandardFuzzerTestState();

  pdpi::IrTableDefinition multicast_dependency_definition =
      gutil::FindOrDie(fuzzer_state.config.GetIrP4Info().tables_by_name(),
                       "referenced_by_multicast_replica_table");

  absl::BitGen init_gen;

  // Generate up to 50 random table entries that can be referenced by multicast.
  for (int i = 0; i < 50; ++i) {
    p4::v1::Update update;
    update.set_type(p4::v1::Update::INSERT);
    ASSERT_OK_AND_ASSIGN(*update.mutable_entity()->mutable_table_entry(),
                         FuzzValidTableEntry(&init_gen, fuzzer_state.config,
                                             fuzzer_state.switch_state,
                                             multicast_dependency_definition));
    ASSERT_OK(fuzzer_state.switch_state.ApplyUpdate(update));
  }

  LOG(INFO) << "State size = "
            << fuzzer_state.switch_state.GetNumTableEntries();

  // Use the same sequence seed for both generators.
  absl::SeedSeq seed;
  absl::BitGen gen_0(seed);
  absl::BitGen gen_1(seed);

  // Create 50 instances and verify that they are identical.
  for (int i = 0; i < 20; ++i) {
    ASSERT_OK_AND_ASSIGN(
        p4::v1::MulticastGroupEntry entry0,
        FuzzValidMulticastGroupEntry(&gen_0, fuzzer_state.config,
                                     fuzzer_state.switch_state));

    ASSERT_OK_AND_ASSIGN(
        p4::v1::MulticastGroupEntry entry1,
        FuzzValidMulticastGroupEntry(&gen_1, fuzzer_state.config,
                                     fuzzer_state.switch_state));

    EXPECT_THAT(entry0, EqualsProto(entry1));
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
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrTableDefinition table_definition,
      GetAOneShotTableDefinition(fuzzer_state.config.GetIrP4Info()));
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrActionProfileDefinition action_profile_definition,
      GetActionProfileImplementingTable(fuzzer_state.config.GetIrP4Info(),
                                        table_definition));
  for (int i = 0; i < 1000; ++i) {
    // Tests a broad enough band of max weights to give us interesting
    // coverage while being narrow enough to likely catch issues when they
    // happen.
    int max_group_size = absl::Uniform<int>(
        fuzzer_state.gen, kActionProfileActionSetMaxCardinality,
        kGroupSizeArbitraryUpperBound);

    // Modify action profile in config and regenerate table and action profile
    // definitions.
    ASSERT_OK(SetMaxGroupSizeInActionProfile(
        fuzzer_state.config,
        action_profile_definition.action_profile().preamble().id(),
        max_group_size));
    ASSERT_OK_AND_ASSIGN(
        table_definition,
        GetAOneShotTableDefinition(fuzzer_state.config.GetIrP4Info()));
    ASSERT_OK_AND_ASSIGN(
        action_profile_definition,
        GetActionProfileImplementingTable(fuzzer_state.config.GetIrP4Info(),
                                          table_definition));

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
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrTableDefinition table_definition,
      GetAOneShotTableDefinition(fuzzer_state.config.GetIrP4Info()));
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrActionProfileDefinition action_profile_definition,
      GetActionProfileImplementingTable(fuzzer_state.config.GetIrP4Info(),
                                        table_definition));

  // Modify action profile in config and regenerate table and action profile
  // definitions.
  ASSERT_OK(SetMaxGroupSizeInActionProfile(
      fuzzer_state.config,
      action_profile_definition.action_profile().preamble().id(),
      /*max_group_size=*/0));
  ASSERT_OK_AND_ASSIGN(
      table_definition,
      GetAOneShotTableDefinition(fuzzer_state.config.GetIrP4Info()));
  ASSERT_OK_AND_ASSIGN(
      action_profile_definition,
      GetActionProfileImplementingTable(fuzzer_state.config.GetIrP4Info(),
                                        table_definition));

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
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrTableDefinition table_definition,
      GetAOneShotTableDefinition(fuzzer_state.config.GetIrP4Info()));
  ASSERT_OK_AND_ASSIGN(
      pdpi::IrActionProfileDefinition action_profile_definition,
      GetActionProfileImplementingTable(fuzzer_state.config.GetIrP4Info(),
                                        table_definition));
  for (int i = 0; i < 1000; ++i) {
    // Set up.
    const int max_group_size = absl::Uniform<int>(
        fuzzer_state.gen, 1, kActionProfileActionSetMaxCardinality);

    // Modify action profile in config and regenerate table and action profile
    // definitions.
    ASSERT_OK(SetMaxGroupSizeInActionProfile(
        fuzzer_state.config,
        action_profile_definition.action_profile().preamble().id(),
        max_group_size));
    ASSERT_OK_AND_ASSIGN(
        table_definition,
        GetAOneShotTableDefinition(fuzzer_state.config.GetIrP4Info()));
    ASSERT_OK_AND_ASSIGN(
        action_profile_definition,
        GetActionProfileImplementingTable(fuzzer_state.config.GetIrP4Info(),
                                          table_definition));

    // Fuzz an ActionProfileActionSet.
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
  fuzzer_state.config.SetDisabledFullyQualifiedNames({"ingress.id_test_table",
                                                      "ingress.exact_table",
                                                      "ingress.ternary_table"});

  absl::flat_hash_set<uint32_t> disallowed_ids;
  for (const auto& path :
       fuzzer_state.config.GetDisabledFullyQualifiedNames()) {
    std::vector<std::string> parts = absl::StrSplit(path, '.');
    ASSERT_OK_AND_ASSIGN(
        const pdpi::IrTableDefinition& table,
        gutil::FindOrStatus(fuzzer_state.config.GetIrP4Info().tables_by_name(),
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
  fuzzer_state.config.SetDisabledFullyQualifiedNames({
      "ingress.ternary_table.ipv6_upper_64_bits",
      "ingress.ternary_table.normal",
      "ingress.ternary_table.mac",
      "ingress.ternary_table.unsupported_field",
  });

  ASSERT_OK_AND_ASSIGN(
      const pdpi::IrTableDefinition& ternary_table,
      gutil::FindOrStatus(fuzzer_state.config.GetIrP4Info().tables_by_name(),
                          "ternary_table"));

  absl::flat_hash_set<uint32_t> disallowed_ids;
  for (const auto& path :
       fuzzer_state.config.GetDisabledFullyQualifiedNames()) {
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
      gutil::FindOrStatus(fuzzer_state.config.GetIrP4Info().actions_by_name(),
                          "do_thing_1"));
  fuzzer_state.config.SetDisabledFullyQualifiedNames({
      do_thing_action.preamble().name(),
  });

  ASSERT_OK_AND_ASSIGN(
      const pdpi::IrTableDefinition& id_test_table,
      gutil::FindOrStatus(fuzzer_state.config.GetIrP4Info().tables_by_name(),
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
