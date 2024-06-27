#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto.h"
#include "gutil/proto_matchers.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/pd.h"
#include "p4_pdpi/testing/main_p4_pd.pb.h"
#include "p4_pdpi/testing/test_p4info.h"
#include "p4_pdpi/translation_options.h"

namespace pdpi {
namespace {

using gutil::EqualsProto;
using testing::Eq;
using testing::SizeIs;

// A random collection of valid PD table entries for the test p4info.
absl::StatusOr<TableEntries> ValidPdTableEntries() {
  return gutil::ParseTextProto<TableEntries>(R"pb(
    entries {
      wcmp_table_entry {
        match { ipv4 { value: "0.0.255.0" prefix_length: 24 } }
        wcmp_actions {
          action { do_thing_1 { arg2: "0x01234567" arg1: "0x01234568" } }
          weight: 1
        }
        wcmp_actions {
          action { do_thing_1 { arg2: "0x01234569" arg1: "0x01234560" } }
          weight: 2
        }
      }
    }
    entries {
      exact_table_entry {
        match {
          normal: "0x054"
          ipv4: "10.43.12.5"
          ipv6: "3242::fee2"
          mac: "00:11:22:33:44:55"
          str: "hello"
        }
        action { NoAction {} }
      }
    }
    entries {
      optional_table_entry {
        match { ipv6 { value: "3242::fee2" } }
        action { do_thing_1 { arg2: "0x01234567" arg1: "0x01234568" } }
        priority: 32
      }
    })pb");
}

absl::StatusOr<TableEntries> ValidPdTableEntriesWithMulticastGroupEntry() {
  ASSIGN_OR_RETURN(TableEntries pd, ValidPdTableEntries());
  ASSIGN_OR_RETURN(
      *pd.add_entries(),
      gutil::ParseTextProto<TableEntry>(
          R"pb(
            multicast_group_table_entry {
              match { multicast_group_id: "0x0007" }
              action {
                replicate {
                  replicas { port: "some_port" instance: "0x0001" }
                  replicas { port: "some_port" instance: "0x0002" }
                  replicas { port: "some_other_port" instance: "0x0001" }
                }
              }
            })pb"));
  return pd;
}

absl::StatusOr<IrTableEntries> ValidIrTableEntries() {
  ASSIGN_OR_RETURN(TableEntries pd, ValidPdTableEntries());
  return PartialPdTableEntriesToIrTableEntries(GetTestIrP4Info(), pd);
}

absl::StatusOr<IrEntities> ValidIrEntities() {
  ASSIGN_OR_RETURN(TableEntries pd,
                   ValidPdTableEntriesWithMulticastGroupEntry());
  return PdTableEntriesToIrEntities(GetTestIrP4Info(), pd);
}

using VectorTranslationTest = testing::TestWithParam<pdpi::TranslationOptions>;

TEST_P(VectorTranslationTest,
       FooTableEntriesToBarPointWiseEqualFooTableEntryToBar) {
  const TranslationOptions options = GetParam();
  const auto& info = GetTestIrP4Info();
  ASSERT_OK_AND_ASSIGN(TableEntries pd_entries, ValidPdTableEntries());

  IrTableEntries ir_entries, expected_ir_entries;
  std::vector<p4::v1::TableEntry> pi_entries_from_pd,
      expected_pi_entries_from_pd;
  std::vector<p4::v1::TableEntry> pi_entries_from_ir,
      expected_pi_entries_from_ir;
  ASSERT_OK_AND_ASSIGN(ir_entries, PartialPdTableEntriesToIrTableEntries(
                                       info, pd_entries, options));
  ASSERT_OK_AND_ASSIGN(
      pi_entries_from_pd,
      PartialPdTableEntriesToPiTableEntries(info, pd_entries, options));
  ASSERT_OK_AND_ASSIGN(pi_entries_from_ir,
                       IrTableEntriesToPi(info, ir_entries, options));
  for (const auto& pd_entry : pd_entries.entries()) {
    ASSERT_OK_AND_ASSIGN(
        *expected_ir_entries.add_entries(),
        PartialPdTableEntryToIrTableEntry(info, pd_entry, options));
    ASSERT_OK_AND_ASSIGN(
        expected_pi_entries_from_pd.emplace_back(),
        PartialPdTableEntryToPiTableEntry(info, pd_entry, options));
  }
  for (const auto& ir_entry : ir_entries.entries()) {
    ASSERT_OK_AND_ASSIGN(expected_pi_entries_from_ir.emplace_back(),
                         IrTableEntryToPi(info, ir_entry, options));
  }

  // Check pointwise equality for PD -> IR.
  ASSERT_EQ(ir_entries.entries_size(), pd_entries.entries_size());
  for (int i = 0; i < ir_entries.entries_size(); ++i) {
    EXPECT_THAT(ir_entries.entries(i),
                EqualsProto(expected_ir_entries.entries(i)))
        << "for IR entry at index " << i;
  }

  // Check pointwise equality for PD -> PI.
  ASSERT_THAT(pi_entries_from_pd, SizeIs(Eq(pd_entries.entries_size())));
  for (int i = 0; i < pi_entries_from_pd.size(); ++i) {
    EXPECT_THAT(pi_entries_from_pd[i],
                EqualsProto(expected_pi_entries_from_pd[i]))
        << "for PI entry at index " << i;
  }

  // Check pointwise equality for IR -> PI.
  ASSERT_THAT(pi_entries_from_ir, SizeIs(Eq(ir_entries.entries_size())));
  for (int i = 0; i < pi_entries_from_ir.size(); ++i) {
    EXPECT_THAT(pi_entries_from_ir[i],
                EqualsProto(expected_pi_entries_from_ir[i]))
        << "for PI entry at index " << i;
  }
}

TEST_P(VectorTranslationTest,
       TableEntriesToEntitiesPointWiseEqualTableEntryToEntity) {
  const TranslationOptions options = GetParam();
  const auto& info = GetTestIrP4Info();
  ASSERT_OK_AND_ASSIGN(TableEntries pd_entries,
                       ValidPdTableEntriesWithMulticastGroupEntry());

  IrEntities ir_entities, expected_ir_entities;
  std::vector<p4::v1::Entity> pi_entities_from_pd, expected_pi_entities_from_pd;
  std::vector<p4::v1::Entity> pi_entities_from_ir, expected_pi_entities_from_ir;
  ASSERT_OK_AND_ASSIGN(ir_entities,
                       PdTableEntriesToIrEntities(info, pd_entries, options));
  ASSERT_OK_AND_ASSIGN(pi_entities_from_pd,
                       PdTableEntriesToPiEntities(info, pd_entries, options));
  ASSERT_OK_AND_ASSIGN(pi_entities_from_ir,
                       IrEntitiesToPi(info, ir_entities, options));
  for (const auto& pd_entry : pd_entries.entries()) {
    ASSERT_OK_AND_ASSIGN(*expected_ir_entities.add_entities(),
                         PdTableEntryToIrEntity(info, pd_entry, options));
    ASSERT_OK_AND_ASSIGN(expected_pi_entities_from_pd.emplace_back(),
                         PdTableEntryToPiEntity(info, pd_entry, options));
  }
  for (const auto& ir_entry : ir_entities.entities()) {
    ASSERT_OK_AND_ASSIGN(expected_pi_entities_from_ir.emplace_back(),
                         IrEntityToPi(info, ir_entry, options));
  }

  // Check pointwise equality for PD -> IR.
  ASSERT_EQ(ir_entities.entities_size(), pd_entries.entries_size());
  for (int i = 0; i < ir_entities.entities_size(); ++i) {
    EXPECT_THAT(ir_entities.entities(i),
                EqualsProto(expected_ir_entities.entities(i)))
        << "for IR entity at index " << i;
  }

  // Check pointwise equality for PD -> PI.
  ASSERT_THAT(pi_entities_from_pd, SizeIs(Eq(pd_entries.entries_size())));
  for (int i = 0; i < pi_entities_from_pd.size(); ++i) {
    EXPECT_THAT(pi_entities_from_pd[i],
                EqualsProto(expected_pi_entities_from_pd[i]))
        << "for PI entity at index " << i;
  }

  // Check pointwise equality for IR -> PI.
  ASSERT_THAT(pi_entities_from_ir, SizeIs(Eq(ir_entities.entities_size())));
  for (int i = 0; i < pi_entities_from_ir.size(); ++i) {
    EXPECT_THAT(pi_entities_from_ir[i],
                EqualsProto(expected_pi_entities_from_ir[i]))
        << "for PI entity at index " << i;
  }
}

using PdToPiRoundtripTest = testing::TestWithParam<pdpi::TranslationOptions>;

TEST_P(PdToPiRoundtripTest, PartialEntriesTranslationRoundrips) {
  const TranslationOptions& options = GetParam();
  const auto& info = GetTestIrP4Info();
  ASSERT_OK_AND_ASSIGN(TableEntries pd_entries, ValidPdTableEntries());

  TableEntries roundtripped_pd_entries;
  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::TableEntry> pi_entries,
      PartialPdTableEntriesToPiTableEntries(info, pd_entries, options));
  ASSERT_OK(
      PiTableEntriesToPd(info, pi_entries, &roundtripped_pd_entries, options));
  EXPECT_THAT(roundtripped_pd_entries, EqualsProto(pd_entries));
}

TEST_P(PdToPiRoundtripTest, EntriesTranslationRoundrips) {
  const TranslationOptions& options = GetParam();
  const auto& info = GetTestIrP4Info();
  ASSERT_OK_AND_ASSIGN(TableEntries pd_entries,
                       ValidPdTableEntriesWithMulticastGroupEntry());

  TableEntries roundtripped_pd_entries;
  ASSERT_OK_AND_ASSIGN(std::vector<p4::v1::Entity> pi_entities,
                       PdTableEntriesToPiEntities(info, pd_entries, options));
  ASSERT_OK(PiEntitiesToPdTableEntries(info, pi_entities,
                                       &roundtripped_pd_entries, options));
  EXPECT_THAT(roundtripped_pd_entries, EqualsProto(pd_entries));
}

using PdToIrRoundtripTest = testing::TestWithParam<pdpi::TranslationOptions>;

TEST_P(PdToIrRoundtripTest, PartialEntriesTranslationRoundrips) {
  const TranslationOptions& options = GetParam();
  const auto& info = GetTestIrP4Info();
  ASSERT_OK_AND_ASSIGN(TableEntries pd_entries, ValidPdTableEntries());

  TableEntries roundtripped_pd_entries;
  ASSERT_OK_AND_ASSIGN(
      IrTableEntries ir_entries,
      PartialPdTableEntriesToIrTableEntries(info, pd_entries, options));
  ASSERT_OK(
      IrTableEntriesToPd(info, ir_entries, &roundtripped_pd_entries, options));
  EXPECT_THAT(roundtripped_pd_entries, EqualsProto(pd_entries));
}

TEST_P(PdToIrRoundtripTest, EntriesTranslationRoundrips) {
  const TranslationOptions& options = GetParam();
  const auto& info = GetTestIrP4Info();
  ASSERT_OK_AND_ASSIGN(TableEntries pd_entries,
                       ValidPdTableEntriesWithMulticastGroupEntry());

  TableEntries roundtripped_pd_entries;
  ASSERT_OK_AND_ASSIGN(IrEntities ir_entities,
                       PdTableEntriesToIrEntities(info, pd_entries, options));
  ASSERT_OK(IrEntitiesToPdTableEntries(info, ir_entities,
                                       &roundtripped_pd_entries, options));
  EXPECT_THAT(roundtripped_pd_entries, EqualsProto(pd_entries));
}

using IrToPiRoundtripTest = testing::TestWithParam<pdpi::TranslationOptions>;

TEST_P(IrToPiRoundtripTest, EntriesTranslationRoundrips) {
  const TranslationOptions& options = GetParam();
  const auto& info = GetTestIrP4Info();
  ASSERT_OK_AND_ASSIGN(IrTableEntries ir_entries, ValidIrTableEntries());

  ASSERT_OK_AND_ASSIGN(std::vector<p4::v1::TableEntry> pi_entries,
                       IrTableEntriesToPi(info, ir_entries, options));
  ASSERT_OK_AND_ASSIGN(IrTableEntries roundtripped_ir_entries,
                       PiTableEntriesToIr(info, pi_entries, options));

  ASSERT_EQ(roundtripped_ir_entries.entries_size(), ir_entries.entries_size());
  for (int i = 0; i < roundtripped_ir_entries.entries_size(); ++i) {
    EXPECT_THAT(roundtripped_ir_entries.entries(i),
                EqualsProto(ir_entries.entries(i)));
  }
}

TEST_P(IrToPiRoundtripTest, EntitiesTranslationRoundrips) {
  const TranslationOptions& options = GetParam();
  const auto& info = GetTestIrP4Info();
  ASSERT_OK_AND_ASSIGN(IrEntities ir_entities, ValidIrEntities());

  ASSERT_OK_AND_ASSIGN(std::vector<p4::v1::Entity> pi_entities,
                       IrEntitiesToPi(info, ir_entities, options));
  ASSERT_OK_AND_ASSIGN(IrEntities roundtripped_ir_entities,
                       PiEntitiesToIr(info, pi_entities, options));

  ASSERT_EQ(roundtripped_ir_entities.entities_size(),
            ir_entities.entities_size());
  for (int i = 0; i < roundtripped_ir_entities.entities_size(); ++i) {
    EXPECT_THAT(roundtripped_ir_entities.entities(i),
                EqualsProto(ir_entities.entities(i)));
  }
}

TEST(PdToPiOptionsTest,
     OptionAllowUnsupportedDoesNotAffectPartialEntryTranslationResult) {
  const auto& info = GetTestIrP4Info();
  ASSERT_OK_AND_ASSIGN(TableEntries pd_entries, ValidPdTableEntries());

  for (const auto& pd_entry : pd_entries.entries()) {
    for (bool key_only : {false, true}) {
      SCOPED_TRACE(absl::StrFormat("key_only = %v", key_only));
      SCOPED_TRACE(absl::StrCat("pd entry = ", pd_entry.DebugString()));
      ASSERT_OK_AND_ASSIGN(
          p4::v1::TableEntry pi_without_allow_unsupported,
          PartialPdTableEntryToPiTableEntry(info, pd_entry,
                                            TranslationOptions{
                                                .key_only = key_only,
                                                .allow_unsupported = false,
                                            }));
      ASSERT_OK_AND_ASSIGN(
          p4::v1::TableEntry pi_with_allow_unsupported,
          PartialPdTableEntryToPiTableEntry(info, pd_entry,
                                            TranslationOptions{
                                                .key_only = key_only,
                                                .allow_unsupported = true,
                                            }));
      EXPECT_THAT(pi_with_allow_unsupported,
                  EqualsProto(pi_without_allow_unsupported));
    }
  }
}

TEST(PdToPiOptionsTest,
     OptionAllowUnsupportedDoesNotAffectEntryTranslationResult) {
  const auto& info = GetTestIrP4Info();
  ASSERT_OK_AND_ASSIGN(TableEntries pd_entries,
                       ValidPdTableEntriesWithMulticastGroupEntry());

  for (const auto& pd_entry : pd_entries.entries()) {
    for (bool key_only : {false, true}) {
      SCOPED_TRACE(absl::StrFormat("key_only = %v", key_only));
      SCOPED_TRACE(absl::StrCat("pd entry = ", pd_entry.DebugString()));
      ASSERT_OK_AND_ASSIGN(
          p4::v1::Entity pi_without_allow_unsupported,
          PdTableEntryToPiEntity(info, pd_entry,
                                 TranslationOptions{
                                     .key_only = key_only,
                                     .allow_unsupported = false,
                                 }));
      ASSERT_OK_AND_ASSIGN(p4::v1::Entity pi_with_allow_unsupported,
                           PdTableEntryToPiEntity(info, pd_entry,
                                                  TranslationOptions{
                                                      .key_only = key_only,
                                                      .allow_unsupported = true,
                                                  }));
      EXPECT_THAT(pi_with_allow_unsupported,
                  EqualsProto(pi_without_allow_unsupported));
    }
  }
}

TEST(PdToIrOptionsTest,
     OptionAllowUnsupportedDoesNotAffectPartialEntryTranslationResult) {
  const auto& info = GetTestIrP4Info();
  ASSERT_OK_AND_ASSIGN(TableEntries pd_entries, ValidPdTableEntries());

  for (const auto& pd_entry : pd_entries.entries()) {
    for (bool key_only : {false, true}) {
      SCOPED_TRACE(absl::StrFormat("key_only = %v", key_only));
      SCOPED_TRACE(absl::StrCat("pd entry = ", pd_entry.DebugString()));
      ASSERT_OK_AND_ASSIGN(
          IrTableEntry ir_without_allow_unsupported,
          PartialPdTableEntryToIrTableEntry(info, pd_entry,
                                            TranslationOptions{
                                                .key_only = key_only,
                                                .allow_unsupported = false,
                                            }));
      ASSERT_OK_AND_ASSIGN(
          IrTableEntry ir_with_allow_unsupported,
          PartialPdTableEntryToIrTableEntry(info, pd_entry,
                                            TranslationOptions{
                                                .key_only = key_only,
                                                .allow_unsupported = true,
                                            }));
      EXPECT_THAT(ir_with_allow_unsupported,
                  EqualsProto(ir_without_allow_unsupported));
    }
  }
}

TEST(PdToIrOptionsTest,
     OptionAllowUnsupportedDoesNotAffectEntryTranslationResult) {
  const auto& info = GetTestIrP4Info();
  ASSERT_OK_AND_ASSIGN(TableEntries pd_entries,
                       ValidPdTableEntriesWithMulticastGroupEntry());

  for (const auto& pd_entry : pd_entries.entries()) {
    for (bool key_only : {false, true}) {
      SCOPED_TRACE(absl::StrFormat("key_only = %v", key_only));
      SCOPED_TRACE(absl::StrCat("pd entry = ", pd_entry.DebugString()));
      ASSERT_OK_AND_ASSIGN(
          IrEntity ir_without_allow_unsupported,
          PdTableEntryToIrEntity(info, pd_entry,
                                 TranslationOptions{
                                     .key_only = key_only,
                                     .allow_unsupported = false,
                                 }));
      ASSERT_OK_AND_ASSIGN(IrEntity ir_with_allow_unsupported,
                           PdTableEntryToIrEntity(info, pd_entry,
                                                  TranslationOptions{
                                                      .key_only = key_only,
                                                      .allow_unsupported = true,
                                                  }));
      EXPECT_THAT(ir_with_allow_unsupported,
                  EqualsProto(ir_without_allow_unsupported));
    }
  }
}

TEST(IrToPiOptionsTest,
     OptionAllowUnsupportedDoesNotAffectEntryTranslationResult) {
  const auto& info = GetTestIrP4Info();
  ASSERT_OK_AND_ASSIGN(IrTableEntries ir_entries, ValidIrTableEntries());

  for (const auto& ir_entry : ir_entries.entries()) {
    for (bool key_only : {false, true}) {
      SCOPED_TRACE(absl::StrFormat("key_only = %v", key_only));
      SCOPED_TRACE(absl::StrCat("ir entry = ", ir_entry.DebugString()));
      ASSERT_OK_AND_ASSIGN(p4::v1::TableEntry pi_without_allow_unsupported,
                           IrTableEntryToPi(info, ir_entry,
                                            TranslationOptions{
                                                .key_only = key_only,
                                                .allow_unsupported = false,
                                            }));
      ASSERT_OK_AND_ASSIGN(p4::v1::TableEntry pi_with_allow_unsupported,
                           IrTableEntryToPi(info, ir_entry,
                                            TranslationOptions{
                                                .key_only = key_only,
                                                .allow_unsupported = true,
                                            }));
      EXPECT_THAT(pi_with_allow_unsupported,
                  EqualsProto(pi_without_allow_unsupported));
    }
  }
}

TEST(IrToPiOptionsTest,
     OptionAllowUnsupportedDoesNotAffectEntityTranslationResult) {
  const auto& info = GetTestIrP4Info();
  ASSERT_OK_AND_ASSIGN(IrEntities ir_entities, ValidIrEntities());

  for (const auto& ir_entity : ir_entities.entities()) {
    for (bool key_only : {false, true}) {
      SCOPED_TRACE(absl::StrFormat("key_only = %v", key_only));
      SCOPED_TRACE(absl::StrCat("ir entry = ", ir_entity.DebugString()));
      ASSERT_OK_AND_ASSIGN(p4::v1::Entity pi_without_allow_unsupported,
                           IrEntityToPi(info, ir_entity,
                                        TranslationOptions{
                                            .key_only = key_only,
                                            .allow_unsupported = false,
                                        }));
      ASSERT_OK_AND_ASSIGN(p4::v1::Entity pi_with_allow_unsupported,
                           IrEntityToPi(info, ir_entity,
                                        TranslationOptions{
                                            .key_only = key_only,
                                            .allow_unsupported = true,
                                        }));
      EXPECT_THAT(pi_with_allow_unsupported,
                  EqualsProto(pi_without_allow_unsupported));
    }
  }
}

TEST(IrToPdOptionsTest,
     OptionAllowUnsupportedDoesNotAffectEntryTranslationResult) {
  const auto& info = GetTestIrP4Info();
  ASSERT_OK_AND_ASSIGN(IrTableEntries ir_entries, ValidIrTableEntries());

  for (const auto& ir_entry : ir_entries.entries()) {
    for (bool key_only : {false, true}) {
      SCOPED_TRACE(absl::StrFormat("key_only = %v", key_only));
      SCOPED_TRACE(absl::StrCat("ir entry = ", ir_entry.DebugString()));
      TableEntry pd_without_allow_unsupported, pd_with_allow_unsupported;
      ASSERT_OK(IrTableEntryToPd(info, ir_entry, &pd_without_allow_unsupported,
                                 TranslationOptions{
                                     .key_only = key_only,
                                     .allow_unsupported = false,
                                 }));
      ASSERT_OK(IrTableEntryToPd(info, ir_entry, &pd_with_allow_unsupported,
                                 TranslationOptions{
                                     .key_only = key_only,
                                     .allow_unsupported = true,
                                 }));
      EXPECT_THAT(pd_with_allow_unsupported,
                  EqualsProto(pd_without_allow_unsupported));
    }
  }
}

TEST(IrToPdOptionsTest,
     OptionAllowUnsupportedDoesNotAffectEntityTranslationResult) {
  const auto& info = GetTestIrP4Info();
  ASSERT_OK_AND_ASSIGN(IrEntities ir_entities, ValidIrEntities());

  for (const auto& ir_entity : ir_entities.entities()) {
    for (bool key_only : {false, true}) {
      SCOPED_TRACE(absl::StrFormat("key_only = %v", key_only));
      SCOPED_TRACE(absl::StrCat("ir entry = ", ir_entity.DebugString()));
      TableEntry pd_without_allow_unsupported, pd_with_allow_unsupported;
      ASSERT_OK(IrEntityToPdTableEntry(info, ir_entity,
                                       &pd_without_allow_unsupported,
                                       TranslationOptions{
                                           .key_only = key_only,
                                           .allow_unsupported = false,
                                       }));
      ASSERT_OK(IrEntityToPdTableEntry(info, ir_entity,
                                       &pd_with_allow_unsupported,
                                       TranslationOptions{
                                           .key_only = key_only,
                                           .allow_unsupported = true,
                                       }));
      EXPECT_THAT(pd_with_allow_unsupported,
                  EqualsProto(pd_without_allow_unsupported));
    }
  }
}

std::string GetTestNameSuffix(
    const testing::TestParamInfo<TranslationOptions>& info) {
  return absl::StrFormat("key_only_%v_and_allow_unsupported_%v",
                         info.param.key_only, info.param.allow_unsupported);
}

INSTANTIATE_TEST_SUITE_P(
    , VectorTranslationTest,
    testing::ValuesIn({
        TranslationOptions{.key_only = false, .allow_unsupported = false},
        TranslationOptions{.key_only = true, .allow_unsupported = false},
        TranslationOptions{.key_only = false, .allow_unsupported = true},
        TranslationOptions{.key_only = true, .allow_unsupported = true},
    }),
    GetTestNameSuffix);

INSTANTIATE_TEST_SUITE_P(, PdToPiRoundtripTest,
                         testing::ValuesIn({
                             TranslationOptions{.allow_unsupported = false},
                             TranslationOptions{.allow_unsupported = true},
                         }),
                         GetTestNameSuffix);

INSTANTIATE_TEST_SUITE_P(, PdToIrRoundtripTest,
                         testing::ValuesIn({
                             TranslationOptions{.allow_unsupported = false},
                             TranslationOptions{.allow_unsupported = true},
                         }),
                         GetTestNameSuffix);

INSTANTIATE_TEST_SUITE_P(, IrToPiRoundtripTest,
                         testing::ValuesIn({
                             TranslationOptions{.allow_unsupported = false},
                             TranslationOptions{.allow_unsupported = true},
                         }),
                         GetTestNameSuffix);

}  // namespace
}  // namespace pdpi
