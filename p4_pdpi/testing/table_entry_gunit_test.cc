#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
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

absl::StatusOr<std::vector<pdpi::IrTableEntry>> ValidIrTableEntries() {
  std::vector<pdpi::IrTableEntry> ir;
  ASSIGN_OR_RETURN(TableEntries pd, ValidPdTableEntries());
  for (const auto& pd_entry : pd.entries()) {
    ASSIGN_OR_RETURN(ir.emplace_back(),
                     PdTableEntryToIr(GetTestIrP4Info(), pd_entry));
  }
  return ir;
}

using VectorTranslationTest = testing::TestWithParam<bool>;  // key_only?

TEST_P(VectorTranslationTest,
       FooTableEntriesToBarPointWiseEqualFooTableEntryToBar) {
  const bool key_only = GetParam();
  const auto& info = GetTestIrP4Info();
  ASSERT_OK_AND_ASSIGN(TableEntries pd_entries, ValidPdTableEntries());

  std::vector<pdpi::IrTableEntry> ir_entries, expected_ir_entries;
  std::vector<p4::v1::TableEntry> pi_entries_from_pd,
      expected_pi_entries_from_pd;
  std::vector<p4::v1::TableEntry> pi_entries_from_ir,
      expected_pi_entries_from_ir;
  ASSERT_OK_AND_ASSIGN(ir_entries,
                       PdTableEntriesToIr(info, pd_entries, key_only));
  ASSERT_OK_AND_ASSIGN(pi_entries_from_pd,
                       PdTableEntriesToPi(info, pd_entries, key_only));
  ASSERT_OK_AND_ASSIGN(pi_entries_from_ir,
                       IrTableEntriesToPi(info, ir_entries, key_only));
  for (const auto& pd_entry : pd_entries.entries()) {
    ASSERT_OK_AND_ASSIGN(expected_ir_entries.emplace_back(),
                         PdTableEntryToIr(info, pd_entry, key_only));
    ASSERT_OK_AND_ASSIGN(expected_pi_entries_from_pd.emplace_back(),
                         PdTableEntryToPi(info, pd_entry, key_only));
  }
  for (const auto& ir_entry : ir_entries) {
    ASSERT_OK_AND_ASSIGN(expected_pi_entries_from_ir.emplace_back(),
                         IrTableEntryToPi(info, ir_entry, key_only));
  }

  // Check pointwise equality for PD -> IR.
  ASSERT_THAT(ir_entries, SizeIs(Eq(pd_entries.entries_size())));
  for (int i = 0; i < ir_entries.size(); ++i) {
    EXPECT_THAT(ir_entries[i], EqualsProto(expected_ir_entries[i]))
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
  ASSERT_THAT(pi_entries_from_ir, SizeIs(Eq(ir_entries.size())));
  for (int i = 0; i < pi_entries_from_ir.size(); ++i) {
    EXPECT_THAT(pi_entries_from_ir[i],
                EqualsProto(expected_pi_entries_from_ir[i]))
        << "for PI entry at index " << i;
  }
}

TEST(PdTableEntriesToPiTest, RoundTripsWithPiTableEntriesToPd) {
  const auto& info = GetTestIrP4Info();
  ASSERT_OK_AND_ASSIGN(TableEntries pd_entries, ValidPdTableEntries());

  TableEntries roundtripped_pd_entries;
  ASSERT_OK_AND_ASSIGN(std::vector<p4::v1::TableEntry> pi_entries,
                       PdTableEntriesToPi(info, pd_entries));
  ASSERT_OK(PiTableEntriesToPd(info, pi_entries, &roundtripped_pd_entries));
  EXPECT_THAT(roundtripped_pd_entries, EqualsProto(pd_entries));
}

TEST(PdTableEntriesToIrTest, RoundTripsWithIrTableEntriesToPd) {
  const auto& info = GetTestIrP4Info();
  ASSERT_OK_AND_ASSIGN(TableEntries pd_entries, ValidPdTableEntries());

  TableEntries roundtripped_pd_entries;
  ASSERT_OK_AND_ASSIGN(std::vector<pdpi::IrTableEntry> ir_entries,
                       PdTableEntriesToIr(info, pd_entries));
  ASSERT_OK(IrTableEntriesToPd(info, ir_entries, &roundtripped_pd_entries));
  EXPECT_THAT(roundtripped_pd_entries, EqualsProto(pd_entries));
}

TEST(IrTableEntriesToPiTest, RoundTripsWithPiTableEntriesToIr) {
  const auto& info = GetTestIrP4Info();
  ASSERT_OK_AND_ASSIGN(std::vector<pdpi::IrTableEntry> ir_entries,
                       ValidIrTableEntries());

  ASSERT_OK_AND_ASSIGN(std::vector<p4::v1::TableEntry> pi_entries,
                       IrTableEntriesToPi(info, ir_entries));
  ASSERT_OK_AND_ASSIGN(std::vector<pdpi::IrTableEntry> roundtripped_ir_entries,
                       PiTableEntriesToIr(info, pi_entries));

  ASSERT_THAT(roundtripped_ir_entries, SizeIs(Eq(ir_entries.size())));
  for (int i = 0; i < roundtripped_ir_entries.size(); ++i) {
    EXPECT_THAT(roundtripped_ir_entries[i], EqualsProto(ir_entries[i]));
  }
}

INSTANTIATE_TEST_SUITE_P(, VectorTranslationTest, testing::Bool(),
                         [](const auto& info) -> std::string {
                           return absl::StrCat("key_only_",
                                               info.param ? "true" : "false");
                         });

}  // namespace
}  // namespace pdpi
