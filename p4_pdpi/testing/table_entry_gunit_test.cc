#include <vector>

#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "p4/v1/p4runtime.pb.h"
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

TEST(PdTableEntriesToPI, PointwiseEqualsPdTableEntryToPi) {
  const auto& info = GetTestIrP4Info();
  ASSERT_OK_AND_ASSIGN(TableEntries pd_entries, ValidPdTableEntries());

  std::vector<p4::v1::TableEntry> pi_entries, expected_pi_entries;
  ASSERT_OK_AND_ASSIGN(pi_entries, PdTableEntriesToPi(info, pd_entries));
  for (auto& pd_entry : pd_entries.entries()) {
    ASSERT_OK_AND_ASSIGN(expected_pi_entries.emplace_back(),
                         PdTableEntryToPi(info, pd_entry));
  }

  ASSERT_THAT(pi_entries, SizeIs(Eq(pd_entries.entries_size())));
  for (int i = 0; i < pi_entries.size(); ++i) {
    EXPECT_THAT(pi_entries[i], EqualsProto(expected_pi_entries[i]))
        << "for entry at index " << i;
  }
}

TEST(PdTableEntriesToPI, RoundTripsWithPiTableEntriesToPd) {
  const auto& info = GetTestIrP4Info();
  ASSERT_OK_AND_ASSIGN(TableEntries pd_entries, ValidPdTableEntries());

  TableEntries roundtripped_pd_entries;
  ASSERT_OK_AND_ASSIGN(std::vector<p4::v1::TableEntry> pi_entries,
                       PdTableEntriesToPi(info, pd_entries));
  ASSERT_OK(PiTableEntriesToPd(info, pi_entries, &roundtripped_pd_entries));
  EXPECT_THAT(roundtripped_pd_entries, EqualsProto(pd_entries));
}

}  // namespace
}  // namespace pdpi
