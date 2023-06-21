
#include <iostream>
#include <string>

#include "absl/algorithm/container.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "gutil/proto.h"
#include "gutil/testing.h"
#include "p4_pdpi/pd.h"
#include "p4_pdpi/sequencing_util.h"
#include "p4_pdpi/testing/main_p4_pd.pb.h"
#include "p4_pdpi/testing/test_helper.h"
#include "p4_pdpi/testing/test_p4info.h"

constexpr absl::string_view kInputBanner =
    "-- INPUT "
    "-----------------------------------------------------------------------\n";
const absl::string_view kOutputBanner =
    "-- OUTPUT "
    "---------------------------------------------------------------------\n";

// Runs golden file test for EntriesReferredToByTableEntry function.
void EntriesReferredToByTableEntryTest(absl::string_view test_name,
                                       absl::string_view pd_string) {
  std::cout << TestHeader(absl::StrCat("EntriesReferredToByTableEntryTest: ",
                                       test_name))
            << std::endl;

  pdpi::TableEntry pd_entry =
      gutil::ParseProtoOrDie<pdpi::TableEntry>(pd_string);

  const auto pi_table_entry =
      pdpi::PdTableEntryToPi(pdpi::GetTestIrP4Info(), pd_entry);
  CHECK(pi_table_entry.ok());  // Crash ok

  std::cout << kInputBanner << "-- PD table entry --\n";
  std::cout << gutil::PrintTextProto(pd_entry) << std::endl;

  auto referred_table_entries = pdpi::EntriesReferredToByTableEntry(
      *pi_table_entry, pdpi::GetTestIrP4Info());
  CHECK(referred_table_entries.ok());  // Crash ok

  // Since ReferredTableEntry has less than operator, we can sort and maintain
  // golden file stability.
  absl::c_sort(*referred_table_entries);
  std::cout << kOutputBanner << "-- ReferredTableEntries --\n";
  if (referred_table_entries->empty()) {
    std::cout << "<empty>\n";
  }
  for (const auto& entry : *referred_table_entries) {
    std::cout << absl::StrCat(entry) << std::endl;
  }
  std::cout << std::endl;
}

int main(int argc, char** argv) {
  EntriesReferredToByTableEntryTest(
      "Referring to using an entry with 1 match field",
      R"pb(
        referring_by_match_field_table_entry {
          match { referring_id_1: "key-a" }
          action { do_thing_4 {} }
          priority: 32
        }
      )pb");

  EntriesReferredToByTableEntryTest(
      "Referring to an entry using with 2 match fields",
      R"pb(
        referring_by_match_field_table_entry {
          match {
            referring_id_1: "key-x"
            referring_id_2 { value: "0x223" }
          }
          action { do_thing_4 {} }
          priority: 32
        }
      )pb");
  EntriesReferredToByTableEntryTest(
      "Referring to an entry using with 1 action param",
      R"pb(
        referring_by_action_table_entry {
          match { val: "0x012" }
          action {
            referring_to_one_match_field_action {
              referring_id_1: "key-a",
            }
          }
        }
      )pb");
  EntriesReferredToByTableEntryTest(
      "Referring to an entry using with 2 action params",
      R"pb(
        referring_by_action_table_entry {
          match { val: "0x012" }
          action {
            referring_to_two_match_fields_action {
              referring_id_1: "key-xy",
              referring_id_2: "0x033"
            }
          }
        }
      )pb");
  EntriesReferredToByTableEntryTest(
      "Entry that doesn't refer to other entry will not generate "
      "ReferredTableEntry",
      R"pb(
        two_match_fields_table_entry {
          match { id_1: "key-b", id_2: "0x024" }
          action { do_thing_4 {} }
        }
      )pb");

  return 0;
}
