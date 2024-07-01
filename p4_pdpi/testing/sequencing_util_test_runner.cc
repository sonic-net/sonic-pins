
#include <iostream>

#include "absl/algorithm/container.h"
#include "absl/container/btree_map.h"
#include "absl/container/flat_hash_map.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "gutil/proto.h"
#include "gutil/testing.h"
#include "p4_pdpi/ir.pb.h"
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
    "----------------------------------------------------------------------\n";

// Runs golden file test for CreateReferenceRelations
void CreateReferenceRelationsTest(const pdpi::IrP4Info& ir_p4info) {
  std::cout << TestHeader("CreateReferenceRelationsTest") << std::endl;
  absl::flat_hash_map<pdpi::ReferenceRelationKey, pdpi::ReferenceRelation>
      reference_relations = pdpi::CreateReferenceRelations(ir_p4info);

  std::cout << kInputBanner << "-- IrP4Info's references --" << std::endl;
  for (const pdpi::IrMatchFieldReference& reference : ir_p4info.references()) {
    std::cout << gutil::PrintTextProto(reference);
  }
  std::cout << std::endl;
  std::cout << kOutputBanner << "-- ReferenceRelations --" << std::endl;

  // Use btree_map to maintain order and make golden file stable.
  absl::btree_map<pdpi::ReferenceRelationKey, pdpi::ReferenceRelation>
      ordered_reference_relations(reference_relations.begin(),
                                  reference_relations.end());
  for (const auto& [key, reference_relation] : ordered_reference_relations) {
    std::cout << absl::StrCat(key) << ", " << absl::StrCat(reference_relation)
              << std::endl;
  }
  std::cout << std::endl;
}

// Runs golden file test for EntriesReferredToByTableEntry function.
void EntriesReferredToByTableEntryTest(absl::string_view test_name,
                                       absl::string_view pd_string) {
  std::cout << TestHeader(absl::StrCat("EntriesReferredToByTableEntryTest: ",
                                       test_name))
            << std::endl;

  pdpi::TableEntry pd_entry =
      gutil::ParseProtoOrDie<pdpi::TableEntry>(pd_string);

  const auto pi_table_entry = pdpi::PartialPdTableEntryToPiTableEntry(
      pdpi::GetTestIrP4Info(), pd_entry);
  CHECK(pi_table_entry.ok());  // Crash ok

  std::cout << kInputBanner << "-- PD table entry --\n";
  std::cout << gutil::PrintTextProto(pd_entry) << std::endl;

  auto referred_table_entries = pdpi::EntriesReferredToByTableEntry(
      pdpi::GetTestIrP4Info(), *pi_table_entry);
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

void CreateReferrableTableEntryTest(
    absl::string_view test_name, const pdpi::IrP4Info& ir_p4info,
    const absl::flat_hash_map<pdpi::ReferenceRelationKey,
                              pdpi::ReferenceRelation>& reference_relations,
    absl::string_view pd_string) {
  std::cout << TestHeader(
                   absl::StrCat("CreateReferrableTableEntryTest: ", test_name))
            << std::endl;

  pdpi::TableEntry pd_entry =
      gutil::ParseProtoOrDie<pdpi::TableEntry>(pd_string);

  const auto pi_table_entry =
      pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, pd_entry);

  CHECK_OK(pi_table_entry.status())  // Crash ok
      << "Unable to convert table entry from PD to PI: "
      << pi_table_entry.status().ToString();

  std::cout << kInputBanner << "-- PD table entry --" << std::endl;
  std::cout << gutil::PrintTextProto(pd_entry);

  absl::StatusOr<pdpi::ReferredTableEntry> referrable_table_entry =
      pdpi::CreateReferrableTableEntry(ir_p4info, reference_relations,
                                       *pi_table_entry);

  std::cout << kOutputBanner << "-- ReferredTableEntry or failure status --"
            << std::endl;
  if (!referrable_table_entry.ok()) {
    std::cout << referrable_table_entry.status().ToString() << std::endl;
    return;
  } else {
    std::cout << absl::StrCat(*referrable_table_entry) << std::endl;
  }
}

int main(int argc, char** argv) {
  std::cout << "Golden file test for utils used for reachability analysis.\n"
               "Note, std::cout doesn't work nicely with hex values: certain "
               "hex values are converted, via obsecure means, to control "
               "characters and become invisible in the golde file.\n\n";
  CreateReferenceRelationsTest(pdpi::GetTestIrP4Info());
  EntriesReferredToByTableEntryTest(
      "Referring to an entry with 2 match fields",
      R"pb(
        referring_by_match_field_table_entry {
          match { referring_id_1: "key-x" referring_id_2: "0x034" }
          action { do_thing_4 {} }
        }
      )pb");
  EntriesReferredToByTableEntryTest("Referring to an entry with 1 action param",
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
      "Referring to an entry with 2 action params",
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

  absl::flat_hash_map<pdpi::ReferenceRelationKey, pdpi::ReferenceRelation>
      default_reference_relations =
          pdpi::CreateReferenceRelations(pdpi::GetTestIrP4Info());

  // -- CreateReferredTableEntry test.
  CreateReferrableTableEntryTest(
      "Non-referred-to table entry will not generate ReferredTableEntry",
      pdpi::GetTestIrP4Info(), default_reference_relations,
      R"pb(
        referring_by_action_table_entry {
          match { val: "0x001" }
          action {
            referring_to_two_match_fields_action {
              referring_id_1: "key-a",
              referring_id_2: "0x000"
            }
          }
        }
      )pb");

  CreateReferrableTableEntryTest(
      "Referred-to table entry will generate ReferredTableEntry",
      pdpi::GetTestIrP4Info(), default_reference_relations,
      R"pb(
        two_match_fields_table_entry {
          match { id_1: "key-b", id_2: "0x034" }
          action { do_thing_4 {} }
        }
      )pb");

  return 0;
}
