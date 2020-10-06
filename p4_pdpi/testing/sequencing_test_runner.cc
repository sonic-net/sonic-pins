// Copyright 2020 Google LLC
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

#include <iostream>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "glog/logging.h"
#include "gutil/status.h"
#include "gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/pd.h"
#include "p4_pdpi/sequencing.h"
#include "p4_pdpi/testing/main_p4_pd.pb.h"
#include "p4_pdpi/testing/test_helper.h"

using ::p4::config::v1::P4Info;
using ::p4::v1::Update;
using ::p4::v1::WriteRequest;

// Takes a set of PD updates and sequences them.
void SequenceTest(const pdpi::IrP4Info& info, const std::string& test_name,
                  const std::vector<std::string> pd_update_strings) {
  // Convert input to PI.
  std::vector<Update> pi_updates;
  std::vector<pdpi::Update> pd_updates;
  for (const auto& pd_update_string : pd_update_strings) {
    const auto pd_update =
        gutil::ParseProtoOrDie<pdpi::Update>(pd_update_string);
    pd_updates.push_back(pd_update);
    const auto pi_update_or_status = pdpi::PdUpdateToPi(info, pd_update);
    if (!pi_update_or_status.status().ok()) {
      std::cerr << "Unable to convert Update from PD to PI." << std::endl;
      return;
    }
    const auto& pi_update = pi_update_or_status.value();
    pi_updates.push_back(pi_update);
  }

  // Output input.
  std::cout << TestHeader(absl::StrCat("SequenceTest: ", test_name))
            << std::endl
            << std::endl;
  std::cout << "--- PD updates (input):" << std::endl;
  if (pd_updates.empty()) std::cout << "<empty>" << std::endl << std::endl;

  // Run sequencing.
  absl::StatusOr<std::vector<WriteRequest>> result_or_status =
      pdpi::SequencePiUpdatesIntoWriteRequests(info, pi_updates);
  if (!result_or_status.status().ok()) {
    std::cout << "--- Sequencing failed (output):" << std::endl;
    std::cout << result_or_status.status() << std::endl;
    return;
  }
  std::vector<WriteRequest>& result = result_or_status.value();

  // Output results.
  for (const auto& update : pd_updates) {
    std::cout << update.DebugString() << std::endl;
  }
  std::cout << "--- Write requests (output):" << std::endl;
  if (result.empty()) std::cout << "<empty>" << std::endl << std::endl;
  int i = 0;
  for (const auto& pi_write_request : result) {
    pdpi::WriteRequest pd_write_request;
    const auto& status =
        pdpi::PiWriteRequestToPd(info, pi_write_request, &pd_write_request);
    if (!status.ok()) {
      std::cerr << "Unable to convert WriteRequest from PI to PD." << std::endl;
      return;
    }
    std::cout << "WriteRequest #" << i << std::endl;
    i += 1;
    std::cout << pd_write_request.DebugString() << std::endl;
  }
}

// Takes a set of PD table entries and sorts them
void SortTest(const pdpi::IrP4Info& info, const std::string& test_name,
              const std::vector<std::string> pd_table_entries_strings) {
  // Convert input to PI.
  std::vector<p4::v1::TableEntry> pi_entries;
  std::vector<pdpi::TableEntry> pd_entries;
  for (const auto& pd_entry_string : pd_table_entries_strings) {
    const auto pd_entry =
        gutil::ParseProtoOrDie<pdpi::TableEntry>(pd_entry_string);
    pd_entries.push_back(pd_entry);
    const auto pi_entry_or_status = pdpi::PdTableEntryToPi(info, pd_entry);
    if (!pi_entry_or_status.status().ok()) {
      std::cerr << "Unable to convert TableEntry from PD to PI." << std::endl;
      return;
    }
    const auto& pi_entry = pi_entry_or_status.value();
    pi_entries.push_back(pi_entry);
  }

  // Output input.
  std::cout << TestHeader(absl::StrCat("SortTest: ", test_name)) << std::endl
            << std::endl;
  std::cout << "--- PD entries (input):" << std::endl;
  if (pd_entries.empty()) std::cout << "<empty>" << std::endl << std::endl;
  for (const auto& entry : pd_entries) {
    std::cout << entry.DebugString() << std::endl;
  }

  // Run sorting.
  absl::Status status = pdpi::SortTableEntries(info, pi_entries);
  if (!status.ok()) {
    std::cout << "--- Sorting failed (output):" << std::endl;
    std::cout << status << std::endl;
    return;
  }

  // Output results.
  std::cout << "--- Sorted entries (output):" << std::endl;
  if (pi_entries.empty()) std::cout << "<empty>" << std::endl << std::endl;
  for (const auto& entry : pi_entries) {
    pdpi::TableEntry pd_entry;
    if (!pdpi::PiTableEntryToPd(info, entry, &pd_entry).ok()) {
      std::cerr << "Unable to convert TableEntry from PI to PD." << std::endl;
      return;
    }
    std::cout << pd_entry.DebugString() << std::endl;
  }
}

int main(int argc, char** argv) {
  // Usage: sequencing_test <p4info file>.
  if (argc != 2) {
    std::cerr << "Invalid number of arguments." << std::endl;
    return 1;
  }
  const auto p4info = gutil::ParseProtoFileOrDie<P4Info>(argv[1]);
  const auto status_or_info = pdpi::CreateIrP4Info(p4info);
  if (!status_or_info.status().ok()) {
    std::cerr << "Unable to create IrP4Info." << std::endl;
    return 1;
  }
  const auto& info = status_or_info.value();

  SequenceTest(info, "Empty input", {});
  SequenceTest(info, "Insert(a) -> Insert(a)",
               {R"pb(
                  type: INSERT
                  table_entry {
                    referring_table_entry {
                      match { val: "0x001" }
                      action {
                        referring_action {
                          referring_id_1: "key-a",
                          referring_id_2: "non-existent"
                        }
                      }
                    }
                  }
                )pb",
                R"pb(
                  type: INSERT
                  table_entry {
                    referred_table_entry {
                      match { id: "key-a" }
                      action { do_thing_4 {} }
                    }
                  }
                )pb"});
  SequenceTest(info, "Delete(a) -> Delete(a)",
               {R"pb(
                  type: DELETE
                  table_entry {
                    referring_table_entry {
                      match { val: "0x001" }
                      action {
                        referring_action {
                          referring_id_1: "key-a",
                          referring_id_2: "non-existent"
                        }
                      }
                    }
                  }
                )pb",
                R"pb(
                  type: DELETE
                  table_entry {
                    referred_table_entry {
                      match { id: "key-a" }
                      action { do_thing_4 {} }
                    }
                  }
                )pb"});
  SequenceTest(info,
               "Test case with 1 entry in the first batch and multiple ones in "
               "the second batch. Used to verify the API is stable.",
               {R"pb(
                  type: DELETE
                  table_entry {
                    referring_table_entry {
                      match { val: "0x001" }
                      action {
                        referring_action {
                          referring_id_1: "key-a"
                          referring_id_2: "key-b"
                        }
                      }
                    }
                  }
                )pb",
                R"pb(
                  type: DELETE
                  table_entry {
                    referred_table_entry {
                      match { id: "key-a" }
                      action { do_thing_4 {} }
                    }
                  }
                )pb",
                R"pb(
                  type: DELETE
                  table_entry {
                    referred_table_entry {
                      match { id: "key-b" }
                      action { do_thing_4 {} }
                    }
                  }
                )pb"});
  SequenceTest(info, "Insert(a), Insert(not-a)",
               {R"pb(
                  type: INSERT
                  table_entry {
                    referring_table_entry {
                      match { val: "0x001" }
                      action {
                        referring_action {
                          referring_id_1: "key-a",
                          referring_id_2: "non-existent"
                        }
                      }
                    }
                  }
                )pb",
                R"pb(
                  type: INSERT
                  table_entry {
                    referred_table_entry {
                      match { id: "not-key-a" }
                      action { do_thing_4 {} }
                    }
                  }
                )pb"});
  SequenceTest(
      info, "Insert(a) -> Insert(a), Insert(different table)",
      {R"pb(
         type: INSERT
         table_entry {
           referring_table_entry {
             match { val: "0x001" }
             action {
               referring_action {
                 referring_id_1: "key-a",
                 referring_id_2: "non-existent"
               }
             }
           }
         }
       )pb",
       R"pb(
         type: INSERT
         table_entry {
           referred_table_entry {
             match { id: "key-a" }
             action { do_thing_4 {} }
           }
         }
       )pb",
       R"pb(
         type: INSERT
         table_entry {
           lpm2_table_entry {
             match { ipv6 { value: "ffff::abcd:0:0" prefix_length: 96 } }
             action { NoAction {} }
           }
         }
       )pb"});
  SequenceTest(info, "Insert(a) -> Insert(a), Insert(b) -> Insert(b)",
               {R"pb(
                  type: INSERT
                  table_entry {
                    referring_table_entry {
                      match { val: "0x001" }
                      action {
                        referring_action {
                          referring_id_1: "key-a",
                          referring_id_2: "non-existent"
                        }
                      }
                    }
                  }
                )pb",
                R"pb(
                  type: INSERT
                  table_entry {
                    referred_table_entry {
                      match { id: "key-a" }
                      action { do_thing_4 {} }
                    }
                  }
                )pb",
                R"pb(
                  type: INSERT
                  table_entry {
                    referring_table_entry {
                      match { val: "0x002" }
                      action {
                        referring_action {
                          referring_id_1: "key-b",
                          referring_id_2: "non-existent"
                        }
                      }
                    }
                  }
                )pb",
                R"pb(
                  type: INSERT
                  table_entry {
                    referred_table_entry {
                      match { id: "key-b" }
                      action { do_thing_4 {} }
                    }
                  }
                )pb"});
  SequenceTest(info,
               "Insert(a) -> Insert(a), Insert(a) -> Insert(a) (i.e., two "
               "inserts pointing to the same insert)",
               {R"pb(
                  type: INSERT
                  table_entry {
                    referring_table_entry {
                      match { val: "0x001" }
                      action {
                        referring_action {
                          referring_id_1: "key-a",
                          referring_id_2: "non-existent"
                        }
                      }
                    }
                  }
                )pb",
                R"pb(
                  type: INSERT
                  table_entry {
                    referred_table_entry {
                      match { id: "key-a" }
                      action { do_thing_4 {} }
                    }
                  }
                )pb",
                R"pb(
                  type: INSERT
                  table_entry {
                    referring_table_entry {
                      match { val: "0x002" }
                      action {
                        referring_action {
                          referring_id_1: "key-a",
                          referring_id_2: "non-existent"
                        }
                      }
                    }
                  }
                )pb"});

  SequenceTest(info, "A referring to B using a match field",
               {R"pb(
                  type: INSERT
                  table_entry {
                    referring2_table_entry {
                      match { referring_id: "key-a" }
                      action { do_thing_4 {} }
                    }
                  }
                )pb",
                R"pb(
                  type: INSERT
                  table_entry {
                    referred_table_entry {
                      match { id: "key-a" }
                      action { do_thing_4 {} }
                    }
                  }
                )pb"});

  SortTest(info, "A referring to B",
           {R"pb(
              referring_table_entry {
                match { val: "0x001" }
                action {
                  referring_action {
                    referring_id_1: "key-a",
                    referring_id_2: "non-existent"
                  }
                }
              }
            )pb",
            R"pb(
              referred_table_entry {
                match { id: "key-a" }
                action { do_thing_4 {} }
              }
            )pb"});

  SortTest(info, "A referring to B twice",
           {R"pb(
              referring_table_entry {
                match { val: "0x001" }
                action {
                  referring_action {
                    referring_id_1: "key-a",
                    referring_id_2: "key-a"
                  }
                }
              }
            )pb",
            R"pb(
              referred_table_entry {
                match { id: "key-a" }
                action { do_thing_4 {} }
              }
            )pb"});

  // TODO: Add negative test (where updates and P4Info are out of sync).

  return 0;
}
