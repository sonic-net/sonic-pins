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
#include "gutil/proto.h"
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

using ::gutil::PrintTextProto;
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
    std::cout << PrintTextProto(update) << std::endl;
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
    std::cout << PrintTextProto(pd_write_request) << std::endl;
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
    std::cout << PrintTextProto(entry) << std::endl;
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
    std::cout << PrintTextProto(pd_entry) << std::endl;
  }
}

void GetEntriesUnreachableFromRootsTest(
    const pdpi::IrP4Info& info, const std::string& test_name,
    const std::vector<std::string> pd_table_entry_strings) {
  // Convert input to PI.
  std::vector<p4::v1::TableEntry> pi_entries;
  std::vector<pdpi::TableEntry> pd_entries;
  for (const auto& pd_entry_string : pd_table_entry_strings) {
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
  std::cout << TestHeader(absl::StrCat("GetEntriesUnreachableFromRootsTest: ",
                                       test_name))
            << std::endl
            << std::endl;
  std::cout << "--- PD entries (input):" << std::endl;
  if (pd_entries.empty()) std::cout << "<empty>" << std::endl << std::endl;
  for (const auto& entry : pd_entries) {
    std::cout << PrintTextProto(entry) << std::endl;
  }

  // We use the entry metadata to determine whether to treat it as a root entry
  // or not.
  auto is_root = [](const p4::v1::TableEntry& entry) {
    return entry.metadata() == "Root";
  };

  // Run GetEntriesUnreachableFromRoots.
  auto unreachable_entries =
      pdpi::GetEntriesUnreachableFromRoots(pi_entries, is_root, info);
  if (!unreachable_entries.ok()) {
    std::cout << "--- Getting unreachable entries from roots failed (output):"
              << std::endl;
    std::cout << unreachable_entries.status() << std::endl;
    return;
  }
  std::cout << "--- Unreachable entries from roots (output):" << std::endl;
  if (unreachable_entries->empty()) {
    std::cout << "<empty>" << std::endl << std::endl;
  }

  // Output results.
  for (const auto& entry : *unreachable_entries) {
    pdpi::TableEntry pd_entry;
    if (!pdpi::PiTableEntryToPd(info, entry, &pd_entry).ok()) {
      std::cerr << "Unable to convert TableEntry from PI to PD." << std::endl;
      return;
    }
    std::cout << PrintTextProto(pd_entry) << std::endl;
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

  GetEntriesUnreachableFromRootsTest(info, "Empty input generates no garbage.",
                                     {});

  // Root  Root
  GetEntriesUnreachableFromRootsTest(info, "All root entries means no garbage.",
                                     {
                                         R"pb(
                                           referring_table_entry {
                                             match { val: "0x001" }
                                             action {
                                               referring_action {
                                                 referring_id_1: "key-a",
                                                 referring_id_2: "key-a"
                                               }
                                             }
                                             controller_metadata: "Root"
                                           }
                                         )pb",
                                         R"pb(
                                           referring_table_entry {
                                             match { val: "0x002" }
                                             action {
                                               referring_action {
                                                 referring_id_1: "key-a",
                                                 referring_id_2: "key-b"
                                               }
                                             }
                                             controller_metadata: "Root"
                                           }
                                         )pb",
                                     });

  // Root
  //   |
  // Dependency
  GetEntriesUnreachableFromRootsTest(
      info, "Root referring to the only entry generates no garbage.",
      {
          R"pb(
            referring_table_entry {
              match { val: "0x001" }
              action {
                referring_action {
                  referring_id_1: "key-a",
                  referring_id_2: "key-a"
                }
              }
              controller_metadata: "Root"
            }
          )pb",
          R"pb(
            referred_table_entry {
              match { id: "key-a" }
              action { do_thing_4 {} }
              controller_metadata: "Dependency"
            }
          )pb",
      });

  //    Root
  //   |           \
  // Dependency   Dependency
  GetEntriesUnreachableFromRootsTest(
      info, "Root referring to all dependencies generates no garbage.",
      {
          R"pb(
            referring_table_entry {
              match { val: "0x001" }
              action {
                referring_action {
                  referring_id_1: "key-a",
                  referring_id_2: "key-b"
                }
              }
              controller_metadata: "Root"
            }
          )pb",
          R"pb(
            referred_table_entry {
              match { id: "key-a" }
              action { do_thing_4 {} }
              controller_metadata: "Dependency"
            }
          )pb",
          R"pb(
            referred_table_entry {
              match { id: "key-b" }
              action { do_thing_4 {} }
              controller_metadata: "Dependency"
            }
          )pb",
      });

  // Root
  //   |
  // Dependency   Garbage
  GetEntriesUnreachableFromRootsTest(info, "Garbage is unreachable.",
                                     {
                                         R"pb(
                                           referring_table_entry {
                                             match { val: "0x001" }
                                             action {
                                               referring_action {
                                                 referring_id_1: "key-a",
                                                 referring_id_2: "key-b"
                                               }
                                             }
                                             controller_metadata: "Root"
                                           }
                                         )pb",
                                         R"pb(
                                           referred_table_entry {
                                             match { id: "key-a" }
                                             action { do_thing_4 {} }
                                             controller_metadata: "Dependency"
                                           }
                                         )pb",
                                         R"pb(
                                           referred_table_entry {
                                             match { id: "key-c" }
                                             action { do_thing_4 {} }
                                             controller_metadata: "Garbage"
                                           }
                                         )pb",
                                     });
  // Root
  //   |
  // Dependency   Root
  GetEntriesUnreachableFromRootsTest(info,
                                     "Root referring to dependency and a "
                                     "standalone Root generates no garbage.",
                                     {
                                         R"pb(
                                           referring_table_entry {
                                             match { val: "0x001" }
                                             action {
                                               referring_action {
                                                 referring_id_1: "key-a",
                                                 referring_id_2: "key-b"
                                               }
                                             }
                                             controller_metadata: "Root"
                                           }
                                         )pb",
                                         R"pb(
                                           referred_table_entry {
                                             match { id: "key-a" }
                                             action { do_thing_4 {} }
                                             controller_metadata: "Dependency"
                                           }
                                         )pb",
                                         R"pb(
                                           referring_table_entry {
                                             match { val: "0x001" }
                                             action {
                                               referring_action {
                                                 referring_id_1: "non-exist",
                                                 referring_id_2: "non-exist"
                                               }
                                             }
                                             controller_metadata: "Root"
                                           }
                                         )pb",
                                     });
  // Garbage   Garbage
  GetEntriesUnreachableFromRootsTest(info, "All entries are garbage.",
                                     {
                                         R"pb(
                                           referred_table_entry {
                                             match { id: "key-a" }
                                             action { do_thing_4 {} }
                                             controller_metadata: "Garbage"
                                           }
                                         )pb",
                                         R"pb(
                                           referred_table_entry {
                                             match { id: "key-c" }
                                             action { do_thing_4 {} }
                                             controller_metadata: "Garbage"
                                           }
                                         )pb",
                                     });

  // Root  Root
  //  \     /
  //  Dependency
  GetEntriesUnreachableFromRootsTest(
      info, "Two roots referring to one dependency generates no garbage.",
      {
          R"pb(
            referring_table_entry {
              match { val: "0x001" }
              action {
                referring_action {
                  referring_id_1: "key-a",
                  referring_id_2: "key-a"
                }
              }
              controller_metadata: "Root"
            }
          )pb",
          R"pb(
            referring_table_entry {
              match { val: "0x002" }
              action {
                referring_action {
                  referring_id_1: "key-a",
                  referring_id_2: "key-a"
                }
              }
              controller_metadata: "Root"
            }
          )pb",
          R"pb(
            referred_table_entry {
              match { id: "key-a" }
              action { do_thing_4 {} }
              controller_metadata: "Dependency"
            }
          )pb",
      });

  // Root
  //   |
  // Child dependency
  //   |
  // Grand child Dependency
  GetEntriesUnreachableFromRootsTest(
      info, "Children and grand children of the root are not garbage.",
      {
          R"pb(
            referring_to_referring2_table_entry {
              match { referring2_table_id: "key-a" }
              action { do_thing_4 {} }
              controller_metadata: "Root"
            }
          )pb",
          R"pb(
            referring2_table_entry {
              match { referring_id: "key-a" }
              action { do_thing_4 {} }
              controller_metadata: "Child dependency"
            })pb",
          R"pb(
            referred_table_entry {
              match { id: "key-a" }
              action { do_thing_4 {} }
              controller_metadata: "Grand child Dependency"
            }
          )pb",
      });
  // NonRoot garbage
  //        |
  // NonRoot garbage
  GetEntriesUnreachableFromRootsTest(
      info, "NonRoot referring to other NonRoot is garbage.",
      {
          R"pb(
            referred_table_entry {
              match { id: "key-a" }
              action { do_thing_4 {} }
              controller_metadata: "NonRoot garbage"
            }
          )pb",
          R"pb(
            referring_table_entry {
              match { val: "0x001" }
              action {
                referring_action {
                  referring_id_1: "key-a"
                  referring_id_2: "non-existent"
                }
              }
              controller_metadata: "NonRoot garbage"
            }
          )pb",
      });

  // Root
  //   |
  // Child dependency          NonRoot garbage
  //   |                        /
  // Grand child Dependency
  GetEntriesUnreachableFromRootsTest(
      info,
      "NonRoot referring to other dependency is garbage, but other "
      "dependencies that are referred by a root won't be removed.",
      {
          R"pb(
            referring_to_referring2_table_entry {
              match { referring2_table_id: "key-a" }
              action { do_thing_4 {} }
              controller_metadata: "Root"
            }
          )pb",
          R"pb(
            referring2_table_entry {
              match { referring_id: "key-a" }
              action { do_thing_4 {} }
              controller_metadata: "Child dependency"
            })pb",
          R"pb(
            referred_table_entry {
              match { id: "key-a" }
              action { do_thing_4 {} }
              controller_metadata: "Grand child Dependency"
            }
          )pb",
          R"pb(
            referring_table_entry {
              match { val: "0x001" }
              action {
                referring_action {
                  referring_id_1: "key-a"
                  referring_id_2: "non-existent"
                }
              }
              controller_metadata: "NonRoot garbage"
            }
          )pb",
      });

  // Conglomeration of entries, courtesy of dilo@.
  // Root
  //   |
  // Dependency    NonRoot Garbage  NonRoot Garbage        Root
  //   |             /                      |                |
  // Dependency                     NonRoot Garbage        Dependency      Root
  GetEntriesUnreachableFromRootsTest(
      info, "Conglomeration test.",
      {
          R"pb(
            referring_to_referring2_table_entry {
              match { referring2_table_id: "key-a" }
              action { do_thing_4 {} }
              controller_metadata: "Root"
            }
          )pb",
          R"pb(
            referring2_table_entry {
              match { referring_id: "key-a" }
              action { do_thing_4 {} }
              controller_metadata: "Child dependency"
            })pb",
          R"pb(
            referred_table_entry {
              match { id: "key-a" }
              action { do_thing_4 {} }
              controller_metadata: "Grand child Dependency"
            }
          )pb",
          R"pb(
            referring_table_entry {
              match { val: "0x001" }
              action {
                referring_action {
                  referring_id_1: "key-a"
                  referring_id_2: "non-existent"
                }
              }
              controller_metadata: "NonRoot garbage"
            }
          )pb",
          R"pb(
            referred_table_entry {
              match { id: "key-b" }
              action { do_thing_4 {} }
              controller_metadata: "NonRoot garbage"
            }
          )pb",
          R"pb(
            referring_table_entry {
              match { val: "0x001" }
              action {
                referring_action {
                  referring_id_1: "key-b"
                  referring_id_2: "non-existent"
                }
              }
              controller_metadata: "NonRoot garbage"
            }
          )pb",
          R"pb(
            referring_table_entry {
              match { val: "0x001" }
              action {
                referring_action {
                  referring_id_1: "key-c",
                  referring_id_2: "non-exist"
                }
              }
              controller_metadata: "Root"
            }
          )pb",
          R"pb(
            referred_table_entry {
              match { id: "key-c" }
              action { do_thing_4 {} }
              controller_metadata: "Dependency"
            }
          )pb",
          R"pb(
            referring_table_entry {
              match { val: "0x001" }
              action {
                referring_action {
                  referring_id_1: "non-exist",
                  referring_id_2: "non-exist"
                }
              }
              controller_metadata: "Root"
            }
          )pb",
      });
  // TODO: Add negative test (where updates and P4Info are out of
  // sync).
  return 0;
}  // NOLINT(readability/fn_size)
