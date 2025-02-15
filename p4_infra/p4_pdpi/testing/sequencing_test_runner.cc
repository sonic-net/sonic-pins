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

#include <cmath>
#include <iostream>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/substitute.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/testing.h"
#include "gutils/status_matchers.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/pd.h"
#include "p4_infra/p4_pdpi/sequencing.h"
#include "p4_infra/p4_pdpi/testing/main_p4_pd.pb.h"
#include "p4_infra/p4_pdpi/testing/test_helper.h"

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
      std::cerr << "Unable to convert Update from PD to PI."
                << pi_update_or_status.status() << std::endl;
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
      std::cerr << "Unable to convert WriteRequest from PI to PD." << status
                << std::endl;
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
  std::vector<p4::v1::Entity> pi_entities;
  std::vector<pdpi::TableEntry> pd_entries;
  for (const auto& pd_entry_string : pd_table_entries_strings) {
    const auto pd_entry =
        gutil::ParseProtoOrDie<pdpi::TableEntry>(pd_entry_string);
    pd_entries.push_back(pd_entry);
    const auto pi_entity_or_status =
        pdpi::PdTableEntryToPiEntity(info, pd_entry);
    if (!pi_entity_or_status.status().ok()) {
      std::cerr << "Unable to convert PD TableEntry to PI Entity."
                << pi_entity_or_status.status() << std::endl;
      return;
    }
    pi_entities.push_back(*pi_entity_or_status);
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
  absl::Status status = pdpi::StableSortEntities(info, pi_entities);
  if (!status.ok()) {
    std::cout << "--- Sorting failed (output):" << std::endl;
    std::cout << status << std::endl;
    return;
  }

  // Output results.
  std::cout << "--- Sorted entities (output):" << std::endl;
  if (pi_entities.empty()) std::cout << "<empty>" << std::endl << std::endl;
  for (const auto& entry : pi_entities) {
    pdpi::TableEntry pd_entry;
    if (absl::Status status =
            pdpi::PiEntityToPdTableEntry(info, entry, &pd_entry);
        !status.ok()) {
      std::cerr << "Unable to convert PI Entity to PD TableEntry." << status
                << std::endl;
      return;
    }
    std::cout << PrintTextProto(pd_entry) << std::endl;
  }
}

void GetEntriesUnreachableFromRootsTest(
    const pdpi::IrP4Info& info, const std::string& test_name,
    const std::vector<std::string> pd_table_entry_strings) {
  // Convert input to PI.
  std::vector<p4::v1::Entity> pi_entities;
  std::vector<pdpi::TableEntry> pd_entries;
  for (const auto& pd_entry_string : pd_table_entry_strings) {
    const auto pd_entry =
        gutil::ParseProtoOrDie<pdpi::TableEntry>(pd_entry_string);
    pd_entries.push_back(pd_entry);
    const auto pi_entity = pdpi::PdTableEntryToPiEntity(info, pd_entry);
    if (!pi_entity.status().ok()) {
      std::cerr << "Unable to convert TableEntry from PD to PI."
                << pi_entity.status() << std::endl;
      return;
    }
    pi_entities.push_back(*pi_entity);
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
  // TODO: b/316634574 - Remove multicast check once PDPI translation propagates
  // multicast metadata.
  auto is_root = [](const p4::v1::Entity& entity) {
    return entity.table_entry().metadata() == "Root" ||
           entity.packet_replication_engine_entry().has_multicast_group_entry();
  };

  // Run GetEntriesUnreachableFromRoots.
  absl::StatusOr<std::vector<p4::v1::Entity>> unreachable_entities =
      pdpi::GetEntitiesUnreachableFromRoots(pi_entities, is_root, info);
  if (!unreachable_entities.ok()) {
    std::cout << "--- Getting unreachable entities from roots failed (output):"
              << std::endl;
    std::cout << unreachable_entities.status() << std::endl;
    return;
  }
  std::cout << "--- Unreachable entries from roots (output):" << std::endl;
  if (unreachable_entities->empty()) {
    std::cout << "<empty>" << std::endl << std::endl;
  }

  // Output results.
  for (const auto& entity : *unreachable_entities) {
    pdpi::TableEntry pd_entry;
    if (absl::Status status =
            pdpi::PiEntityToPdTableEntry(info, entity, &pd_entry);
        !status.ok()) {
      std::cerr << "Unable to convert Entity from PI to PD." << status
                << std::endl;
      return;
    }
    std::cout << PrintTextProto(pd_entry) << std::endl;
  }
}

void ExtractWriteRequestsInvalidInputTest() {
  p4::v1::WriteRequest write_request = WriteRequest();
  write_request.add_updates();
  ASSERT_FALSE(pdpi::ExtractWriteRequests(std::move(write_request), 0).ok());

  write_request = WriteRequest();
  write_request.add_updates();
  ASSERT_FALSE(pdpi::ExtractWriteRequests(std::move(write_request), -1).ok());
}

void ExtractWriteRequestsOmitMaximumBatchSizeTest() {
  p4::v1::WriteRequest write_request = WriteRequest();
  write_request.add_updates();
  absl::StatusOr<std::vector<p4::v1::WriteRequest>> result =
      pdpi::ExtractWriteRequests(std::move(write_request), std::nullopt);
  ASSERT_OK(result);
  ASSERT_EQ(result->size(), 1);
}

void ExtractWriteRequestPreservesFieldsTest() {
  p4::v1::WriteRequest write_request = WriteRequest();
  for (int i = 0; i < 11; i++) {
    write_request.add_updates();
  }
  ::p4::v1::Uint128 election_id;
  election_id.set_high(100);
  election_id.set_low(10);
  *write_request.mutable_election_id() = election_id;
  write_request.set_device_id(123);
  write_request.set_role("role");

  absl::StatusOr<std::vector<p4::v1::WriteRequest>> result =
      pdpi::ExtractWriteRequests(std::move(write_request), 2);

  ASSERT_EQ(result->size(), 6);
  for (int i = 0; i < result->size(); i++) {
    EXPECT_EQ(result->at(i).election_id().high(), election_id.high());
    EXPECT_EQ(result->at(i).election_id().low(), election_id.low());
    EXPECT_EQ(result->at(i).device_id(), 123);
    EXPECT_EQ(result->at(i).role(), "role");
  }
}

void ExtractWriteRequestsTest(int update_size, int max_write_request_size) {
  std::vector<p4::v1::Update> updates;
  updates.reserve(update_size);
  for (int i = 0; i < update_size; i++) {
    updates.push_back(gutil::ParseProtoOrDie<p4::v1::Update>(
        absl::Substitute(R"pb(
                           type: INSERT
                           entity {
                             table_entry {
                               metadata: "$0"
                               table_id: 1
                               match {
                                 field_id: 1
                                 exact { value: "\123\"" }
                               }
                             }
                           }
                         )pb",
                         i)));
  }
  p4::v1::WriteRequest write_request = WriteRequest();
  // Add `update_size` number of updates to the write request.
  for (int i = 0; i < update_size; i++) {
    *write_request.add_updates() = updates[i];
  }

  absl::StatusOr<std::vector<p4::v1::WriteRequest>> result =
      pdpi::ExtractWriteRequests(std::move(write_request),
                                 max_write_request_size);
  if (max_write_request_size < 1) {
    std::cout << TestHeader(absl::StrCat(
                     "SplitUpWriteRequestTest: ",
                     "max_write_request_size smaller than 1 results in error."))
              << "\n"
              << result.status().message() << "\n\n";
    return;
  }
  ASSERT_OK(result);
  if (update_size < max_write_request_size) {
    std::cout << TestHeader(
                     absl::StrCat("SplitUpWriteRequestTest: ",
                                  "No splitting if update_size is "
                                  "smaller than max_write_request_size."))
              << "\n";
  } else {
    std::cout << TestHeader(absl::StrCat("SplitUpWriteRequestTest: ",
                                         "Updates split up to have a size of "
                                         "at most max_write_request_size."))
              << "\n";
  }
  std::cout << "-- SplitUpWriteRequest input:\nupdates size: " << update_size
            << " max update size: " << max_write_request_size;
  std::cout << "\n\n-- SplitUpWriteRequest output:\n";

  int expected_size = ceil((float)update_size / (float)max_write_request_size);
  if (result->size() != expected_size) {
    std::cout << "The number of requests after splitting doesn't equal to the "
                 "size dictated by the formula. Expected: "
              << expected_size << " Actual: " << result->size() << "\n";
  }

  std::cout << "number of write requests: " << result->size() << "\n";
  int i = 0;
  for (const auto& write_request : *result) {
    for (const auto& update : write_request.updates()) {
      if (update.entity().table_entry().metadata() != absl::StrCat(i)) {
        std::cout << "spliting up the write request scrambled the order of "
                     "updates\n";
      }
      i++;
    }
  }
}

void ExtractWriteRequestsTests() {
  ExtractWriteRequestsInvalidInputTest();
  ExtractWriteRequestsOmitMaximumBatchSizeTest();
  ExtractWriteRequestPreservesFieldsTest();
  ExtractWriteRequestsTest(/*update_size=*/1, /*max_write_request_size=*/0);
  ExtractWriteRequestsTest(/*update_size=*/1, /*max_write_request_size=*/1);
  ExtractWriteRequestsTest(/*update_size=*/1, /*max_write_request_size=*/2);
  ExtractWriteRequestsTest(/*update_size=*/6, /*max_write_request_size=*/2);
  ExtractWriteRequestsTest(/*update_size=*/123, /*max_write_request_size=*/55);
  ExtractWriteRequestsTest(/*update_size=*/123, /*max_write_request_size=*/5);
}

void RunSequenceTests(const pdpi::IrP4Info& info) {
  SequenceTest(info, "Empty input", {});

  // Test entries that have reference relationships are properly sequenced.
  // A note on notation: A -> B means B is dependent on A and A needs to be
  // sequenced ahead of B. The arrow shows the order entries need to be
  // sequenced.
  SequenceTest(info,
               "INSERT EntryWithOneKey{key-a} -> "
               "INSERT EntryThatRefersTo{key-a}",
               {
                   R"pb(
                     type: INSERT
                     table_entry {
                       referring_by_action_table_entry {
                         match { val: "0x001" }
                         action {
                           referring_to_one_match_field_action {
                             referring_id_1: "key-a",
                           }
                         }
                       }
                     }
                   )pb",
                   R"pb(
                     type: INSERT
                     table_entry {
                       one_match_field_table_entry {
                         match { id: "key-a" }
                         action { do_thing_4 {} }
                       }
                     }
                   )pb",
               });
  SequenceTest(
      info, "DELETE EntryThatRefersTo{key-a} -> DELETE EntryWithOneKey{key-a}",
      {
          R"pb(
            type: DELETE
            table_entry {
              one_match_field_table_entry {
                match { id: "key-a" }
                action { do_thing_4 {} }
              }
            }
          )pb",
          R"pb(
            type: DELETE
            table_entry {
              referring_by_action_table_entry {
                match { val: "0x001" }
                action {
                  referring_to_one_match_field_action {
                    referring_id_1: "key-a",
                  }
                }
              }
            }
          )pb",
      });

  // TODO re-enable after adding double dependencies.
  // SequenceTest(
  //  info,
  //  "INSERT EntryWithOneKey{key-a} -> INSERT EntryThatRefersTo{key-a, 0x002}",
  //     {R"pb(
  //        type: INSERT
  //        table_entry {
  //          referring_by_action_table_entry {
  //            match { val: "0x001" }
  //            action {
  //              referring_to_two_match_fields_action {
  //                referring_id_1: "key-a",
  //                referring_id_2: "0x002",
  //              }
  //            }
  //          }
  //        }
  //      )pb",
  //      R"pb(
  //        type: INSERT
  //        table_entry {
  //          one_match_field_table_entry {
  //            match { id: "key-a" }
  //            action { do_thing_4 {} }
  //          }
  //        }
  //      )pb"});
  SequenceTest(info,
               "INSERT EntryWithTwoKeys{key-a, 0x002} -> INSERT "
               "EntryThatRefersTo{key-a, 0x002}",
               {
                   R"pb(
                     type: INSERT
                     table_entry {
                       referring_by_action_table_entry {
                         match { val: "0x001" }
                         action {
                           referring_to_two_match_fields_action {
                             referring_id_1: "key-a",
                             referring_id_2: "0x002",
                           }
                         }
                       }
                     }
                   )pb",
                   R"pb(
                     type: INSERT
                     table_entry {
                       two_match_fields_table_entry {
                         match { id_1: "key-a", id_2: "0x002" }
                         action { do_thing_4 {} }
                       }
                     }
                   )pb",
               });
  SequenceTest(info,
               "DELETE EntryThatRefersTo{key-a, 0x002} -> DELETE "
               "EntryWithTwoKeys{key-a, 0x002}",
               {
                   R"pb(
                     type: DELETE
                     table_entry {
                       two_match_fields_table_entry {
                         match { id_1: "key-a", id_2: "0x002" }
                         action { do_thing_4 {} }
                       }
                     }
                   )pb",
                   R"pb(
                     type: DELETE
                     table_entry {
                       referring_by_action_table_entry {
                         match { val: "0x001" }
                         action {
                           referring_to_two_match_fields_action {
                             referring_id_1: "key-a",
                             referring_id_2: "0x002",
                           }
                         }
                       }
                     }
                   )pb",
               });

  // Sequence tests to test entries that do not refer to another entry by
  // any of its match field will not be sequenced.
  SequenceTest(info,
               "INSERT EntryThatRefersTo{key-a, 0x002}, INSERT "
               "EntryWithTwoKeys{key-c, 0x004}",
               {
                   R"pb(
                     type: INSERT
                     table_entry {
                       referring_by_action_table_entry {
                         match { val: "0x001" }
                         action {
                           referring_to_two_match_fields_action {
                             referring_id_1: "key-a",
                             referring_id_2: "0x002",
                           }
                         }
                       }
                     }
                   )pb",
                   R"pb(
                     type: INSERT
                     table_entry {
                       two_match_fields_table_entry {
                         match { id_1: "key-c", id_2: "0x004" }
                         action { do_thing_4 {} }
                       }
                     }
                   )pb",
               });

  SequenceTest(info,
               "DELETE EntryThatRefersTo{key-a, 0x002}, DELETE "
               "EntryWithTwoKeys{key-c, 0x004}",
               {
                   R"pb(
                     type: DELETE
                     table_entry {
                       referring_by_action_table_entry {
                         match { val: "0x001" }
                         action {
                           referring_to_two_match_fields_action {
                             referring_id_1: "key-a",
                             referring_id_2: "0x002",
                           }
                         }
                       }
                     }
                   )pb",
                   R"pb(
                     type: DELETE
                     table_entry {
                       two_match_fields_table_entry {
                         match { id_1: "key-c", id_2: "0x004" }
                         action { do_thing_4 {} }
                       }
                     }
                   )pb",
               });

  // Sequence tests to test entries that partially refer to another entry
  // will not be sequenced.
  SequenceTest(info,
               "[INCORRECT due to false dependency] INSERT "
               "EntryThatRefersTo{key-a, 0x002}, INSERT "
               "EntryWithTwoKeys{key-a, 0x004} should be in a single batch and "
               "no change in orders",
               {
                   R"pb(
                     type: INSERT
                     table_entry {
                       referring_by_action_table_entry {
                         match { val: "0x001" }
                         action {
                           referring_to_two_match_fields_action {
                             referring_id_1: "key-a",
                             referring_id_2: "0x002",
                           }
                         }
                       }
                     }
                   )pb",
                   R"pb(
                     type: INSERT
                     table_entry {
                       two_match_fields_table_entry {
                         match { id_1: "key-a", id_2: "0x004" }
                         action { do_thing_4 {} }
                       }
                     }
                   )pb",
               });

  SequenceTest(info,
               "[INCORRECT due to false dependency] DELETE "
               "EntryWithTwoKeys{key-a, 0x004}, DELETE "
               "EntryThatRefersTo{key-a, 0x002} should be in a single batch no "
               "change in orders",
               {
                   R"pb(
                     type: DELETE
                     table_entry {
                       two_match_fields_table_entry {
                         match { id_1: "key-a", id_2: "0x004" }
                         action { do_thing_4 {} }
                       }
                     }
                   )pb",
                   R"pb(
                     type: DELETE
                     table_entry {
                       referring_by_action_table_entry {
                         match { val: "0x001" }
                         action {
                           referring_to_two_match_fields_action {
                             referring_id_1: "key-a",
                             referring_id_2: "0x002",
                           }
                         }
                       }
                     }
                   )pb",
               });

  // test orders are stable among entries that don't have reference
  // relationships.
  SequenceTest(info,
               "[INCORRECT due to false dependency] INSERT Entries that don't "
               "refer to each other should be in one batch and maintain the "
               "original orders.",
               {
                   R"pb(
                     type: INSERT
                     table_entry {
                       referring_by_action_table_entry {
                         match { val: "0x001" }
                         action {
                           referring_to_two_match_fields_action {
                             referring_id_1: "key-a"
                             referring_id_2: "0x002"
                           }
                         }
                       }
                     }
                   )pb",
                   R"pb(
                     type: INSERT
                     table_entry {
                       two_match_fields_table_entry {
                         match { id_1: "key-a", id_2: "0x003" }
                         action { do_thing_4 {} }
                       }
                     }
                   )pb",
                   R"pb(
                     type: INSERT
                     table_entry {
                       one_match_field_table_entry {
                         match { id: "key-c" }
                         action { do_thing_4 {} }
                       }
                     }
                   )pb",
               });
  SequenceTest(info,
               "[INCORRECT due to false dependency] DELETE Entries that don't "
               "refer to each other should be in one batch and maintain the "
               "original orders.",
               {
                   R"pb(
                     type: DELETE
                     table_entry {
                       referring_by_action_table_entry {
                         match { val: "0x001" }
                         action {
                           referring_to_two_match_fields_action {
                             referring_id_1: "key-a"
                             referring_id_2: "0x002"
                           }
                         }
                       }
                     }
                   )pb",
                   R"pb(
                     type: DELETE
                     table_entry {
                       two_match_fields_table_entry {
                         match { id_1: "key-a", id_2: "0x003" }
                         action { do_thing_4 {} }
                       }
                     }
                   )pb",
                   R"pb(
                     type: DELETE
                     table_entry {
                       one_match_field_table_entry {
                         match { id: "key-c" }
                         action { do_thing_4 {} }
                       }
                     }
                   )pb",
               });

  // Tests a mix of referred and referring entries and other entries.
  SequenceTest(
      info,
      "INSERT EntryWithOneKey{key-a} ->"
      "INSERT EntryThatRefersTo{key-a} , another entry",
      {
          R"pb(
            type: INSERT
            table_entry {
              referring_by_action_table_entry {
                match { val: "0x001" }
                action {
                  referring_to_one_match_field_action {
                    referring_id_1: "key-a",
                  }
                }
              }
            }
          )pb",
          R"pb(
            type: INSERT
            table_entry {
              one_match_field_table_entry {
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
          )pb",
      });
  SequenceTest(info,
               "INSERT EntryWithOneKey{key-a} -> INSERT"
               "EntryThatRefersTo{key-a} ,"
               "INSERT EntryWithOneKey{key-b} -> INSERT"
               "EntryThatRefersTo{key-b}",
               {
                   R"pb(
                     type: INSERT
                     table_entry {
                       referring_by_action_table_entry {
                         match { val: "0x001" }
                         action {
                           referring_to_one_match_field_action {
                             referring_id_1: "key-a",
                           }
                         }
                       }
                     }
                   )pb",
                   R"pb(
                     type: INSERT
                     table_entry {
                       one_match_field_table_entry {
                         match { id: "key-a" }
                         action { do_thing_4 {} }
                       }
                     }
                   )pb",
                   R"pb(
                     type: INSERT
                     table_entry {
                       referring_by_action_table_entry {
                         match { val: "0x002" }
                         action {
                           referring_to_one_match_field_action {
                             referring_id_1: "key-b",
                           }
                         }
                       }
                     }
                   )pb",
                   R"pb(
                     type: INSERT
                     table_entry {
                       one_match_field_table_entry {
                         match { id: "key-b" }
                         action { do_thing_4 {} }
                       }
                     }
                   )pb",
               });

  SequenceTest(info,
               "INSERT EntryThatRefersTo{key-a}"
               "<- INSERT EntryWithOneKey{key-a} -> "
               "INSERT EntryThatRefersTo{key-a}. Two INSERT "
               "refers to the same referred entry.",
               {
                   R"pb(
                     type: INSERT
                     table_entry {
                       referring_by_action_table_entry {
                         match { val: "0x001" }
                         action {
                           referring_to_one_match_field_action {
                             referring_id_1: "key-a",
                           }
                         }
                       }
                     }
                   )pb",
                   R"pb(
                     type: INSERT
                     table_entry {
                       one_match_field_table_entry {
                         match { id: "key-a" }
                         action { do_thing_4 {} }
                       }
                     }
                   )pb",
                   R"pb(
                     type: INSERT
                     table_entry {
                       referring_by_action_table_entry {
                         match { val: "0x002" }
                         action {
                           referring_to_one_match_field_action {
                             referring_id_1: "key-a",
                           }
                         }
                       }
                     }
                   )pb",
               });

  SequenceTest(
      info, "referring via match fields for INSERT",
      {
          R"pb(
            type: INSERT
            table_entry {
              referring_by_match_field_table_entry {
                match { referring_id_1: "key-a" referring_id_2: "0x001" }
                action { do_thing_4 {} }
              }
            }
          )pb",
          R"pb(
            type: INSERT
            table_entry {
              two_match_fields_table_entry {
                match { id_1: "key-a", id_2: "0x001" }
                action { do_thing_4 {} }
              }
            }
          )pb",
      });
  SequenceTest(
      info, "referring via match fields for DELETE",
      {
          R"pb(
            type: DELETE
            table_entry {
              two_match_fields_table_entry {
                match { id_1: "key-a", id_2: "0x001" }
                action { do_thing_4 {} }
              }
            }
          )pb",
          R"pb(
            type: DELETE
            table_entry {
              referring_by_match_field_table_entry {
                match { referring_id_1: "key-a" referring_id_2: "0x001" }
                action { do_thing_4 {} }
              }
            }
          )pb",
      });
}  // NOLINT(readability/fn_size)

void RunSortTests(const pdpi::IrP4Info& info) {
  SortTest(info, "Empty input", {});

  // Test entries that have reference relationships are properly sorted.
  // A note on notation: A -> B means that A should be sorted ahead of B. E.g.
  // because B may be dependent on A.
  SortTest(info,
           "EntryWithOneKey{key-a} -> "
           "EntryThatRefersTo{key-a}",
           {
               R"pb(
                 referring_by_action_table_entry {
                   match { val: "0x001" }
                   action {
                     referring_to_one_match_field_action {
                       referring_id_1: "key-a",
                     }
                   }
                 }
               )pb",
               R"pb(
                 one_match_field_table_entry {
                   match { id: "key-a" }
                   action { do_thing_4 {} }
                 }
               )pb",
           });

  SortTest(info, "EntryWithOneKey{key-a} -> EntryThatRefersTo{key-a, 0x002}",
           {R"pb(
              referring_by_action_table_entry {
                match { val: "0x001" }
                action {
                  referring_to_two_match_fields_action {
                    referring_id_1: "key-a",
                    referring_id_2: "0x002",
                  }
                }
              }
            )pb",
            R"pb(
              one_match_field_table_entry {
                match { id: "key-a" }
                action { do_thing_4 {} }
              }
            )pb"});
  SortTest(info,
           "EntryWithTwoKeys{key-a, 0x002} -> EntryThatRefersTo{key-a, 0x002}",
           {
               R"pb(
                 referring_by_action_table_entry {
                   match { val: "0x001" }
                   action {
                     referring_to_two_match_fields_action {
                       referring_id_1: "key-a",
                       referring_id_2: "0x002",
                     }
                   }
                 }
               )pb",
               R"pb(
                 two_match_fields_table_entry {
                   match { id_1: "key-a", id_2: "0x002" }
                   action { do_thing_4 {} }
                 }
               )pb",
           });

  // Sorted even if the entries don't necessarily refer to each other.
  SortTest(info,
           "EntryThatRefersTo{key-a, 0x002} -> EntryWithTwoKeys{key-c, 0x004}",
           {
               R"pb(
                 referring_by_action_table_entry {
                   match { val: "0x001" }
                   action {
                     referring_to_two_match_fields_action {
                       referring_id_1: "key-a",
                       referring_id_2: "0x002",
                     }
                   }
                 }
               )pb",
               R"pb(
                 two_match_fields_table_entry {
                   match { id_1: "key-c", id_2: "0x004" }
                   action { do_thing_4 {} }
                 }
               )pb",
           });

  SortTest(info, "Entries at same rank should maintain the original order.",
           {
               R"pb(
                 referring_by_action_table_entry {
                   match { val: "0x001" }
                   action {
                     referring_to_two_match_fields_action {
                       referring_id_1: "key-a"
                       referring_id_2: "0x002"
                     }
                   }
                 }
               )pb",
               R"pb(
                 packet_count_and_meter_table_entry {
                   match { ipv4 { value: "16.36.50.0" prefix_length: 24 } }
                   action { packet_count_and_meter {} }
                 }
               )pb",
           });

  // Tests a mix of referred and referring entries and other entries.
  SortTest(info,
           "EntryWithOneKey{key-a} -> EntryThatRefersTo{key-a} , another entry",
           {
               R"pb(
                 lpm2_table_entry {
                   match { ipv6 { value: "ffff::abcd:0:0" prefix_length: 96 } }
                   action { NoAction {} }
                 }
               )pb",
               R"pb(
                 referring_by_action_table_entry {
                   match { val: "0x001" }
                   action {
                     referring_to_one_match_field_action {
                       referring_id_1: "key-a",
                     }
                   }
                 }
               )pb",
               R"pb(
                 one_match_field_table_entry {
                   match { id: "key-a" }
                   action { do_thing_4 {} }
                 }
               )pb",
           });
  SortTest(info,
           "EntryWithOneKey{key-a} -> EntryThatRefersTo{key-a} ,"
           "EntryWithOneKey{key-b} -> EntryThatRefersTo{key-b}",
           {
               R"pb(
                 referring_by_action_table_entry {
                   match { val: "0x001" }
                   action {
                     referring_to_one_match_field_action {
                       referring_id_1: "key-a",
                     }
                   }
                 }
               )pb",
               R"pb(
                 one_match_field_table_entry {
                   match { id: "key-a" }
                   action { do_thing_4 {} }
                 }
               )pb",
               R"pb(
                 referring_by_action_table_entry {
                   match { val: "0x001" }
                   action {
                     referring_to_two_match_fields_action {
                       referring_id_1: "key-a",
                       referring_id_2: "0x002",
                     }
                   }
                 }
               )pb",
               R"pb(
                 two_match_fields_table_entry {
                   match { id_1: "key-c", id_2: "0x004" }
                   action { do_thing_4 {} }
                 }
               )pb",
           });

  SortTest(
      info,
      "two_match_fields_table_entry -> referring_by_match_field_table_entry",
      {
          R"pb(
            referring_by_match_field_table_entry {
              match { referring_id_1: "key-a" referring_id_2: "0x001" }
              action { do_thing_4 {} }
            }
          )pb",
          R"pb(
            two_match_fields_table_entry {
              match { id_1: "key-a", id_2: "0x001" }
              action { do_thing_4 {} }
            }
          )pb",
      });
}  // NOLINT(readability/fn_size)

void RunGetEntriesUnreachableFromRootsTests(const pdpi::IrP4Info& info) {
  GetEntriesUnreachableFromRootsTest(info, "Empty input generates no garbage.",
                                     {});

  // Root  Root
  GetEntriesUnreachableFromRootsTest(
      info, "All root entries means no garbage.",
      {
          R"pb(
            referring_by_action_table_entry {
              match { val: "0x001" }
              action {
                referring_to_two_match_fields_action {
                  referring_id_1: "key-a",
                  referring_id_2: "0x003"
                }
              }
              controller_metadata: "Root"
            }
          )pb",
          R"pb(
            referring_by_action_table_entry {
              match { val: "0x002" }
              action {
                referring_to_two_match_fields_action {
                  referring_id_1: "key-a",
                  referring_id_2: "0x002"
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
            referring_by_action_table_entry {
              match { val: "0x001" }
              action {
                referring_to_one_match_field_action {
                  referring_id_1: "key-a",
                }
              }
              controller_metadata: "Root"
            }
          )pb",
          R"pb(
            one_match_field_table_entry {
              match { id: "key-a" }
              action { do_thing_4 {} }
              controller_metadata: "Dependency"
            }
          )pb",
      });

  //    Root
  //   |           \
  // Dependency   Dependency
  // TODO re-enable after adding double dependencies.
  // GetEntriesUnreachableFromRootsTest(
  //     info, "Root referring to all dependencies generates no garbage.",
  //     {
  //         R"pb(
  //           referring_by_action_table_entry {
  //             match { val: "0x001" }
  //             action {
  //               referring_to_two_match_fields_action {
  //                 referring_id_1: "key-a",
  //                 referring_id_2: "0x002"
  //               }
  //             }
  //             controller_metadata: "Root"
  //           }
  //         )pb",
  //         R"pb(
  //           one_match_field_table_entry {
  //             match { id: "key-a" }
  //             action { do_thing_4 {} }
  //             controller_metadata: "Dependency"
  //           }
  //         )pb",
  //         R"pb(
  //           two_match_fields_table_entry {
  //             match { id_1: "key-a", id_2: "0x002" }
  //             action { do_thing_4 {} }
  //             controller_metadata: "Dependency"
  //           }
  //         )pb",
  //     });

  // Root
  //   |
  // Dependency   Garbage
  GetEntriesUnreachableFromRootsTest(
      info, "Garbage is unreachable.",
      {
          R"pb(
            referring_by_action_table_entry {
              match { val: "0x001" }
              action {
                referring_to_one_match_field_action { referring_id_1: "key-a" }
              }
              controller_metadata: "Root"
            }
          )pb",
          R"pb(
            one_match_field_table_entry {
              match { id: "key-a" }
              action { do_thing_4 {} }
              controller_metadata: "Dependency"
            }
          )pb",
          R"pb(
            one_match_field_table_entry {
              match { id: "key-c" }
              action { do_thing_4 {} }
              controller_metadata: "Garbage"
            }
          )pb",
      });
  // Root
  //   |
  // Dependency   Root
  GetEntriesUnreachableFromRootsTest(
      info,
      "Root referring to dependency and a standalone Root generates no "
      "garbage.",
      {
          R"pb(
            referring_by_action_table_entry {
              match { val: "0x001" }
              action {
                referring_to_one_match_field_action { referring_id_1: "key-a" }
              }
              controller_metadata: "Root"
            }
          )pb",
          R"pb(
            one_match_field_table_entry {
              match { id: "key-a" }
              action { do_thing_4 {} }
              controller_metadata: "Dependency"
            }
          )pb",
          R"pb(
            referring_by_action_table_entry {
              match { val: "0x001" }
              action {
                referring_to_two_match_fields_action {
                  referring_id_1: "non-exist",
                  referring_id_2: "0x000"
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
                                           one_match_field_table_entry {
                                             match { id: "key-a" }
                                             action { do_thing_4 {} }
                                             controller_metadata: "Garbage"
                                           }
                                         )pb",
                                         R"pb(
                                           one_match_field_table_entry {
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
            referring_by_action_table_entry {
              match { val: "0x001" }
              action {
                referring_to_two_match_fields_action {
                  referring_id_1: "key-a",
                  referring_id_2: "0x002"
                }
              }
              controller_metadata: "Root"
            }
          )pb",
          R"pb(
            referring_by_action_table_entry {
              match { val: "0x002" }
              action {
                referring_to_two_match_fields_action {
                  referring_id_1: "key-a",
                  referring_id_2: "0x002"
                }
              }
              controller_metadata: "Root"
            }
          )pb",
          R"pb(
            two_match_fields_table_entry {
              match { id_1: "key-a", id_2: "0x002" }
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
            referring_to_referring_by_match_field_table_entry {
              match { referring_to_referring_id_1: "key-a" }
              action { do_thing_4 {} }
              controller_metadata: "Root"
            }
          )pb",
          R"pb(
            referring_by_match_field_table_entry {
              match { referring_id_1: "key-a" referring_id_2: "0x001" }
              action { do_thing_4 {} }
              controller_metadata: "Child dependency"
            })pb",
          R"pb(
            two_match_fields_table_entry {
              match { id_1: "key-a", id_2: "0x001" }
              action { do_thing_4 {} }
              controller_metadata: "Grand child Dependency"
            }
          )pb",
      });
  // garbage
  //  |
  // garbage
  GetEntriesUnreachableFromRootsTest(
      info, "Garbage referring to other is garbage.",
      {
          R"pb(
            referring_by_match_field_table_entry {
              match { referring_id_1: "key-a" referring_id_2: "0x001" }
              action { do_thing_4 {} }
              controller_metadata: "garbage"
            }
          )pb",
          R"pb(
            two_match_fields_table_entry {
              match { id_1: "key-a", id_2: "0x001" }
              action { do_thing_4 {} }
              controller_metadata: "garbage"
            }
          )pb",
      });

  // Root
  //   |
  // Child dependency          garbage
  //   |                        /
  // Grand child Dependency
  GetEntriesUnreachableFromRootsTest(
      info,
      "Garbage referring to other dependency is garbage, but other "
      "dependencies that are referred by a root won't be removed.",
      {
          R"pb(
            referring_to_referring_by_match_field_table_entry {
              match { referring_to_referring_id_1: "key-a" }
              action { do_thing_4 {} }
              controller_metadata: "Root"
            }
          )pb",
          R"pb(
            referring_by_match_field_table_entry {
              match { referring_id_1: "key-a" referring_id_2: "0x001" }
              action { do_thing_4 {} }
              controller_metadata: "Child dependency"
            })pb",
          R"pb(
            two_match_fields_table_entry {
              match { id_1: "key-a", id_2: "0x001" }
              action { do_thing_4 {} }
              controller_metadata: "Grandchild dependency referenced by garbage"
            }
          )pb",
          R"pb(
            referring_by_action_table_entry {
              match { val: "0x001" }
              action {
                referring_to_two_match_fields_action {
                  referring_id_1: "key-a"
                  referring_id_2: "0x001"
                }
              }
              controller_metadata: "garbage"
            }
          )pb",
      });

  // Conglomeration of entries, courtesy of dilo@.
  // Root
  //   |
  // Dependency Garbage              Garbage            Root
  //   |        /                      |                |
  // Dependency                     Garbage        Dependency      Root
  GetEntriesUnreachableFromRootsTest(
      info, "Conglomeration test.",
      {
          R"pb(
            referring_to_referring_by_match_field_table_entry {
              match { referring_to_referring_id_1: "key-a" }
              action { do_thing_4 {} }
              controller_metadata: "Root"
            }
          )pb",
          R"pb(
            referring_by_match_field_table_entry {
              match { referring_id_1: "key-a" referring_id_2: "0x002" }
              action { do_thing_4 {} }
              controller_metadata: "Child dependency"
            })pb",
          R"pb(
            two_match_fields_table_entry {
              match { id_1: "key-a", id_2: "0x002" }
              action { do_thing_4 {} }
              controller_metadata: "Grand child Dependency"
            }
          )pb",
          R"pb(
            referring_by_action_table_entry {
              match { val: "0x001" }
              action {
                referring_to_two_match_fields_action {
                  referring_id_1: "key-a"
                  referring_id_2: "0x000"
                }
              }
              controller_metadata: "garbage"
            }
          )pb",
          R"pb(
            one_match_field_table_entry {
              match { id: "key-b" }
              action { do_thing_4 {} }
              controller_metadata: "garbage"
            }
          )pb",
          R"pb(
            referring_by_action_table_entry {
              match { val: "0x001" }
              action {
                referring_to_two_match_fields_action {
                  referring_id_1: "key-b"
                  referring_id_2: "0x000"
                }
              }
              controller_metadata: "garbage"
            }
          )pb",
          R"pb(
            referring_by_action_table_entry {
              match { val: "0x001" }
              action {
                referring_to_one_match_field_action {
                  referring_id_1: "key-c",
                }
              }
              controller_metadata: "Root"
            }
          )pb",
          R"pb(
            one_match_field_table_entry {
              match { id: "key-c" }
              action { do_thing_4 {} }
              controller_metadata: "Dependency"
            }
          )pb",
          R"pb(
            referring_by_action_table_entry {
              match { val: "0x001" }
              action {
                referring_to_two_match_fields_action {
                  referring_id_1: "non-exist",
                  referring_id_2: "0x000"
                }
              }
              controller_metadata: "Root"
            }
          )pb",
      });
  // Multicast Root
  //       |
  //   Dependency      Garbage
  GetEntriesUnreachableFromRootsTest(
      info, "Entries referenced by multicast entries are not garbage collected",
      {
          R"pb(
            multicast_group_table_entry {
              match { multicast_group_id: "0x0037" }
              action {
                replicate {
                  replicas {
                    port: "port_1"
                    instance: "0x0031"
                    backup_replicas { port: "port_2" instance: "0x0032" }
                  }
                }
              }
            }
          )pb",
          R"pb(
            referenced_by_multicast_replica_table_entry {
              match { port: "port_1" instance: "0x0031" }
              action { do_thing_4 {} }
              controller_metadata: "Not Garbage because of primary replica"
            }
          )pb",
          R"pb(
            referenced_by_multicast_replica_table_entry {
              match { port: "port_2" instance: "0x0032" }
              action { do_thing_4 {} }
              controller_metadata: "Not Garbage because of backup replica"
            }
          )pb",
          R"pb(
            referenced_by_multicast_replica_table_entry {
              match { port: "port_12" instance: "0x0031" }
              action { do_thing_4 {} }
              controller_metadata: "Garbage"
            }
          )pb",
      });

  // The reason why some tests are subsets of other tests instead of being
  // combined into one test is because Reference computation is a stateful
  // computation so presence of other entries could influence the outcome of
  // reachability analysis so test cases need to be built incrementally(There
  // was a bug during development that was masked because of test cases were
  // combined).
  GetEntriesUnreachableFromRootsTest(
      info,
      "Reference via match fields: partially referred to non-root entries are "
      "unreachable.",
      {
          R"pb(
            referring_by_match_field_table_entry {
              match { referring_id_1: "key-a" referring_id_2: "0x000" }
              action { do_thing_4 {} }
              controller_metadata: "Root"
            }
          )pb",
          R"pb(
            two_match_fields_table_entry {
              match { id_1: "key-a", id_2: "0x001" }
              action { do_thing_4 {} }
              controller_metadata: "garbage partially referred to via id_1"
            }
          )pb",
          R"pb(
            two_match_fields_table_entry {
              match { id_1: "key-b", id_2: "0x000" }
              action { do_thing_4 {} }
              controller_metadata: "garbage partially referred to via id_2"
            }
          )pb",
      });
  GetEntriesUnreachableFromRootsTest(
      info,
      "Reference via match fields: partially referred to non-root entries are "
      "unreachable and the fully referred to entry is reachable.",
      {
          R"pb(
            referring_by_match_field_table_entry {
              match { referring_id_1: "key-a" referring_id_2: "0x000" }
              action { do_thing_4 {} }
              controller_metadata: "Root"
            }
          )pb",
          R"pb(
            two_match_fields_table_entry {
              match { id_1: "key-a", id_2: "0x001" }
              action { do_thing_4 {} }
              controller_metadata: "garbage partially referred to via id_1"
            }
          )pb",
          R"pb(
            two_match_fields_table_entry {
              match { id_1: "key-b", id_2: "0x000" }
              action { do_thing_4 {} }
              controller_metadata: "garbage partially referred to via id_2"
            }
          )pb",
          R"pb(
            two_match_fields_table_entry {
              match { id_1: "key-a", id_2: "0x000" }
              action { do_thing_4 {} }
              controller_metadata: "fully referred to via both match fields"
            }
          )pb",
      });

  GetEntriesUnreachableFromRootsTest(
      info,
      "Reference via action: partially referred to non-root entries are "
      "unreachable.",
      {
          R"pb(
            referring_by_action_table_entry {
              match { val: "0x001" }
              action {
                referring_to_two_match_fields_action {
                  referring_id_1: "key-a",
                  referring_id_2: "0x000"
                }
              }
              controller_metadata: "Root"
            }
          )pb",
          R"pb(
            two_match_fields_table_entry {
              match { id_1: "key-a", id_2: "0x001" }
              action { do_thing_4 {} }
              controller_metadata: "garbage partially referred to via id_1"
            }
          )pb",
          R"pb(
            two_match_fields_table_entry {
              match { id_1: "key-b", id_2: "0x000" }
              action { do_thing_4 {} }
              controller_metadata: "garbage partially referred to via id_2"
            }
          )pb",
      });

  GetEntriesUnreachableFromRootsTest(
      info,
      "Reference via action: partially referred to non-root entries are "
      "unreachable and the fully referred entry is reachable.",
      {
          R"pb(
            referring_by_action_table_entry {
              match { val: "0x001" }
              action {
                referring_to_two_match_fields_action {
                  referring_id_1: "key-a",
                  referring_id_2: "0x000"
                }
              }
              controller_metadata: "Root"
            }
          )pb",
          R"pb(
            two_match_fields_table_entry {
              match { id_1: "key-a", id_2: "0x000" }
              action { do_thing_4 {} }
              controller_metadata: "Child fully referred by all match fields"
            }
          )pb",
          R"pb(
            two_match_fields_table_entry {
              match { id_1: "key-a", id_2: "0x001" }
              action { do_thing_4 {} }
              controller_metadata: "garbage partially referred to via id_1"
            }
          )pb",
          R"pb(
            two_match_fields_table_entry {
              match { id_1: "key-b", id_2: "0x000" }
              action { do_thing_4 {} }
              controller_metadata: "garbage partially referred to via id_2"
            }
          )pb",
      });
  GetEntriesUnreachableFromRootsTest(
      info,
      "Referred to Entries with same match fields but different actions and "
      "metadata are reachable",
      {
          R"pb(
            referring_by_action_table_entry {
              match { val: "0x001" }
              action {
                referring_to_two_match_fields_action {
                  referring_id_1: "key-a",
                  referring_id_2: "0x000"
                }
              }
              controller_metadata: "Root"
            }
          )pb",
          R"pb(
            two_match_fields_table_entry {
              match { id_1: "key-a", id_2: "0x000" }
              action { do_thing_4 {} }
              controller_metadata: "Child fully referred to by all match fields"
            }
          )pb",
          R"pb(
            two_match_fields_table_entry {
              match { id_1: "key-a", id_2: "0x000" }
              action { do_thing_1 { arg1: "0x00000002" arg2: "0x00000001" } }
              controller_metadata: "Referred to child with a :)"
            }
          )pb",
      });
}  // NOLINT(readability/fn_size)

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

  RunSequenceTests(info);

  RunSortTests(info);

  RunGetEntriesUnreachableFromRootsTests(info);

  ExtractWriteRequestsTests();
  // TODO: b/208439664 - Add negative test (where updates and P4Info are out of
  // sync).
  return 0;
}
