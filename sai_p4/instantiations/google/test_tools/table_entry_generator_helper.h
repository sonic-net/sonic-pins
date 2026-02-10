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

#ifndef PINS_INFRA_SAI_P4_INSTANTIATIONS_GOOGLE_TEST_TOOLS_TABLE_ENTRY_GENERATOR_HELPER_H_
#define PINS_INFRA_SAI_P4_INSTANTIATIONS_GOOGLE_TEST_TOOLS_TABLE_ENTRY_GENERATOR_HELPER_H_

// This file includes definitions and helper functions for writing
// TableEntryGenerator templates in table_entry_generator.cc.

#include "absl/functional/any_invocable.h"
#include "absl/strings/string_view.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
namespace sai {

struct TableEntryGenerator {
  using EntryGenerator = absl::AnyInvocable<pdpi::IrTableEntry(int)>;

  // A set of table entries that must be installed before any entries from the
  // table entry generator can be installed.
  // Example: a VRF table entry is a pre-requisite for IPv4/IPv6 table entries.
  std::vector<pdpi::IrTableEntry> prerequisites;

  // A function to generate the Nth table entry for the table. Arguments must be
  // in the range of [0, INT_MAX-1].
  EntryGenerator generator;
};

// Returns an EntryGenerator that adds the specified match field as an
// incrementing match field. The type and range of the match is taken from the
// table definition. If the entry index is larger than the range, the match
// field value will wrap around.
//
// Example:
//   auto entry = *gutil::ParseTextProto<pdpi::IrTableEntry>(R"pb(
//       table_name: "ipv4_table"
//       matches { name: "vrf_id" exact { str: "vrf-80" } }
//       action { name: "drop" }
//   )pb");
//   auto generator = IrMatchFieldGenerator(ir_table_def, entry, "ipv4_dst");
//
//   generator(1) Returns:
//     table_name: "ipv4_table"
//     matches { name: "vrf_id" exact { str: "vrf-80" } }
//     matches {
//       name: "ipv4_dst"
//       lpm { value { ipv4: "1.0.0.1" } prefix_length: 32 }
//     }
//     action { name: "drop" }
//
//   generator(16) Returns:
//     table_name: "ipv4_table"
//     matches { name: "vrf_id" exact { str: "vrf-80" } }
//     matches {
//       name: "ipv4_dst"
//       lpm { value { ipv4: "1.0.0.16" } prefix_length: 32 }
//     }
//     action { name: "drop" }
TableEntryGenerator::EntryGenerator
IrMatchFieldGenerator(const pdpi::IrTableDefinition &table_definition,
                      pdpi::IrTableEntry base_entry,
                      absl::string_view match_field);

// Returns an EntryGenerator that populates the priority with an incrementing
// value. If the base entry contains a priority, it will be overwritten.
//
// Example:
//   auto entry = *gutil::ParseTextProto<pdpi::IrTableEntry>(R"pb(
//       table_name: "acl_egress_table"
//       action { name: "acl_drop" }
//   )pb");
//   auto generator = PriorityGenerator(entry);
//
//   generator(1) Returns:
//     table_name: "acl_egress_table"
//     priority: 1
//     action { name: "acl_drop" }
//
//   generator(16) Returns:
//     table_name: "acl_egress_table"
//     priority: 16
//     action { name: "acl_drop" }
TableEntryGenerator::EntryGenerator
PriorityGenerator(pdpi::IrTableEntry base_entry);

// Returns an EntryGenerator similar to the result of IrMatchFieldGenerator but
// which also increments the priority field (similar to PriorityGenerator).
TableEntryGenerator::EntryGenerator IrMatchFieldAndPriorityGenerator(
    const pdpi::IrTableDefinition &table_definition,
    pdpi::IrTableEntry base_entry, absl::string_view match_field);

} // namespace sai

#endif // PINS_INFRA_SAI_P4_INSTANTIATIONS_GOOGLE_TEST_TOOLS_TABLE_ENTRY_GENERATOR_HELPER_H_
