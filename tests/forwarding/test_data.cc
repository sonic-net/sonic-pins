// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "tests/forwarding/test_data.h"

#include <net/ethernet.h>

#include "absl/strings/str_format.h"
#include "gutil/testing.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

namespace sai_pd {

std::vector<sai::TableEntry> CreateUpTo255GenericTableEntries(
    int num_table_entries) {
  // Valid IPv4 address is 4 octets of numbers (from 0-255 in decimal) separated
  // by periods.
  num_table_entries = std::min(num_table_entries, 255);
  std::vector<sai::TableEntry> pd_table_entries;
  pd_table_entries.reserve(num_table_entries);
  for (int i = 0; i < num_table_entries; ++i) {
    sai::TableEntry& pd_entry = pd_table_entries.emplace_back();
    pd_entry = gutil::ParseProtoOrDie<sai::TableEntry>(
        R"pb(
          acl_ingress_table_entry {
            match {
              is_ipv4 { value: "0x1" }
              dst_ip { value: "10.206.196.0" mask: "255.255.255.255" }
              ip_protocol { value: "0x11" mask: "0xff" }
              l4_dst_port { value: "0x0043" mask: "0xffff" }
            }
            action { trap { qos_queue: "0x7" } }
            priority: 2040
          }
        )pb");
    pd_entry.mutable_acl_ingress_table_entry()
        ->mutable_match()
        ->mutable_dst_ip()
        ->set_value(absl::StrFormat("10.206.196.%d", i));
  }

  return pd_table_entries;
}

}  // namespace sai_pd
