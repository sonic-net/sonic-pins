// Copyright 2025 Google LLC
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

#include "tests/lib/common_ir_table_entries.h"

#include "absl/strings/string_view.h"
#include "p4_pdpi/ir.pb.h"

namespace pins {

pdpi::IrTableEntry L3AdmitAllIrTableEntry() {
  pdpi::IrTableEntry table_entry;
  table_entry.set_table_name("l3_admit_table");
  table_entry.set_priority(1);
  table_entry.mutable_action()->set_name("admit_to_l3");
  return table_entry;
}

pdpi::IrTableEntry VrfIrTableEntry(absl::string_view vrf_id) {
  pdpi::IrTableEntry vrf_entry;
  vrf_entry.set_table_name("vrf_table");
  vrf_entry.add_matches()->set_name("vrf_id");
  vrf_entry.mutable_matches(0)->mutable_exact()->set_str(std::string(vrf_id));
  vrf_entry.mutable_action()->set_name("no_action");
  return vrf_entry;
}

} // namespace pins
