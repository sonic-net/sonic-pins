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

#include <string>

#include "absl/strings/string_view.h"
#include "p4_infra/p4_pdpi/ir.pb.h"

namespace pins {

pdpi::IrTableEntry PuntAllPacketsToControllerIrTableEntry(
    absl::string_view queue_id) {
  pdpi::IrTableEntry entry;
  entry.set_table_name("acl_ingress_table");
  entry.set_priority(1);

  // We do not provide any match fields so this entry will match every packet.
  entry.mutable_action()->set_name("acl_trap");
  auto &queue_param = *entry.mutable_action()->add_params();
  queue_param.set_name("qos_queue");
  *queue_param.mutable_value()->mutable_str() = queue_id;

  return entry;
}

pdpi::IrTableEntry SetVrfIdForAllPacketsIrTableEntry(absl::string_view vrf_id) {
  pdpi::IrTableEntry entry;

  entry.set_table_name("acl_pre_ingress_table");
  entry.set_priority(1129);

  // We do not provide any match fields so this entry will match every packet.
  entry.mutable_action()->set_name("set_vrf");
  auto &vrf_param = *entry.mutable_action()->add_params();
  vrf_param.set_name("vrf_id");
  *vrf_param.mutable_value()->mutable_str() = vrf_id;

  return entry;
}

} // namespace pins
