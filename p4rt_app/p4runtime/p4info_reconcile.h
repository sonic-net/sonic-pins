// Copyright 2025 Google LLC
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

#ifndef PINS_P4RT_APP_P4RUNTIME_P4INFO_RECONCILE_H_
#define PINS_P4RT_APP_P4RUNTIME_P4INFO_RECONCILE_H_

#include <string>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_join.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4rt_app/p4runtime/resource_utilization.h"

namespace p4rt_app {

// This struct represents the actions that must be taken to reconcile a new
// p4info from the current one.
struct P4InfoReconcileTransition {
  // Hashing
  std::vector<std::string> hashing_packet_field_configs_to_delete;
  std::vector<std::string> hashing_packet_field_configs_to_set;
  bool update_switch_table = false;

  // ACL
  std::vector<std::string> acl_tables_to_delete;
  std::vector<std::string> acl_tables_to_add;
  std::vector<std::string> acl_tables_to_modify;

  template <typename Sink>
  friend void AbslStringify(Sink& sink,
                            const P4InfoReconcileTransition& transition) {
    absl::Format(
        &sink,
        R"({
  hashing_packet_field_configs_to_delete = {%s},
  hashing_packet_field_configs_to_set = {%s},
  upate_switch_table = %s,
  acl_tables_to_delete = {%s},
  acl_tables_to_add = {%s},
  acl_tables_to_modify = {%s},
})",

        absl::StrJoin(transition.hashing_packet_field_configs_to_delete, ", "),
        absl::StrJoin(transition.hashing_packet_field_configs_to_set, ", "),
        (transition.update_switch_table ? "true" : "false"),
        absl::StrJoin(transition.acl_tables_to_delete, ", "),
        absl::StrJoin(transition.acl_tables_to_add, ", "),
        absl::StrJoin(transition.acl_tables_to_modify, ", "));
  }
};

// Returns the transition steps for migrating to a new P4Info.
// Returns an error if there is an unreconcilable difference.
absl::StatusOr<P4InfoReconcileTransition> CalculateTransition(
    const pdpi::IrP4Info& from, const pdpi::IrP4Info& to);

absl::StatusOr<absl::flat_hash_map<std::string, ActionProfileResourceCapacity>>
GetUpdatedResourceCapacities(
    const pdpi::IrP4Info& ir_p4info,
    const absl::flat_hash_map<std::string, ActionProfileResourceCapacity>&
        original);

}  // namespace p4rt_app

#endif  // PINS_P4RT_APP_P4RUNTIME_P4INFO_RECONCILE_H_
