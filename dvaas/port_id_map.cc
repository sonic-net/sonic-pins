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

#include "dvaas/port_id_map.h"

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/substitute.h"
#include "gutil/status.h"
#include "lib/p4rt/p4rt_port.h"

namespace dvaas {

using pins_test::P4rtPortId;

absl::StatusOr<MirrorTestbedP4rtPortIdMap>
MirrorTestbedP4rtPortIdMap::CreateFromSutToControlSwitchPortMap(
    absl::flat_hash_map<P4rtPortId, pins_test::P4rtPortId>
        sut_to_control_port_map) {
  absl::flat_hash_map<pins_test::P4rtPortId, pins_test::P4rtPortId>
      control_to_sut_port_map;
  for (const auto& [sut_port, control_port] : sut_to_control_port_map) {
    if (control_to_sut_port_map.contains(control_port)) {
      return gutil::InvalidArgumentErrorBuilder() << absl::Substitute(
                 "Both SUT P4RT port IDs '$0' and '$1' are mapped to control "
                 "switch P4RT port ID '$2'",
                 sut_port, control_to_sut_port_map[control_port], control_port);
    }
    control_to_sut_port_map[control_port] = sut_port;
  }

  return MirrorTestbedP4rtPortIdMap(control_to_sut_port_map);
}

absl::StatusOr<MirrorTestbedP4rtPortIdMap>
MirrorTestbedP4rtPortIdMap::CreateFromControlSwitchToSutPortMap(
    absl::flat_hash_map<pins_test::P4rtPortId, pins_test::P4rtPortId>
        control_to_sut_port_map) {
  absl::flat_hash_map<pins_test::P4rtPortId, pins_test::P4rtPortId>
      sut_to_control_port_map;
  for (const auto& [control_port, sut_port] : control_to_sut_port_map) {
    if (sut_to_control_port_map.contains(sut_port)) {
      return gutil::InvalidArgumentErrorBuilder() << absl::Substitute(
                 "Both control switch P4RT port IDs '$0' and '$1' are mapped "
                 "to SUT P4RT port ID '$2'",
                 control_port, sut_to_control_port_map[sut_port], sut_port);
    }
    sut_to_control_port_map[sut_port] = control_port;
  }

  return MirrorTestbedP4rtPortIdMap(control_to_sut_port_map);
}

absl::StatusOr<pins_test::P4rtPortId>
MirrorTestbedP4rtPortIdMap::GetSutPortConnectedToControlSwitchPort(
    const pins_test::P4rtPortId& control_port) const {
  // Handle implicit identity map.
  if (!control_to_sut_port_map_.has_value()) return control_port;

  // Handle explicit map.
  const auto it = control_to_sut_port_map_->find(control_port);
  if (it == control_to_sut_port_map_->end()) {
    return absl::NotFoundError(
        absl::Substitute("Control port '$0' was not found in control switch "
                         "to SUT P4RT port ID map.",
                         control_port));
  } else {
    return it->second;
  }
}

}  // namespace dvaas
