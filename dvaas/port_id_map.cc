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

#include <string>
#include <vector>

#include "absl/algorithm/container.h"
#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/test_artifact_writer.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/p4rt/p4rt_port.h"
#include "proto/gnmi/gnmi.grpc.pb.h"

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
    return absl::NotFoundError(absl::Substitute(
        "Control port '$0' was not found among keys of control switch "
        "to SUT P4RT port ID one-to-one map.",
        control_port));
  }
  return it->second;
}

absl::StatusOr<pins_test::P4rtPortId>
MirrorTestbedP4rtPortIdMap::GetControlSwitchPortConnectedToSutPort(
    const pins_test::P4rtPortId& sut_port) const {
  // Handle implicit identity map.
  if (!control_to_sut_port_map_.has_value()) return sut_port;

  // Handle explicit map.
  const auto it = absl::c_find_if(*control_to_sut_port_map_,
                                  [&](const auto& control_sut_port) {
                                    return control_sut_port.second == sut_port;
                                  });
  if (it == control_to_sut_port_map_->end()) {
    return absl::NotFoundError(absl::Substitute(
        "SUT port '$0' was not found among values of control switch "
        "to SUT P4RT port ID one-to-one map.",
        sut_port));
  }
  return it->first;
}

absl::Status CheckAndStoreMappedAndUnmappedPortIds(
    const MirrorTestbedP4rtPortIdMap& port_id_map,
    gnmi::gNMI::StubInterface& sut, gnmi::gNMI::StubInterface& control_switch,
    gutil::TestArtifactWriter& writer) {
  // Get all sut ports and control switch ports.
  auto match_all_predicate = [](auto) { return true; };
  ASSIGN_OR_RETURN(std::vector<pins_test::P4rtPortId> all_sut_ports,
                   pins_test::GetMatchingP4rtPortIds(sut, match_all_predicate));
  ASSIGN_OR_RETURN(
      std::vector<pins_test::P4rtPortId> all_control_ports,
      pins_test::GetMatchingP4rtPortIds(control_switch, match_all_predicate));

  absl::btree_set<pins_test::P4rtPortId> unmapped_sut_ports(
      all_sut_ports.begin(), all_sut_ports.end());
  absl::btree_set<pins_test::P4rtPortId> unmapped_control_ports(
      all_control_ports.begin(), all_control_ports.end());

  // Collect port mappings in the artifact string.
  std::string artifact_string = "Control <-> SUT";
  for (const pins_test::P4rtPortId& control_port : all_control_ports) {
    auto sut_port =
        port_id_map.GetSutPortConnectedToControlSwitchPort(control_port);
    if (!sut_port.ok()) continue;
    // The port is mapped.
    // Ensure that it is mapped to an existing port.
    if (!unmapped_sut_ports.contains(*sut_port)) {
      if (absl::c_find(all_sut_ports, *sut_port) != all_sut_ports.end()) {
        // Two control ports are mapped to the same SUT port. That should never
        // happen based on an invariant of the class.
        return gutil::InvalidArgumentErrorBuilder() << absl::Substitute(
                   "Two control switch P4RT port IDs (including '$0') are "
                   "mapped to the same SUT P4RT port ID '$1'",
                   control_port, *sut_port);
      } else {
        // The mapped port doesn't exist at all.
        return gutil::InvalidArgumentErrorBuilder() << absl::Substitute(
                   "SUT P4RT port ID '$0' does not exist, but is mapped to by "
                   "control switch P4RT port ID '$1'",
                   *sut_port, control_port);
      }
    }

    // Consider both ports mapped and add the mapping to the artifact string.
    unmapped_sut_ports.erase(*sut_port);
    unmapped_control_ports.erase(control_port);
    absl::StrAppendFormat(&artifact_string, "\n% 7s <-> %s",
                          control_port.GetP4rtEncoding(),
                          sut_port->GetP4rtEncoding());
  }

  // Record unmapped ports.
  if (!unmapped_sut_ports.empty()) {
    absl::StrAppendFormat(&artifact_string, "\n\nUnmapped SUT ports: %s",
                          absl::StrJoin(unmapped_sut_ports, ", "));
  }
  if (!unmapped_control_ports.empty()) {
    absl::StrAppendFormat(&artifact_string, "\n\nUnmapped control ports: %s",
                          absl::StrJoin(unmapped_control_ports, ", "));
  }

  return writer.AppendToTestArtifact("mirror_testbed_port_map.txt",
                                     artifact_string);
}

bool MirrorTestbedP4rtPortIdMap::IsImplicitIdentityMap() const {
  return !control_to_sut_port_map_.has_value();
}

absl::StatusOr<absl::btree_set<pins_test::P4rtPortId>>
MirrorTestbedP4rtPortIdMap::GetMappedSutPorts() const {
  if (IsImplicitIdentityMap()) {
    return absl::FailedPreconditionError(
        "Getting mapped SUT ports is not supported for the implicit identity "
        "map.");
  }
  absl::btree_set<pins_test::P4rtPortId> sut_ports;
  for (const auto& [control_port, sut_port] : *control_to_sut_port_map_) {
    sut_ports.insert(sut_port);
  }
  return sut_ports;
}

}  // namespace dvaas
