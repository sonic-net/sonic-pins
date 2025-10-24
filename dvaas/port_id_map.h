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

#ifndef PINS_DVAAS_PORT_ID_MAP_H_
#define PINS_DVAAS_PORT_ID_MAP_H_

#include <optional>
#include <utility>

#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "gutil/test_artifact_writer.h"
#include "lib/p4rt/p4rt_port.h"
#include "proto/gnmi/gnmi.grpc.pb.h"

namespace dvaas {

// Keeps a map between the P4RT port IDs of connected interfaces between the
// control switch and the SUT in a mirror testbed.
class MirrorTestbedP4rtPortIdMap {
public:
  // Creates a port mapping from SUT -> control switch port map.
  static absl::StatusOr<MirrorTestbedP4rtPortIdMap>
  CreateFromSutToControlSwitchPortMap(
      absl::flat_hash_map<pins_test::P4rtPortId, pins_test::P4rtPortId>
          sut_to_control_port_map);

  // Creates a port mapping from control switch -> SUT port map.
  static absl::StatusOr<MirrorTestbedP4rtPortIdMap>
  CreateFromControlSwitchToSutPortMap(
      absl::flat_hash_map<pins_test::P4rtPortId, pins_test::P4rtPortId>
          control_to_sut_port_map);

  // Creates an implicit map in which any port ID is mapped to itself.
  static MirrorTestbedP4rtPortIdMap CreateIdentityMap() {
    return MirrorTestbedP4rtPortIdMap();
  }

  // Creates a map in which the P4RT port IDs of interfaces of SUT and control
  // switch with the same OpenConfig interface name are mapped to each other.
  static absl::StatusOr<MirrorTestbedP4rtPortIdMap>
  CreateFromMatchingInterfaceNames(gnmi::gNMI::StubInterface &sut,
                                   gnmi::gNMI::StubInterface &control_switch) {
    // TODO: Implement inferring port ID mapping from mirror
    // testbed interface names.
    return absl::UnimplementedError(
        "Inferring port ID mapping from mirror testbed interface names is not "
        "supported yet.");
  }

  // Returns the P4RT port ID of the SUT interface connected to the interface on
  // the control switch with the given P4RT port ID according to the port
  // mapping.
  absl::StatusOr<pins_test::P4rtPortId> GetSutPortConnectedToControlSwitchPort(
      const pins_test::P4rtPortId &control_port) const;

  // Returns the P4RT port ID of the control switch interface connected to the
  // interface on the SUT with the given P4RT port ID according to the port
  // mapping.
  absl::StatusOr<pins_test::P4rtPortId> GetControlSwitchPortConnectedToSutPort(
      const pins_test::P4rtPortId &sut_port) const;

  // Returns the set of P4RT port IDs of the SUT interfaces mapped to a control
  // switch port. Returns an error if the port mapping is implicit.
  absl::StatusOr<absl::btree_set<pins_test::P4rtPortId>> GetMappedSutPorts()
      const;

  // Returns true if no explicit port mapping is provided. In that case, the
  // object implicitly assumes that any port ID in SUT is mapped to the same
  // port ID on the control switch.
  bool IsImplicitIdentityMap() const;

 private:
  MirrorTestbedP4rtPortIdMap(
      absl::flat_hash_map<pins_test::P4rtPortId, pins_test::P4rtPortId>
          control_to_sut_port_map)
      : control_to_sut_port_map_(std::move(control_to_sut_port_map)) {}
  MirrorTestbedP4rtPortIdMap() = default;

  // If nullopt, an implicit identity map is assumed.
  std::optional<
      absl::flat_hash_map<pins_test::P4rtPortId, pins_test::P4rtPortId>>
      control_to_sut_port_map_;
};

// Records the mapping between control and SUT ports as an artifact, noting
// any unmapped ports in both.
// Also, ensures that mapped ports exist.
absl::Status CheckAndStoreMappedAndUnmappedPortIds(
    const MirrorTestbedP4rtPortIdMap &port_id_map,
    gnmi::gNMI::StubInterface &sut, gnmi::gNMI::StubInterface &control_switch,
    gutil::TestArtifactWriter &writer);

} // namespace dvaas

#endif // PINS_DVAAS_PORT_ID_MAP_H_
