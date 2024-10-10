// Copyright (c) 2024, Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "dvaas/mirror_testbed_config.h"

#include <functional>
#include <optional>
#include <string>
#include <vector>

#include "absl/algorithm/container.h"
#include "absl/container/btree_map.h"
#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/match.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "dvaas/port_id_map.h"
#include "dvaas/switch_api.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/test_artifact_writer.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/p4_runtime_session_extras.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "thinkit/mirror_testbed.h"

namespace dvaas {
namespace {

constexpr absl::string_view kArtifactPrefix = "configurator.";

struct StoreSwitchStateParams {
  bool store_p4info = false;
  bool store_ir_p4info = false;
  bool store_gnmi_config = false;
  bool store_ir_entities = false;
};
absl::Status StoreSwitchStateAsArtifacts(
    SwitchApi& switch_api, absl::string_view prefix,
    const StoreSwitchStateParams& params = {}) {
  gutil::BazelTestArtifactWriter writer;
  ASSIGN_OR_RETURN(const p4::config::v1::P4Info p4info,
                   pdpi::GetP4Info(*switch_api.p4rt));
  if (params.store_p4info) {
    // Store P4Info.
    RETURN_IF_ERROR(writer.AppendToTestArtifact(
        absl::StrCat(prefix, "p4info.txtpb"), gutil::PrintTextProto(p4info)));
  }
  if (params.store_ir_p4info) {
    // Store IR P4Info.
    ASSIGN_OR_RETURN(const pdpi::IrP4Info ir_p4info,
                     pdpi::CreateIrP4Info(p4info));
    RETURN_IF_ERROR(
        writer.AppendToTestArtifact(absl::StrCat(prefix, "ir_p4info.txtpb"),
                                    gutil::PrintTextProto(ir_p4info)));
  }
  if (params.store_gnmi_config) {
    // Store gNMI config.
    ASSIGN_OR_RETURN(const std::string gnmi_config,
                     pins_test::GetGnmiConfig(*switch_api.gnmi));
    RETURN_IF_ERROR(writer.AppendToTestArtifact(
        absl::StrCat(prefix, "gnmi_config.json"), gnmi_config));
  }
  // Store IR entities.
  if (params.store_ir_entities) {
    ASSIGN_OR_RETURN(const pdpi::IrEntities ir_entities,
                     pdpi::ReadIrEntities(*switch_api.p4rt));
    RETURN_IF_ERROR(
        writer.AppendToTestArtifact(absl::StrCat(prefix, "ir_entities.txtpb"),
                                    gutil::PrintTextProto(ir_entities)));
  }
  return absl::OkStatus();
};

// Tries to configure a subset of SUT's interfaces to map every given P4RT port
// ID in `p4rt_port_ids` to an enabled Ethernet interface. If provided,
// `target_sut_ports` limits the set of changes to those specific ports.
absl::Status ConfigureSutInterfacesWithGivenP4rtPortIds(
    gnmi::gNMI::StubInterface& sut_gnmi_stub,
    const absl::btree_set<pins_test::P4rtPortId>& p4rt_port_ids,
    std::optional<absl::btree_set<pins_test::P4rtPortId>> target_sut_ports) {
  // Map the given P4RT port IDs to enabled Ethernet interfaces by default.
  std::function<bool(const pins_test::openconfig::Interfaces::Interface&)>
      selector = pins_test::IsEnabledEthernetInterface;
  // If `target_sut_ports` is provided, only map to those interfaces.
  if (target_sut_ports.has_value()) {
    selector =
        [&](const pins_test::openconfig::Interfaces::Interface& interface) {
          return pins_test::IsEnabledEthernetInterface(interface) &&
                 target_sut_ports->contains(
                     pins_test::P4rtPortId::MakeFromOpenConfigEncoding(
                         interface.config().p4rt_id()));
        };
  }

  absl::btree_set<int> open_config_p4rt_port_ids;
  for (const pins_test::P4rtPortId& p4rt_port_id : p4rt_port_ids) {
    open_config_p4rt_port_ids.insert(p4rt_port_id.GetOpenConfigEncoding());
  }
  // Map the required P4RT port IDs to matching interfaces on the SUT.
  RETURN_IF_ERROR(pins_test::MapP4rtIdsToMatchingInterfaces(
      sut_gnmi_stub, open_config_p4rt_port_ids, selector));

  return absl::OkStatus();
}

// Returns the (first) interface with the given P4RT `port_id` from the given
// list of `interfaces`. Returns an error if no such interface is found.
absl::StatusOr<pins_test::openconfig::Interfaces::Interface>
GetInterfaceFromPortId(const pins_test::openconfig::Interfaces& interfaces,
                       pins_test::P4rtPortId port_id) {
  const auto it = absl::c_find_if(
      interfaces.interfaces(),
      [&](const pins_test::openconfig::Interfaces::Interface& interface) {
        return interface.config().p4rt_id() == port_id.GetOpenConfigEncoding();
      });
  if (it == interfaces.interfaces().end()) {
    return absl::NotFoundError(absl::StrCat(
        "Could not find interface with P4RT port ID ",
        port_id.GetOpenConfigEncoding(), " in the given interface list."));
  }
  return *it;
}

// Returns the (first) interface with the given `interface_name` from the given
// list of `interfaces`. Returns an error if no such interface is found.
absl::StatusOr<pins_test::openconfig::Interfaces::Interface>
GetInterfaceFromName(const pins_test::openconfig::Interfaces& interfaces,
                     std::string interface_name) {
  const auto it = absl::c_find_if(
      interfaces.interfaces(),
      [&](const pins_test::openconfig::Interfaces::Interface& interface) {
        return interface.config().name() == interface_name;
      });
  if (it == interfaces.interfaces().end()) {
    return absl::NotFoundError(
        absl::StrCat("Could not find interface with name '", interface_name,
                     "' in the given interface list."));
  }
  return *it;
}

// Returns SUT interface name to control switch interface name connectivity map
// inferred from the given `port_id_map`.
absl::StatusOr<absl::btree_map<std::string, std::string>>
MakeSutToControlInterfaceNameMapFromPortIdMap(
    const MirrorTestbedP4rtPortIdMap& port_id_map,
    const pins_test::openconfig::Interfaces& sut_interfaces,
    const pins_test::openconfig::Interfaces& control_interfaces) {
  absl::btree_map<std::string, std::string> sut_to_control_interface_name_map;
  ASSIGN_OR_RETURN(absl::btree_set<pins_test::P4rtPortId> target_sut_ports,
                   port_id_map.GetMappedSutPorts());
  for (const pins_test::P4rtPortId& sut_port : target_sut_ports) {
    // Get P4RT port ID of the control switch port connected to the SUT port.
    ASSIGN_OR_RETURN(
        const pins_test::P4rtPortId control_port,
        port_id_map.GetControlSwitchPortConnectedToSutPort(sut_port));
    // Get SUT interface by P4RT port ID.
    ASSIGN_OR_RETURN(
        const pins_test::openconfig::Interfaces::Interface sut_interface,
        GetInterfaceFromPortId(sut_interfaces, sut_port));
    // Get control switch interface by P4RT port ID.
    ASSIGN_OR_RETURN(
        const pins_test::openconfig::Interfaces::Interface control_interface,
        GetInterfaceFromPortId(control_interfaces, control_port));
    // Add to the map.
    sut_to_control_interface_name_map.insert(
        {sut_interface.config().name(), control_interface.config().name()});
  }
  return sut_to_control_interface_name_map;
}

// Helper function to perform the given `action` on pairs of connected SUT-CS
// interfaces (provided by `sut_to_control_interface_name_map`). If
// `target_sut_port_ids` is provided, only the pairs containing SUT ports with
// P4RT IDs in that set are considered.
absl::Status PerformActionOnConnectedInterfacePairs(
    absl::btree_map<std::string, std::string> sut_to_control_interface_name_map,
    const pins_test::openconfig::Interfaces& sut_interfaces,
    const pins_test::openconfig::Interfaces& control_interfaces,
    const std::optional<absl::btree_set<pins_test::P4rtPortId>>&
        target_sut_ports,
    std::function<absl::Status(
        const pins_test::openconfig::Interfaces::Interface& sut_interface,
        const pins_test::openconfig::Interfaces::Interface& control_interface)>
        action) {
  for (const auto& [sut_interface_name, control_interface_name] :
       sut_to_control_interface_name_map) {
    // Get SUT interface by name.
    ASSIGN_OR_RETURN(
        const pins_test::openconfig::Interfaces::Interface sut_interface,
        GetInterfaceFromName(sut_interfaces, sut_interface_name));
    // Skip if the SUT port is not in the target set.
    if (target_sut_ports.has_value() &&
        !target_sut_ports->contains(
            pins_test::P4rtPortId::MakeFromOpenConfigEncoding(
                sut_interface.config().p4rt_id()))) {
      continue;
    }
    // Get control switch interface by name.
    ASSIGN_OR_RETURN(
        const pins_test::openconfig::Interfaces::Interface control_interface,
        GetInterfaceFromName(control_interfaces, control_interface_name));
    // Perform the action.
    RETURN_IF_ERROR(action(sut_interface, control_interface));
  }

  return absl::OkStatus();
}

// Returns a SUT to control switch P4RT port ID map inferred from the given
// `sut_to_control_interface_name_map`. If `target_sut_port_ids` is provided,
// only the SUT ports with P4RT IDs in that set are mapped.
absl::StatusOr<MirrorTestbedP4rtPortIdMap>
MakePortIdMapFromSutToControlInterfaceNameMap(
    absl::btree_map<std::string, std::string> sut_to_control_interface_name_map,
    const pins_test::openconfig::Interfaces& sut_interfaces,
    const pins_test::openconfig::Interfaces& control_interfaces,
    const std::optional<absl::btree_set<pins_test::P4rtPortId>>&
        target_sut_ports) {
  absl::flat_hash_map<pins_test::P4rtPortId, pins_test::P4rtPortId>
      sut_to_control_port_id_map;
  RETURN_IF_ERROR(PerformActionOnConnectedInterfacePairs(
      sut_to_control_interface_name_map, sut_interfaces, control_interfaces,
      target_sut_ports, /*action=*/
      [&](const pins_test::openconfig::Interfaces::Interface& sut_interface,
          const pins_test::openconfig::Interfaces::Interface& control_interface)
          -> absl::Status {
        sut_to_control_port_id_map.insert(
            {pins_test::P4rtPortId::MakeFromOpenConfigEncoding(
                 sut_interface.config().p4rt_id()),
             pins_test::P4rtPortId::MakeFromOpenConfigEncoding(
                 control_interface.config().p4rt_id())});
        return absl::OkStatus();
      }));

  return MirrorTestbedP4rtPortIdMap::CreateFromSutToControlSwitchPortMap(
      sut_to_control_port_id_map);
}

// Stores the given `sut_to_control_interface_name_map` as a test artifact.
// If `target_sut_ports` is provided, only the SUT ports with P4RT IDs in the
// set are considered.
absl::Status StorePortMapAsTestArtifact(
    const absl::btree_map<std::string, std::string>&
        sut_to_control_interface_name_map,
    absl::string_view prefix,
    const pins_test::openconfig::Interfaces& sut_interfaces,
    const pins_test::openconfig::Interfaces& control_interfaces,
    const std::optional<absl::btree_set<pins_test::P4rtPortId>>&
        target_sut_ports) {
  gutil::BazelTestArtifactWriter writer;
  const std::string file_name = absl::StrCat(prefix, "port_map.txt");
  RETURN_IF_ERROR(writer.AppendToTestArtifact(
      file_name,
      "SUT Interface (P4RT ID) <-> Control Switch Interface (P4RT ID)\n"));
  RETURN_IF_ERROR(PerformActionOnConnectedInterfacePairs(
      sut_to_control_interface_name_map, sut_interfaces, control_interfaces,
      target_sut_ports, /*action=*/
      [&](const pins_test::openconfig::Interfaces::Interface& sut_interface,
          const pins_test::openconfig::Interfaces::Interface& control_interface)
          -> absl::Status {
        RETURN_IF_ERROR(writer.AppendToTestArtifact(
            file_name, absl::Substitute("$0 ($1) <-> $2 ($3)\n",
                                        sut_interface.config().name(),
                                        sut_interface.config().p4rt_id(),
                                        control_interface.config().name(),
                                        control_interface.config().p4rt_id())));
        return absl::OkStatus();
      }));

  return absl::OkStatus();
}

}  // namespace

absl::StatusOr<MirrorTestbedConfigurator> MirrorTestbedConfigurator::Create(
    thinkit::MirrorTestbed* testbed) {
  MirrorTestbedConfigurator configured_testbed(testbed);

  ASSIGN_OR_RETURN(configured_testbed.sut_api_.p4rt,
                   pdpi::P4RuntimeSession::Create(testbed->Sut()));
  ASSIGN_OR_RETURN(configured_testbed.sut_api_.gnmi,
                   testbed->Sut().CreateGnmiStub());
  ASSIGN_OR_RETURN(configured_testbed.control_switch_api_.p4rt,
                   pdpi::P4RuntimeSession::Create(testbed->ControlSwitch()));
  ASSIGN_OR_RETURN(configured_testbed.control_switch_api_.gnmi,
                   testbed->ControlSwitch().CreateGnmiStub());

  constexpr StoreSwitchStateParams kStoreOriginalSwitchStateParams = {
      .store_p4info = true,
      .store_ir_p4info = true,
      .store_gnmi_config = true,
      .store_ir_entities = true,
  };
  RETURN_IF_ERROR(StoreSwitchStateAsArtifacts(
      configured_testbed.sut_api_,
      absl::StrCat(kArtifactPrefix, "original.sut."),
      kStoreOriginalSwitchStateParams));
  RETURN_IF_ERROR(
      StoreSwitchStateAsArtifacts(configured_testbed.control_switch_api_,
                                  absl::StrCat(kArtifactPrefix, "original.cs."),
                                  kStoreOriginalSwitchStateParams));

  return configured_testbed;
}

absl::Status MirrorTestbedConfigurator::ConfigureForForwardingTest(
    const MirrorTestbedConfigurator::Params& params) {
  // The testbed must not have been configured before.
  if (original_control_interfaces_.has_value()) {
    return absl::FailedPreconditionError(
        "Configure function called on an already configured testbed.");
  }
  // Rule out unusual parameter combinations.
  if (params.p4rt_port_ids_to_configure.has_value() &&
      !params.original_port_map.has_value() &&
      !params.mirror_sut_ports_ids_to_control_switch) {
    return absl::InvalidArgumentError(
        "`mirror_sut_ports_to_control_switch` must be true when "
        "`used_p4rt_port_ids` is non-nullopt and `original_port_map` is "
        "nullopt.");
  }
  if (params.original_port_map.has_value() &&
      params.original_port_map->IsImplicitIdentityMap()) {
    return absl::InvalidArgumentError(
        "The original port map should be explicit if not nullopt.");
  }

  // Store the original control switch gNMI interface config before changing
  // it.
  ASSIGN_OR_RETURN(original_control_interfaces_,
                   pins_test::GetInterfacesAsProto(*control_switch_api_.gnmi,
                                                   gnmi::GetRequest::CONFIG));

  // Infer the SUT to control switch interface name connectivity map from the
  // original port map (if provided).
  std::optional<absl::btree_set<pins_test::P4rtPortId>> mapped_sut_ports;
  std::optional<absl::btree_map<std::string, std::string>>
      sut_to_control_interface_name_map;
  if (params.original_port_map.has_value()) {
    ASSIGN_OR_RETURN(mapped_sut_ports,
                     params.original_port_map->GetMappedSutPorts());
    ASSIGN_OR_RETURN(sut_to_control_interface_name_map,
                     MakeSutToControlInterfaceNameMapFromPortIdMap(
                         *params.original_port_map, *original_sut_interfaces_,
                         *original_control_interfaces_));

    RETURN_IF_ERROR(StorePortMapAsTestArtifact(
        *sut_to_control_interface_name_map,
        /*prefix=*/absl::StrCat(kArtifactPrefix, "original."),
        *original_sut_interfaces_, *original_control_interfaces_,
        /*target_sut_ports=*/std::nullopt));
  }

  // Configure SUT IDs to match `p4rt_port_ids_to_configure` (if provided).
  if (params.p4rt_port_ids_to_configure.has_value()) {
    // Clear entities on SUT. This is needed to ensure we can modify the
    // interface configurations.
    RETURN_IF_ERROR(pdpi::ClearEntities(*sut_api_.p4rt));

    // Change interface configurations on SUT to match `used_p4rt_port_ids`.
    RETURN_IF_ERROR(ConfigureSutInterfacesWithGivenP4rtPortIds(
        *sut_api_.gnmi, *params.p4rt_port_ids_to_configure, mapped_sut_ports));
  }

  // Mirror SUT port config to control switch (if requested).
  if (params.mirror_sut_ports_ids_to_control_switch) {
    // Clear entities on control switch. This is needed to ensure we can
    // modify the interface configurations.
    RETURN_IF_ERROR(pdpi::ClearEntities(*control_switch_api_.p4rt));

    // Mirror the SUTs OpenConfig interface <-> P4RT port ID mappings to the
    // control switch.
    RETURN_IF_ERROR(
        pins_test::MirrorSutP4rtPortIdConfigToControlSwitch(testbed_));
  }

  // Infer the new P4RT port ID connectivity map after the modifications. This
  // is inferred from interface connectivity map, which itself was inferred from
  // original port map (if provided). If `p4rt_port_ids_to_configure` is
  // provided, only the SUT ports with P4RT IDs in that set are mapped.
  if (params.original_port_map.has_value()) {
    ASSIGN_OR_RETURN(
        const pins_test::openconfig::Interfaces configured_sut_interfaces,
        pins_test::GetInterfacesAsProto(*sut_api_.gnmi,
                                        gnmi::GetRequest::CONFIG));
    ASSIGN_OR_RETURN(
        const pins_test::openconfig::Interfaces configured_control_interfaces,
        pins_test::GetInterfacesAsProto(*control_switch_api_.gnmi,
                                        gnmi::GetRequest::CONFIG));
    ASSIGN_OR_RETURN(
        configured_port_map_,
        MakePortIdMapFromSutToControlInterfaceNameMap(
            *sut_to_control_interface_name_map, configured_sut_interfaces,
            configured_control_interfaces,
            /*target_sut_ports=*/params.p4rt_port_ids_to_configure));

    RETURN_IF_ERROR(StorePortMapAsTestArtifact(
        *sut_to_control_interface_name_map,
        /*prefix=*/absl::StrCat(kArtifactPrefix, "configured."),
        configured_sut_interfaces, configured_control_interfaces,
        /*target_sut_ports=*/params.p4rt_port_ids_to_configure));
  }

 // Ensure that all enabled ports are up.
  if (params.wait_for_all_enabled_interfaces_to_be_up) {
    RETURN_IF_ERROR(pins_test::WaitForEnabledInterfacesToBeUp(testbed_.Sut()))
            .SetPrepend()
        << "expected enabled interfaces on SUT to be up: ";
    RETURN_IF_ERROR(
        pins_test::WaitForEnabledInterfacesToBeUp(testbed_.ControlSwitch()))
            .SetPrepend()
        << "expected enabled interfaces on control switch to be up: ";
  }

  constexpr StoreSwitchStateParams kStoreConfiguredSwitchStateParams = {
      .store_gnmi_config = true,
      .store_ir_entities = true,
  };
  RETURN_IF_ERROR(StoreSwitchStateAsArtifacts(
      sut_api_, absl::StrCat(kArtifactPrefix, "configured.sut."),
      kStoreConfiguredSwitchStateParams));
  RETURN_IF_ERROR(StoreSwitchStateAsArtifacts(
      control_switch_api_, absl::StrCat(kArtifactPrefix, "configured.cs."),
      kStoreConfiguredSwitchStateParams));

  return absl::OkStatus();
}

absl::Status MirrorTestbedConfigurator::RestoreToOriginalConfiguration() {
  // The testbed must have been configured before.
  if (!original_control_interfaces_.has_value()) {
    return absl::FailedPreconditionError(
        "The testbed has not been configured for forwarding test before.");
  }

  // Clear table entries on both SUT and control switch. This is needed to
  // ensure we can modify their interface configurations.
  RETURN_IF_ERROR(pdpi::ClearEntities(*control_switch_api_.p4rt));
  RETURN_IF_ERROR(pdpi::ClearEntities(*sut_api_.p4rt));

  // Restore the original interface P4RT port id configurations of SUT and
  // control switch.
  RETURN_IF_ERROR(pins_test::SetInterfaceP4rtIds(*sut_api_.gnmi,
                                                 *original_sut_interfaces_));
  RETURN_IF_ERROR(pins_test::SetInterfaceP4rtIds(
      *control_switch_api_.gnmi, *original_control_interfaces_));

  // Remove the kept interfaces.
  original_control_interfaces_.reset();

  // Remove port map (if any).
  configured_port_map_.reset();

  return absl::OkStatus();
}

absl::StatusOr<MirrorTestbedP4rtPortIdMap>
MirrorTestbedConfigurator::GetConfiguredPortMap() {
  if (!configured_port_map_.has_value()) {
    return absl::FailedPreconditionError(
        "Either the testbed has not been configured for forwarding test or no "
        "explicit port map was provided.");
  }
  return *configured_port_map_;
}

}  // namespace dvaas
