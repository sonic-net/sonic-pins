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

#include <string>
#include <vector>

#include "absl/container/btree_set.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
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
// ID in `p4rt_port_ids` to an enabled Ethernet interface.
absl::Status ConfigureSutInterfacesWithGivenP4RtPortIds(
    gnmi::gNMI::StubInterface& sut_gnmi_stub,
    const absl::btree_set<pins_test::P4rtPortId>& p4rt_port_ids) {
  // Only map to enabled Ethernet interfaces.
  auto is_enabled_ethernet_interface =
      [](const pins_test::openconfig::Interfaces::Interface& interface) {
        return interface.config().enabled() &&
               // Ethernet interfaces are, so far, best identified by name.
               absl::StartsWith(interface.name(), "Ethernet");
      };

  absl::btree_set<int> open_config_p4rt_port_ids;
  for (const pins_test::P4rtPortId& p4rt_port_id : p4rt_port_ids) {
    open_config_p4rt_port_ids.insert(p4rt_port_id.GetOpenConfigEncoding());
  }
  // Map the required P4RT port IDs to matching interfaces on the SUT.
  RETURN_IF_ERROR(pins_test::MapP4rtIdsToMatchingInterfaces(
      sut_gnmi_stub, open_config_p4rt_port_ids, is_enabled_ethernet_interface));

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
  if (params.p4rt_port_ids_to_configure.has_value()) {
    if (!params.mirror_sut_ports_ids_to_control_switch) {
      return absl::InvalidArgumentError(
          "`mirror_sut_ports_to_control_switch` must be true when "
          "`used_p4rt_port_ids` is non-nullopt.");
    }
  }

  // Store the original control switch gNMI interface config before changing
  // it.
  ASSIGN_OR_RETURN(original_control_interfaces_,
                   pins_test::GetInterfacesAsProto(*control_switch_api_.gnmi,
                                                   gnmi::GetRequest::CONFIG));

  if (params.p4rt_port_ids_to_configure.has_value()) {
    // Clear entities on SUT. This is needed to ensure we can modify the
    // interface configurations.
    RETURN_IF_ERROR(pdpi::ClearEntities(*sut_api_.p4rt));

    // Change interface configurations on SUT to match `used_p4rt_port_ids`.
    RETURN_IF_ERROR(ConfigureSutInterfacesWithGivenP4RtPortIds(
        *sut_api_.gnmi, *params.p4rt_port_ids_to_configure));
  }

  if (params.mirror_sut_ports_ids_to_control_switch) {
    // Clear entities on control switch. This is needed to ensure we can modify
    // the interface configurations.
    RETURN_IF_ERROR(pdpi::ClearEntities(*control_switch_api_.p4rt));

    // Mirror the SUTs OpenConfig interface <-> P4RT port ID mappings to the
    // control switch.
    RETURN_IF_ERROR(
        pins_test::MirrorSutP4rtPortIdConfigToControlSwitch(testbed_));
  }

  // Ensure that all enabled ports are up.
  RETURN_IF_ERROR(pins_test::WaitForEnabledInterfacesToBeUp(testbed_.Sut()))
          .SetPrepend()
      << "expected enabled interfaces on SUT to be up: ";
  RETURN_IF_ERROR(
      pins_test::WaitForEnabledInterfacesToBeUp(testbed_.ControlSwitch()))
          .SetPrepend()
      << "expected enabled interfaces on control switch to be up: ";

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

  // Restore the original control switch gNMI interface config's P4RT IDs.
  RETURN_IF_ERROR(pins_test::SetInterfaceP4rtIds(
      *control_switch_api_.gnmi, *original_control_interfaces_));

  // Remove the kept interfaces.
  original_control_interfaces_.reset();

  return absl::OkStatus();
}

}  // namespace dvaas
