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

#include "tests/lib/switch_test_setup_helpers.h"

#include <deque>
#include <functional>
#include <future>  // NOLINT: third_party library.
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/btree_map.h"
#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_map.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/optional.h"
#include "absl/types/span.h"
#include "absl/flags/flag.h"
#include "gtest/gtest.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/gnmi/openconfig.pb.h"
#include "lib/p4rt/p4rt_port.h"
#include "lib/validator/validator_lib.h"
#include "p4/config/v1/p4types.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir_tools.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "tests/thinkit_sanity_tests.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/switch.h"

// Flag used to skip gNMI push if set to false in the command line
// TODO(PINS): To be removed when gNMI push config is supported
ABSL_FLAG(bool, gnmi_push_support, true, "gNMI push config supported");

namespace pins_test {
namespace {

constexpr absl::Duration kGnmiTimeoutDefault = absl::Minutes(3);
constexpr char kPortNamedType[] = "port_id_t";

// Only clears entities if a P4RT session can be established.
//
// P4RT requires a device ID to be pushed over gNMI which is not enforced by
// this helper function. Given that we can't know the switch's state in all
// cases where this will be called, we default to best effort for clearing the
// entities.
absl::Status TryClearingEntities(
    thinkit::Switch& thinkit_switch,
    const pdpi::P4RuntimeSessionOptionalArgs& metadata) {
  absl::StatusOr<std::unique_ptr<pdpi::P4RuntimeSession>> session =
      pdpi::P4RuntimeSession::Create(thinkit_switch, metadata);
  if (!session.ok()) {
    LOG(WARNING)
        << "P4RT session could not be established to clear tables. This is "
           "expected if no gNMI config has been previously pushed: "
        << session.status();
    return absl::OkStatus();
  }

  RETURN_IF_ERROR(pdpi::ClearEntities(**session));
  RETURN_IF_ERROR(session.value()->Finish());
  return absl::OkStatus();
}

// Wrapper around `TestGnoiSystemColdReboot` that ensures we don't ignore fatal
// failures.
absl::Status Reboot(thinkit::Switch& thinkit_switch) {
  if (::testing::Test::HasFatalFailure()) {
    return gutil::UnknownErrorBuilder()
           << "skipping switch reboot due to pre-existing, fatal test failure";
  }
  TestGnoiSystemColdReboot(thinkit_switch);
  if (::testing::Test::HasFatalFailure()) {
    return gutil::UnknownErrorBuilder()
           << "switch reboot failed with fatal error";
  }
  return absl::OkStatus();
}

absl::StatusOr<std::unique_ptr<pdpi::P4RuntimeSession>>
CreateP4RuntimeSessionAndOptionallyPushP4Info(
    thinkit::Switch& thinkit_switch,
    const std::optional<p4::config::v1::P4Info>& p4info,
    const pdpi::P4RuntimeSessionOptionalArgs& metadata) {
  ASSIGN_OR_RETURN(std::unique_ptr<pdpi::P4RuntimeSession> session,
                   pdpi::P4RuntimeSession::Create(thinkit_switch, metadata));

  if (p4info.has_value()) {
    // Check if P4Info already exists, and if so reboot to workaround PINS
    // limitations (b/200209778).
    ASSIGN_OR_RETURN(p4::v1::GetForwardingPipelineConfigResponse response,
                     pdpi::GetForwardingPipelineConfig(session.get()));
    ASSIGN_OR_RETURN(std::string p4info_diff,
                     gutil::ProtoDiff(response.config().p4info(), *p4info));
    if (response.config().has_p4info() && !p4info_diff.empty()) {
      LOG(WARNING)
          << "Rebooting since P4Info reconfiguration is unsupported by PINS, "
             "but I am asked to push a P4Info with the following diff:\n"
          << p4info_diff;
      RETURN_IF_ERROR(session->Finish());
      RETURN_IF_ERROR(Reboot(thinkit_switch));
      // Reconnect after reboot.
      ASSIGN_OR_RETURN(
          session, pdpi::P4RuntimeSession::Create(thinkit_switch, metadata));
    }

    // Push P4Info.
    RETURN_IF_ERROR(pdpi::SetMetadataAndSetForwardingPipelineConfig(
        session.get(),
        p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
        *p4info));
  }

  RETURN_IF_ERROR(pdpi::CheckNoEntities(*session));
  return session;
}

// Uses the `port_map` to remap any P4runtime ports in `entries`.
absl::Status RewritePortsInTableEntries(
    const pdpi::IrP4Info& info, std::vector<pdpi::IrTableEntry>& entries,
    const absl::flat_hash_map<P4rtPortId, P4rtPortId>& port_map) {
  p4::config::v1::P4NamedType port_type;
  port_type.set_name(kPortNamedType);
  RETURN_IF_ERROR(pdpi::TransformValuesOfType(
      info, port_type, entries,
      [&](absl::string_view old_string_port) -> absl::StatusOr<std::string> {
        ASSIGN_OR_RETURN(P4rtPortId old_port,
                         P4rtPortId::MakeFromP4rtEncoding(old_string_port));
        ASSIGN_OR_RETURN(P4rtPortId new_port,
                         gutil::FindOrStatus(port_map, old_port));
        return new_port.GetP4rtEncoding();
      }));

  // Watch ports do not have a named type, but we still consider them ports so
  // we have to deal with them specifically rather than using the generic
  // rewriting function above.
  for (pdpi::IrTableEntry& entry : entries) {
    if (entry.has_action_set()) {
      for (auto& action : *entry.mutable_action_set()->mutable_actions()) {
        if (!action.watch_port().empty()) {
          ASSIGN_OR_RETURN(
              P4rtPortId old_watch_port,
              P4rtPortId::MakeFromP4rtEncoding(action.watch_port()));
          ASSIGN_OR_RETURN(P4rtPortId new_watch_port,
                           gutil::FindOrStatus(port_map, old_watch_port));
          *action.mutable_watch_port() = new_watch_port.GetP4rtEncoding();
        }
      }
    }
  }

  return absl::OkStatus();
}

}  // namespace

absl::StatusOr<std::unique_ptr<pdpi::P4RuntimeSession>>
ConfigureSwitchAndReturnP4RuntimeSession(
    thinkit::Switch& thinkit_switch,
    const std::optional<absl::string_view>& gnmi_config,
    const std::optional<p4::config::v1::P4Info>& p4info,
    const pdpi::P4RuntimeSessionOptionalArgs& metadata) {
  // Since the gNMI Config push relies on tables being cleared, we construct a
  // P4RuntimeSession and clear the tables first.
  RETURN_IF_ERROR(TryClearingEntities(thinkit_switch, metadata));

  // Push gNMI config only if it is supported
  // TODO(PINS): To be removed when gNMI push config is supported
  if (absl::GetFlag(FLAGS_gnmi_push_support)) {
    if (gnmi_config.has_value()) {
      RETURN_IF_ERROR(PushGnmiConfig(thinkit_switch, *gnmi_config));
    }
  }

  ASSIGN_OR_RETURN(auto p4rt_session,
                   CreateP4RuntimeSessionAndOptionallyPushP4Info(
                       thinkit_switch, p4info, metadata));

  // Ensure that the P4RT port IDs configured on the switch are reflected in the
  // state before returning.
  ASSIGN_OR_RETURN(std::unique_ptr<gnmi::gNMI::StubInterface> gnmi_stub,
                   thinkit_switch.CreateGnmiStub());
  RETURN_IF_ERROR(
      WaitForGnmiPortIdConvergence(*gnmi_stub,
                                   /*gnmi_timeout=*/kGnmiTimeoutDefault));
  return p4rt_session;
}

absl::StatusOr<std::pair<std::unique_ptr<pdpi::P4RuntimeSession>,
                         std::unique_ptr<pdpi::P4RuntimeSession>>>
ConfigureSwitchPairAndReturnP4RuntimeSessionPair(
    thinkit::Switch& thinkit_switch1, thinkit::Switch& thinkit_switch2,
    const std::optional<absl::string_view>& gnmi_config,
    const std::optional<p4::config::v1::P4Info>& p4info,
    const pdpi::P4RuntimeSessionOptionalArgs& metadata) {
  // We configure both switches in parallel, since it may require rebooting the
  // switch which is costly.
  using T = absl::StatusOr<std::unique_ptr<pdpi::P4RuntimeSession>>;
  T session1, session2;
  {
    std::future<T> future1 = std::async(std::launch::async, [&] {
      return ConfigureSwitchAndReturnP4RuntimeSession(
          thinkit_switch1, gnmi_config, p4info, metadata);
    });
    std::future<T> future2 = std::async(std::launch::async, [&] {
      return ConfigureSwitchAndReturnP4RuntimeSession(
          thinkit_switch2, gnmi_config, p4info, metadata);
    });
    session1 = future1.get();
    session2 = future2.get();
  }
  RETURN_IF_ERROR(session1.status()).SetPrepend()
      << "failed to configure switch '" << thinkit_switch1.ChassisName()
      << "': ";
  RETURN_IF_ERROR(session2.status()).SetPrepend()
      << "failed to configure switch '" << thinkit_switch2.ChassisName()
      << "': ";
  return std::make_pair(std::move(*session1), std::move(*session2));
}

absl::Status ConfigureSwitchPair(
    thinkit::Switch& thinkit_switch1, thinkit::Switch& thinkit_switch2,
    const std::optional<absl::string_view>& gnmi_config,
    const std::optional<p4::config::v1::P4Info>& p4info,
    const pdpi::P4RuntimeSessionOptionalArgs& metadata) {
  return ConfigureSwitchPairAndReturnP4RuntimeSessionPair(
             thinkit_switch1, thinkit_switch2, std::move(gnmi_config),
             std::move(p4info), metadata)
      .status();
}

absl::Status MirrorSutP4rtPortIdConfigToControlSwitch(
    thinkit::MirrorTestbed& testbed,
    absl::Duration config_convergence_timeout_per_switch) {
  ASSIGN_OR_RETURN(std::unique_ptr<gnmi::gNMI::StubInterface> sut_gnmi_stub,
                   testbed.Sut().CreateGnmiStub());
  ASSIGN_OR_RETURN(std::unique_ptr<gnmi::gNMI::StubInterface> control_gnmi_stub,
                   testbed.ControlSwitch().CreateGnmiStub());

  ASSIGN_OR_RETURN(const pins_test::openconfig::Interfaces sut_interfaces,
                   pins_test::GetInterfacesAsProto(*sut_gnmi_stub,
                                                   gnmi::GetRequest::CONFIG));
  RETURN_IF_ERROR(
      pins_test::SetInterfaceP4rtIds(*control_gnmi_stub, sut_interfaces));

  // Ensure that the SUT and control switch gNMI state paths have converged to
  // match their expected configurations.
  RETURN_IF_ERROR(pins_test::WaitForGnmiPortIdConvergence(
                      *sut_gnmi_stub, config_convergence_timeout_per_switch))
          .SetPrepend()
      << "P4RT port IDs did not converge on SUT within "
      << config_convergence_timeout_per_switch << ": ";
  RETURN_IF_ERROR(
      pins_test::WaitForGnmiPortIdConvergence(
          *control_gnmi_stub, config_convergence_timeout_per_switch))
          .SetPrepend()
      << "P4RT port IDs did not converge on control switch within "
      << config_convergence_timeout_per_switch << ": ";
  return absl::OkStatus();
}

// Reads the enabled interfaces from the switch and waits up to `timeout` until
// they are all up. Calls `on_failure` prior to returning status if it is not
// OK.
absl::Status WaitForEnabledInterfacesToBeUp(
    thinkit::Switch& thinkit_switch, absl::Duration timeout,
    std::optional<
        std::function<void(const openconfig::Interfaces& enabled_interfaces)>>
        on_failure) {
  absl::Time start = absl::Now();
  ASSIGN_OR_RETURN(std::unique_ptr<gnmi::gNMI::StubInterface> gnmi_stub,
                   thinkit_switch.CreateGnmiStub());

  // Get all enabled interfaces from the config.
  ASSIGN_OR_RETURN(const pins_test::openconfig::Interfaces enabled_interfaces,
                   pins_test::GetMatchingInterfacesAsProto(
                       *gnmi_stub, gnmi::GetRequest::CONFIG,
                       /*predicate=*/
                       [](const openconfig::Interfaces::Interface& interface) {
                         return interface.config().enabled();
                       },
                       timeout));

  std::vector<std::string> enabled_interface_names;
  enabled_interface_names.reserve(enabled_interfaces.interfaces_size());
  for (const auto& interface : enabled_interfaces.interfaces())
    enabled_interface_names.push_back(interface.name());

  // Wait for all enabled interfaces to be up.
  timeout = timeout - (absl::Now() - start);
  if (on_failure.has_value()) {
    return pins_test::OnFailure(
        pins_test::WaitForCondition(pins_test::PortsUp, timeout, thinkit_switch,
                                    enabled_interface_names,
                                    /*with_healthz=*/false),
        /*on_failure=*/[&]() { (*on_failure)(enabled_interfaces); });
  }
  return pins_test::WaitForCondition(pins_test::PortsUp, timeout,
                                     thinkit_switch, enabled_interface_names,
                                     /*with_healthz=*/false);
}

// Gets every P4runtime port used in `entries`.
absl::StatusOr<absl::btree_set<P4rtPortId>> GetPortsUsed(
    const pdpi::IrP4Info& info, std::vector<pdpi::IrTableEntry> entries) {
  absl::btree_set<P4rtPortId> ports;
  p4::config::v1::P4NamedType port_type;
  port_type.set_name(kPortNamedType);
  RETURN_IF_ERROR(pdpi::VisitValuesOfType(
      info, port_type, entries,
      /*visitor=*/[&](absl::string_view string_port) -> absl::Status {
        ASSIGN_OR_RETURN(P4rtPortId port,
                         P4rtPortId::MakeFromP4rtEncoding(string_port));
        ports.insert(port);
        return absl::OkStatus();
      }));

  // Watch ports do not have a named type, but we still consider them ports so
  // we have to deal with them specifically rather than using the generic
  // function above.
  for (pdpi::IrTableEntry& entry : entries) {
    if (entry.has_action_set()) {
      for (const auto& action : entry.action_set().actions()) {
        if (!action.watch_port().empty()) {
          ASSIGN_OR_RETURN(P4rtPortId port, P4rtPortId::MakeFromP4rtEncoding(
                                                action.watch_port()));
          ports.insert(port);
        }
      }
    }
  }

  return ports;
}

// Remaps ports in a round-robin fashion, but starts by fixing those that are
// both used in `entries` and in `ports`.
absl::Status RewritePortsInTableEntries(
    const pdpi::IrP4Info& info, absl::Span<const P4rtPortId> new_ports,
    std::vector<pdpi::IrTableEntry>& entries) {
  if (new_ports.empty()) {
    return absl::InvalidArgumentError("`new_ports` may not be empty");
  }

  // We get the ports used in the original entries so we can preserve any that
  // exist in both, and then remap them in a round-robin fashion.
  ASSIGN_OR_RETURN(absl::btree_set<P4rtPortId> ports_used_originally,
                   GetPortsUsed(info, entries));

  absl::flat_hash_map<P4rtPortId, P4rtPortId> old_to_new_port_id;
  // Queue of which new port to map an old port to next.
  std::deque<P4rtPortId> new_port_queue;

  for (const P4rtPortId& new_port : new_ports) {
    if (ports_used_originally.contains(new_port)) {
      // Make sure that existing ports are preserved and add them to the back of
      // the queue for balancing.
      old_to_new_port_id[new_port] = new_port;
      new_port_queue.push_back(new_port);
    } else {
      new_port_queue.push_front(new_port);
    }
  }

  // Map all old ports to new ports.
  for (const auto& old_port : ports_used_originally) {
    // If a port is already mapped, we should not remap it.
    if (old_to_new_port_id.contains(old_port)) continue;
    P4rtPortId new_port = std::move(new_port_queue.front());
    new_port_queue.pop_front();
    new_port_queue.push_back(new_port);
    old_to_new_port_id[old_port] = new_port;
  }

  return RewritePortsInTableEntries(info, entries, old_to_new_port_id);
}

absl::Status RewritePortsInTableEntries(
    const pdpi::IrP4Info& info, absl::string_view gnmi_config,
    std::vector<pdpi::IrTableEntry>& entries) {
  ASSIGN_OR_RETURN(absl::btree_set<std::string> valid_port_ids_set,
                   GetAllPortIds(gnmi_config));

  if (valid_port_ids_set.empty()) {
    return absl::InvalidArgumentError(
        "given gnmi_config had no valid port ids");
  }

  std::vector<P4rtPortId> new_ports;
  new_ports.reserve(valid_port_ids_set.size());
  for (const std::string& port_id : valid_port_ids_set) {
    ASSIGN_OR_RETURN(new_ports.emplace_back(),
                     P4rtPortId::MakeFromP4rtEncoding(port_id));
  }

  return RewritePortsInTableEntries(info, new_ports, entries);
}

absl::Status RewritePortsInTableEntriesToEnabledEthernetPorts(
    const pdpi::IrP4Info& info, gnmi::gNMI::StubInterface& gnmi_stub,
    std::vector<pdpi::IrTableEntry>& entries) {
  ASSIGN_OR_RETURN(std::vector<P4rtPortId> valid_port_ids,
                   pins_test::GetMatchingP4rtPortIds(
                       gnmi_stub, pins_test::IsEnabledEthernetInterface));

  if (valid_port_ids.empty()) {
    return absl::InvalidArgumentError(
        "no enabled, ethernet ports were mapped on the switch");
  }

  return RewritePortsInTableEntries(info, valid_port_ids, entries);
}

absl::Status ConfigureSwitch(
    thinkit::Switch& thinkit_switch, const PinsConfigView& config,
    const pdpi::P4RuntimeSessionOptionalArgs& metadata) {
  return gutil::StatusBuilder(
             ConfigureSwitchAndReturnP4RuntimeSession(
                 thinkit_switch, config.gnmi_config, config.p4info, metadata)
                 .status())
             .SetPrepend()
         << "failed to configure switch '" << thinkit_switch.ChassisName()
         << "': ";
}

absl::Status ConfigureSwitchPair(
    thinkit::Switch& switch1, const PinsConfigView& config1,
    thinkit::Switch& switch2, const PinsConfigView& config2,
    const pdpi::P4RuntimeSessionOptionalArgs& metadata) {
  // We configure both switches in parallel, since it may require rebooting the
  // switch which is costly.
  std::future<absl::Status> future1 = std::async(std::launch::async, [&] {
    return ConfigureSwitch(switch1, config1, metadata);
  });
  std::future<absl::Status> future2 = std::async(std::launch::async, [&] {
    return ConfigureSwitch(switch2, config2, metadata);
  });
  absl::Status status = future1.get();
  status.Update(future2.get());
  return status;
}

namespace {
absl::StatusOr<absl::btree_map<std::string, P4rtPortId>>
UpPorts(gnmi::gNMI::StubInterface &gnmi_stub) {
  ASSIGN_OR_RETURN(const auto interface_id_map,
                   GetAllInterfaceNameToPortId(gnmi_stub));
  ASSIGN_OR_RETURN(
      const auto up_interfaces,
      GetUpInterfacesOverGnmi(gnmi_stub, InterfaceType::kSingleton));

  absl::btree_map<std::string, P4rtPortId> ports;
  for (const std::string &interface : up_interfaces) {
    auto lookup = interface_id_map.find(interface);
    if (lookup == interface_id_map.end()) {
      return gutil::NotFoundErrorBuilder()
             << "Interface '"
             << interface << "' was reported up but has no port id mapping.";
    }
    ASSIGN_OR_RETURN(P4rtPortId port_id,
                     P4rtPortId::MakeFromP4rtEncoding(lookup->second));
    ports.insert(std::make_pair(interface, std::move(port_id)));
  }
  return ports;
}
} // namespace

absl::StatusOr<std::vector<MirroredPort>>
MirroredPorts(thinkit::MirrorTestbed &testbed) {
  ASSIGN_OR_RETURN(auto sut_gnmi_stub, testbed.Sut().CreateGnmiStub());
  ASSIGN_OR_RETURN(auto control_switch_gnmi_stub,
                   testbed.ControlSwitch().CreateGnmiStub());

  return MirroredPorts(*sut_gnmi_stub, *control_switch_gnmi_stub);
}

absl::StatusOr<std::vector<MirroredPort>>
MirroredPorts(gnmi::gNMI::StubInterface &sut_gnmi_stub,
              gnmi::gNMI::StubInterface &control_switch_gnmi_stub) {
  ASSIGN_OR_RETURN(auto sut_ports, UpPorts(sut_gnmi_stub),
                   _ << "Failed to lookup operational ports from the SUT.");

  ASSIGN_OR_RETURN(
      auto control_switch_ports, UpPorts(control_switch_gnmi_stub),
      _ << "Failed to lookup operational ports from the Control Switch.");
  std::vector<MirroredPort> mirrored_ports;
  for (const auto &[interface, port] : control_switch_ports) {
    auto lookup = sut_ports.find(interface);
    if (lookup == sut_ports.end())
      continue;
    mirrored_ports.push_back({
        .interface = interface,
        .sut = lookup->second,
        .control_switch = port,
    });
  }
  return mirrored_ports;
}

}  // namespace pins_test
