#include "tests/lib/switch_test_setup_helpers.h"

#include <deque>
#include <functional>
#include <future>  // NOLINT: third_party library.
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "absl/types/optional.h"
#include "absl/types/span.h"
#include "glog/logging.h"
#include "gutil/collections.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/gnmi/openconfig.pb.h"
#include "lib/validator/validator_lib.h"
#include "p4/config/v1/p4types.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir_tools.h"
#include "p4_pdpi/p4_runtime_session.h"

namespace pins_test {
namespace {

constexpr absl::Duration kGnmiTimeoutDefault = absl::Minutes(3);
constexpr char kPortNamedType[] = "port_id_t";

absl::StatusOr<std::unique_ptr<pdpi::P4RuntimeSession>>
CreateP4RuntimeSessionAndClearExistingState(
    thinkit::Switch& thinkit_switch,
    const pdpi::P4RuntimeSessionOptionalArgs& metadata) {
  ASSIGN_OR_RETURN(std::unique_ptr<pdpi::P4RuntimeSession> session,
                   pdpi::P4RuntimeSession::Create(thinkit_switch, metadata));
  RETURN_IF_ERROR(pdpi::ClearTableEntries(session.get()));
  RETURN_IF_ERROR(pdpi::CheckNoTableEntries(session.get())).SetPrepend()
      << "cleared all table entries: ";
  return session;
}

absl::Status PushGnmiAndWaitForConvergence(thinkit::Switch& thinkit_switch,
                                           const std::string& gnmi_config,
                                           absl::Duration gnmi_timeout) {
  RETURN_IF_ERROR(PushGnmiConfig(thinkit_switch, gnmi_config));
  return WaitForGnmiPortIdConvergence(thinkit_switch, gnmi_config,
                                      gnmi_timeout);
}

absl::Status SetForwardingPipelineConfigAndAssureClearedTables(
    pdpi::P4RuntimeSession* session, const p4::config::v1::P4Info& p4info) {
  RETURN_IF_ERROR(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      session, p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      p4info));
  RETURN_IF_ERROR(pdpi::CheckNoTableEntries(session)).SetPrepend()
      << "set a new forwarding pipeline config: ";
  return absl::OkStatus();
}

// Uses the `port_map` to remap any P4runtime ports in `entries`.
absl::Status RewritePortsInTableEntries(
    const pdpi::IrP4Info& info, std::vector<pdpi::IrTableEntry>& entries,
    const absl::flat_hash_map<std::string, std::string>& port_map) {
  p4::config::v1::P4NamedType port_type;
  port_type.set_name(kPortNamedType);
  RETURN_IF_ERROR(pdpi::TransformValuesOfType(
      info, port_type, entries, [&](absl::string_view old_port) {
        return gutil::FindOrStatus(port_map, std::string(old_port));
      }));

  // Watch ports do not have a named type, but we still consider them ports so
  // we have to deal with them specifically rather than using the generic
  // rewriting function above.
  for (pdpi::IrTableEntry& entry : entries) {
    if (entry.has_action_set()) {
      for (auto& action : *entry.mutable_action_set()->mutable_actions()) {
        if (!action.watch_port().empty()) {
          ASSIGN_OR_RETURN(*action.mutable_watch_port(),
                           gutil::FindOrStatus(port_map, action.watch_port()));
        }
      }
    }
  }

  return absl::OkStatus();
}

}  // namespace

absl::StatusOr<std::unique_ptr<pdpi::P4RuntimeSession>>
ConfigureSwitchAndReturnP4RuntimeSession(
    thinkit::Switch& thinkit_switch, std::optional<std::string> gnmi_config,
    std::optional<p4::config::v1::P4Info> p4info,
    const pdpi::P4RuntimeSessionOptionalArgs& metadata) {
  // Since the gNMI Config push relies on tables being cleared, we construct a
  // P4RuntimeSession and clear the tables first.
  ASSIGN_OR_RETURN(
      std::unique_ptr<pdpi::P4RuntimeSession> session,
      CreateP4RuntimeSessionAndClearExistingState(thinkit_switch, metadata));

  if (gnmi_config.has_value()) {
    RETURN_IF_ERROR(
        PushGnmiAndWaitForConvergence(thinkit_switch, *gnmi_config,
                                      /*gnmi_timeout=*/kGnmiTimeoutDefault));
  }

  if (p4info.has_value()) {
    RETURN_IF_ERROR(SetForwardingPipelineConfigAndAssureClearedTables(
        session.get(), *p4info));
  }

  return session;
}

absl::StatusOr<std::pair<std::unique_ptr<pdpi::P4RuntimeSession>,
                         std::unique_ptr<pdpi::P4RuntimeSession>>>
ConfigureSwitchPairAndReturnP4RuntimeSessionPair(
    thinkit::Switch& thinkit_switch1, thinkit::Switch& thinkit_switch2,
    std::optional<std::string> gnmi_config,
    std::optional<p4::config::v1::P4Info> p4info,
    const pdpi::P4RuntimeSessionOptionalArgs& metadata) {
  // Since the gNMI Config push relies on tables being cleared, we construct the
  // P4RuntimeSessions and clear the tables first.
  ASSIGN_OR_RETURN(
      std::unique_ptr<pdpi::P4RuntimeSession> session1,
      CreateP4RuntimeSessionAndClearExistingState(thinkit_switch1, metadata));
  ASSIGN_OR_RETURN(
      std::unique_ptr<pdpi::P4RuntimeSession> session2,
      CreateP4RuntimeSessionAndClearExistingState(thinkit_switch2, metadata));

  if (gnmi_config.has_value()) {
    // Push the gNMI configs to both switches before waiting for convergence.
    RETURN_IF_ERROR(PushGnmiConfig(thinkit_switch1, *gnmi_config));
    RETURN_IF_ERROR(PushGnmiConfig(thinkit_switch2, *gnmi_config));
    RETURN_IF_ERROR(WaitForGnmiPortIdConvergence(thinkit_switch1, *gnmi_config,
                                                 kGnmiTimeoutDefault));
    RETURN_IF_ERROR(WaitForGnmiPortIdConvergence(thinkit_switch2, *gnmi_config,
                                                 kGnmiTimeoutDefault));
  }

  if (p4info.has_value()) {
    RETURN_IF_ERROR(SetForwardingPipelineConfigAndAssureClearedTables(
        session1.get(), *p4info));
    RETURN_IF_ERROR(SetForwardingPipelineConfigAndAssureClearedTables(
        session2.get(), *p4info));
  }

  return std::make_pair(std::move(session1), std::move(session2));
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
absl::StatusOr<absl::btree_set<std::string>> GetPortsUsed(
    const pdpi::IrP4Info& info, std::vector<pdpi::IrTableEntry> entries) {
  absl::btree_set<std::string> ports;
  p4::config::v1::P4NamedType port_type;
  port_type.set_name(kPortNamedType);
  RETURN_IF_ERROR(pdpi::TransformValuesOfType(info, port_type, entries,
                                              [&](absl::string_view port) {
                                                ports.insert(std::string(port));
                                                return std::string(port);
                                              }));

  // Watch ports do not have a named type, but we still consider them ports so
  // we have to deal with them specifically rather than using the generic
  // function above.
  for (pdpi::IrTableEntry& entry : entries) {
    if (entry.has_action_set()) {
      for (const auto& action : entry.action_set().actions()) {
        if (!action.watch_port().empty()) {
          ports.insert(action.watch_port());
        }
      }
    }
  }

  return ports;
}

// Remaps ports in a round-robin fashion, but starts by fixing those that are
// both used in `entries` and in `ports`.
absl::Status RewritePortsInTableEntries(
    const pdpi::IrP4Info& info, absl::Span<const std::string> new_ports,
    std::vector<pdpi::IrTableEntry>& entries) {
  if (new_ports.empty()) {
    return absl::InvalidArgumentError("`new_ports` may not be empty");
  }

  // We get the ports used in the original entries so we can preserve any that
  // exist in both, and then remap them in a round-robin fashion.
  ASSIGN_OR_RETURN(absl::btree_set<std::string> ports_used_originally,
                   GetPortsUsed(info, entries));

  absl::flat_hash_map<std::string, std::string> old_to_new_port_id;
  // Queue of which new port to map an old port to next.
  std::deque<std::string> new_port_queue;

  for (const auto& new_port : new_ports) {
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
    const std::string new_port = new_port_queue.front();
    old_to_new_port_id[old_port] = new_port;
    new_port_queue.pop_front();
    new_port_queue.push_back(new_port);
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

  std::vector<std::string> new_ports(valid_port_ids_set.begin(),
                                     valid_port_ids_set.end());
  return RewritePortsInTableEntries(info, new_ports, entries);
}

}  // namespace pins_test
