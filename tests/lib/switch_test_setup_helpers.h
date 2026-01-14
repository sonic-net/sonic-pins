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

#ifndef PINS_TESTS_LIB_SWITCH_TEST_SETUP_HELPERS_H_
#define PINS_TESTS_LIB_SWITCH_TEST_SETUP_HELPERS_H_

#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/base/attributes.h"
#include "absl/container/btree_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "lib/gnmi/openconfig.pb.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/switch.h"

namespace pins_test {

// A `const&`-like view of a complete or partial PINS config, meaning the
// `gnmi_config` and `p4info` are optional.
struct PinsConfigView {
  // TODO: We would like this to be a string_view, but are running into
  // hard to debug lifetime issues.
  std::optional<std::string> gnmi_config;
  std::optional<p4::config::v1::P4Info> p4info;
};

// Configures the given switch. If you don't have particular requirements, this
// is likely the function you want to use. Specifically:
// * Creates a P4Runtime session.
// * Clears all P4Runtime entities.
// * Pushes the given `gnmi_config`, if any, and waits for the switch to
//   converge.
// * Pushes the given P4Info, if any, via RECONCILE_AND_COMMIT.
absl::Status ConfigureSwitch(
    thinkit::Switch& thinkit_switch, const PinsConfigView& config,
    const pdpi::P4RuntimeSessionOptionalArgs& metadata = {});

// Like `ConfigureSwitch`, but for 2 switches in parallel.
absl::Status ConfigureSwitchPair(
    thinkit::Switch& switch1, const PinsConfigView& config1,
    thinkit::Switch& switch2, const PinsConfigView& config2,
    const pdpi::P4RuntimeSessionOptionalArgs& metadata = {});

// Reads the enabled interfaces from the switch and waits up to `timeout` until
// they are all up. Calls `on_failure` prior to returning status if it is not
// OK.
absl::Status WaitForEnabledInterfacesToBeUp(
    thinkit::Switch& thinkit_switch, absl::Duration timeout = absl::Minutes(5),
    std::optional<
        std::function<void(const openconfig::Interfaces& enabled_interfaces)>>
        on_failure = std::nullopt);

// Reads the enabled ethernet interfaces from the switch and waits up to
// `timeout` until they are all up.
absl::Status WaitForEnabledEthernetInterfacesToBeUp(
    thinkit::Switch& thinkit_switch, absl::Duration timeout = absl::Minutes(5));

// Gets the set of P4 Runtime port IDs used in `entries`.
absl::StatusOr<absl::btree_set<P4rtPortId>> GetPortsUsed(
    const pdpi::IrP4Info& info, std::vector<pdpi::IrTableEntry> entries);

// Gets the set of P4 Runtime port IDs used in `entities`.
absl::StatusOr<absl::btree_set<P4rtPortId>> GetPortsUsed(
    const pdpi::IrP4Info& info, std::vector<pdpi::IrEntity> entities);

// Rewrites the ports of the given table `entries` to only use the given
// non-empty `ports`. Uses `info` to determine which values refer to ports.
// Specifically, for each port `x` in the set of table entries, this
// function remaps it to f(x) such that:
// - if `x \in ports` then `f(x) = x`
// - `x` is remapped to an `f(x) \in ports` (chosen deterministically)
//   such that `\forall. p1,p2 \in ports. |{f(x) = p1 | x \in
//   all_ports(entries)}| <= |{f(x) = p2 | x \in all_ports(entries)}| + 1`.
//
// This function makes it possible to use a list of pre-existing table entries
// with any set of ports desired (or configured on the switch).
absl::Status RewritePortsInTableEntries(
    const pdpi::IrP4Info& info, absl::Span<const P4rtPortId> new_ports,
    std::vector<pdpi::IrTableEntry>& entries);

// Extracts the available ports from the given `gnmi_config` and rewrites
// entries as per above.
absl::Status RewritePortsInTableEntries(
    const pdpi::IrP4Info& info, absl::string_view gnmi_config,
    std::vector<pdpi::IrTableEntry>& entries);

// Extracts the available, enabled, ethernet ports from the switch using the
// given `gnmi_stub` and rewrites entries as per above.
absl::Status RewritePortsInTableEntriesToEnabledEthernetPorts(
    const pdpi::IrP4Info& info, gnmi::gNMI::StubInterface& gnmi_stub,
    std::vector<pdpi::IrTableEntry>& entries);

// -- Legacy Mirror Testbed APIs -----------------------------------------------

// Like `ConfigureSwitch`, but also returns the P4Runtime session used during
// configuration.
absl::StatusOr<std::unique_ptr<pdpi::P4RuntimeSession>>
ConfigureSwitchAndReturnP4RuntimeSession(
    thinkit::Switch& thinkit_switch,
    const std::optional<absl::string_view>& gnmi_config,
    const std::optional<p4::config::v1::P4Info>& p4info,
    const pdpi::P4RuntimeSessionOptionalArgs& metadata = {});

// Configures a pair of switches and sets up P4 Runtime Sessions. If you are
// setting up a pair of switches (e.g. in a mirror testbed) with the same gNMI
// config and P4Info and want to wait for the gNMI configs to converge in
// parallel, this is likely the function that you should use. Specifically, it:
// * Creates two sessions.
// * Clears all entities.
// * Pushes the given `gnmi_config`, if any, and waits for the switches to
//   converge.
// * Pushes the given `p4info`, if any,  via RECONCILE_AND_COMMIT.
ABSL_DEPRECATED(
    "Use `ConfigureSwitchPair` instead, since this function works only for "
    "mirror testbeds.")
absl::StatusOr<std::pair<std::unique_ptr<pdpi::P4RuntimeSession>,
                         std::unique_ptr<pdpi::P4RuntimeSession>>>
ConfigureSwitchPairAndReturnP4RuntimeSessionPair(
    thinkit::Switch& thinkit_switch1, thinkit::Switch& thinkit_switch2,
    const std::optional<absl::string_view>& gnmi_config,
    const std::optional<p4::config::v1::P4Info>& p4info,
    const pdpi::P4RuntimeSessionOptionalArgs& metadata = {});

// Like `ConfigureSwitchPairAndReturnP4RuntimeSessionPair`, but does not return
// the P4Runtime sessions created during configuration.
ABSL_DEPRECATED(
    "Use the other `ConfigureSwitchPair` overload since this one only works "
    "for mirror testbeds.")
absl::Status ConfigureSwitchPair(
    thinkit::Switch& thinkit_switch1, thinkit::Switch& thinkit_switch2,
    const std::optional<absl::string_view>& gnmi_config,
    const std::optional<p4::config::v1::P4Info>& p4info,
    const pdpi::P4RuntimeSessionOptionalArgs& metadata = {});

// Mirrors the P4RT port IDs of the SUT onto the control switch and ensures that
// the state of the switch is properly updated (i.e. that the IDs are reflected
// in the gNMI state path).
absl::Status MirrorSutP4rtPortIdConfigToControlSwitch(
    thinkit::MirrorTestbed& testbed,
    absl::Duration config_convergence_timeout_per_switch = absl::Minutes(5));

// Represents a mirrored connection between a SUT and control switch port of the
// same interface name, assuming that the interface name is linked to the
// physical location of the port.
struct MirroredPort {
  std::string interface;
  P4rtPortId sut;
  P4rtPortId control_switch;
};

// Returns the set of operational UP ports that are mirrored between the SUT and
// control switch.
absl::StatusOr<std::vector<MirroredPort>> MirroredPorts(
    thinkit::MirrorTestbed& testbed);

// Same as above but takes in the gRPC stubs directly.
absl::StatusOr<std::vector<MirroredPort>> MirroredPorts(
    gnmi::gNMI::StubInterface& sut_gnmi_stub,
    gnmi::gNMI::StubInterface& control_switch_gnmi_stub);

}  // namespace pins_test

#endif  // PINS_TESTS_LIB_SWITCH_TEST_SETUP_HELPERS_H_
