#ifndef PINS_TESTS_LIB_SWITCH_TEST_SETUP_HELPERS_H_
#define PINS_TESTS_LIB_SWITCH_TEST_SETUP_HELPERS_H_

#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/btree_set.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "lib/gnmi/openconfig.pb.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/switch.h"

namespace pins_test {

// Configures the switch and sets up a P4 Runtime Session. If you don't have
// particular requirements, this is likely the function you want to use.
// Specifically:
// * Creates a session.
// * Clears all tables.
// * Pushes the given `gnmi_config`, if any, and waits for the switch to
//   converge.
// * Pushes the given P4Info, if any, via RECONCILE_AND_COMMIT.
absl::StatusOr<std::unique_ptr<pdpi::P4RuntimeSession>>
ConfigureSwitchAndReturnP4RuntimeSession(
    thinkit::Switch &thinkit_switch, std::optional<std::string> gnmi_config,
    std::optional<p4::config::v1::P4Info> p4info,
    const pdpi::P4RuntimeSessionOptionalArgs &metadata = {});

// Configures a pair of switches and sets up P4 Runtime Sessions. If you are
// setting up a pair of switches (e.g. in a mirror testbed) with the same gNMI
// config and P4Info and want to wait for the gNMI configs to converge in
// parallel, this is likely the function that you should use. Specifically, it:
// * Creates two sessions.
// * Clears all tables.
// * Pushes the given `gnmi_config`, if any, and waits for the switches to
//   converge.
// * Pushes the given `p4info`, if any,  via RECONCILE_AND_COMMIT.
absl::StatusOr<std::pair<std::unique_ptr<pdpi::P4RuntimeSession>,
                         std::unique_ptr<pdpi::P4RuntimeSession>>>
ConfigureSwitchPairAndReturnP4RuntimeSessionPair(
    thinkit::Switch &thinkit_switch1, thinkit::Switch &thinkit_switch2,
    std::optional<std::string> gnmi_config,
    std::optional<p4::config::v1::P4Info> p4info,
    const pdpi::P4RuntimeSessionOptionalArgs &metadata = {});

// Mirrors the P4RT port IDs of the SUT onto the control switch and ensures that
// the state of the switch is properly updated (i.e. that the IDs are reflected
// in the gNMI state path).
absl::Status MirrorSutP4rtPortIdConfigToControlSwitch(
    thinkit::MirrorTestbed &testbed,
    absl::Duration config_convergence_timeout_per_switch = absl::Minutes(5));

// Reads the enabled interfaces from the switch and waits up to `timeout` until
// they are all up. Calls `on_failure` prior to returning status if it is not
// OK.
absl::Status WaitForEnabledInterfacesToBeUp(
    thinkit::Switch &thinkit_switch, absl::Duration timeout = absl::Minutes(5),
    std::optional<
        std::function<void(const openconfig::Interfaces &enabled_interfaces)>>
        on_failure = std::nullopt);

// Gets a count of which P4runtime ports are used in `entries` and how
// frequently.
absl::StatusOr<absl::btree_set<std::string>>
GetPortsUsed(const pdpi::IrP4Info &info,
             std::vector<pdpi::IrTableEntry> entries);

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
absl::Status
RewritePortsInTableEntries(const pdpi::IrP4Info &info,
                           absl::Span<const std::string> new_ports,
                           std::vector<pdpi::IrTableEntry> &entries);

// Extracts the available ports from the given `gnmi_config` and rewrites
// entries as per above.
absl::Status
RewritePortsInTableEntries(const pdpi::IrP4Info &info,
                           absl::string_view gnmi_config,
                           std::vector<pdpi::IrTableEntry> &entries);

} // namespace pins_test

#endif // PINS_TESTS_LIB_SWITCH_TEST_SETUP_HELPERS_H_
