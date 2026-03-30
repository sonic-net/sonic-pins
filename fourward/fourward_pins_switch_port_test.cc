// TDD: Port identity in P4-simulated PINS switches.
//
// These tests verify the port mapping contracts from
// designs/port_identity.md. All DISABLED until implemented.

#include "fourward/fourward_switch.h"

#include <memory>
#include <string>

#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "lib/gnmi/gnmi_helper.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_runtime/p4_runtime_session.h"
#include "p4_infra/p4_runtime/p4_runtime_session_extras.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"

namespace dvaas {
namespace {

// ---------------------------------------------------------------------------
// Test 1: gNMI Set converges
// ---------------------------------------------------------------------------

// After remapping port IDs via gNMI Set, the state path must converge.
// DVaaS depends on this — it calls WaitForEnabledEthernetInterfacesToBeUp
// after mirroring SUT port config to the control switch.
TEST(FourwardPinsSwitchPortTest,
     DISABLED_GnmiSetConverges) {
  ASSERT_OK_AND_ASSIGN(FourwardSwitch switch_a, FourwardSwitch::Create());

  // Read initial gNMI state — "Ethernet0" has P4RT ID "1".
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<gnmi::gNMI::StubInterface> gnmi_stub,
      switch_a.CreateGnmiStub());

  // Remap "Ethernet0" to P4RT ID "5" via gNMI Set.
  // TODO: Implement gNMI Set for port ID changes in FakeGnmiService.

  // Verify convergence: WaitForEnabledEthernetInterfacesToBeUp succeeds.
  ASSERT_OK(pins_test::WaitForEnabledEthernetInterfacesToBeUp(switch_a));
}

// ---------------------------------------------------------------------------
// Test 2: gNMI-reported P4RT IDs work in P4Runtime
// ---------------------------------------------------------------------------

// Read P4RT port ID from gNMI, use it in a table entry, verify the
// packet uses the correct port. Tests the gNMI → P4RT → dataplane chain.
TEST(FourwardPinsSwitchPortTest,
     DISABLED_GnmiReportedP4rtIdsWorkInP4Runtime) {
  // TODO: Load pipeline, read P4RT ID from gNMI for "Ethernet0",
  // install forwarding entry using that P4RT ID, inject packet,
  // verify it exits on the correct port.
}

// ---------------------------------------------------------------------------
// Test 3: Bridge routes by interface name
// ---------------------------------------------------------------------------

// Two switches with DIFFERENT P4RT IDs for "Ethernet0". A packet exits
// SUT's "Ethernet0" and must arrive on control's "Ethernet0" — even
// though the dataplane port numbers differ.
TEST(FourwardPinsSwitchPortTest,
     DISABLED_BridgeRoutesByInterfaceName) {
  // SUT: "Ethernet0" → P4RT ID "1" (dataplane port 1)
  ASSERT_OK_AND_ASSIGN(FourwardSwitch sut,
                        FourwardSwitch::Create(/*device_id=*/1));

  // Control: "Ethernet0" → P4RT ID "5" (dataplane port 5)
  // TODO: Create with custom FakeInterface list where Ethernet0 has
  // p4rt_id = 5.
  ASSERT_OK_AND_ASSIGN(FourwardSwitch control,
                        FourwardSwitch::Create(/*device_id=*/2));

  // TODO: Start PacketBridge between them.
  // TODO: Install forwarding on SUT to output on SUT's "Ethernet0".
  // TODO: Inject packet on SUT.
  // TODO: Verify packet arrives on control's "Ethernet0" (dataplane
  //   port 5, NOT dataplane port 1).
}

// ---------------------------------------------------------------------------
// Test 4: gNMI Set + P4Runtime (the DVaaS flow)
// ---------------------------------------------------------------------------

// Remap ports via gNMI Set, then install entries using the new P4RT IDs.
// This is what DVaaS does: mirror SUT config → clear entries → remap →
// install → send packets.
TEST(FourwardPinsSwitchPortTest,
     DISABLED_GnmiSetThenP4RuntimeWorks) {
  ASSERT_OK_AND_ASSIGN(FourwardSwitch pins_switch, FourwardSwitch::Create());

  // TODO: gNMI Set to change "Ethernet0" from P4RT ID "1" to "5".
  // TODO: Wait for convergence.
  // TODO: Load pipeline, install entry referencing port "5".
  // TODO: Inject packet, verify it exits on the correct port.
}

// ---------------------------------------------------------------------------
// Test 5: Unmapped port → drop
// ---------------------------------------------------------------------------

// Forward to a P4RT port ID that has no corresponding gNMI interface.
// The packet should be dropped (with a warning), not forwarded.
TEST(FourwardPinsSwitchPortTest,
     DISABLED_UnmappedPortDropsPacket) {
  ASSERT_OK_AND_ASSIGN(FourwardSwitch pins_switch, FourwardSwitch::Create());

  // TODO: Load pipeline, install entry that forwards to port "999"
  //   (no gNMI interface has this P4RT ID).
  // TODO: Inject packet.
  // TODO: Verify packet is dropped (no output).
}

}  // namespace
}  // namespace dvaas
