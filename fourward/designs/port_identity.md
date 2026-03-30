# Port Identity in P4-simulated PINS Switches

**Status: proposal**

## Port identifiers

Ports go by different names depending on who's talking:

| Layer | Real PINS switch | P4-simulated PINS switch |
|---|---|---|
| **Config** | gNMI interface name (e.g. "Ethernet0") | gNMI interface name (same) |
| **API** | P4RT port ID (e.g. "1") | P4RT port ID (same) |
| **Forwarding** | Physical port (hardware) | Dataplane port number (v1model `uint32`) |

Only the config and API layers are user-visible — through gNMI and
P4Runtime respectively. The forwarding layer is internal: on a real
switch it's a hardware port; in the P4 simulator it's the `uint32` in
`standard_metadata.ingress_port` / `egress_port`.

On a real PINS switch, the platform links all three: hardware maps
interface names to physical ports, gNMI config assigns P4RT IDs to
interfaces.

**Problem:** In the P4 simulation, nothing links these identifiers
automatically. We need to design how to manage the port mappings —
establishing them at switch creation, updating them on gNMI Set, and
keeping them consistent across gNMI, P4Runtime, and the dataplane.

**Goal:** The P4-simulated switch should be indistinguishable from a real
PINS switch through the `thinkit::Switch` interface, so that DVaaS works
robustly on both without knowing the difference.

## Requirements

### R1: Internal consistency

Within a single switch, the three identifiers must agree: if gNMI reports
interface "Ethernet0" with P4RT ID "1", then:
- A P4Runtime Write using port "1" affects the port gNMI calls "Ethernet0".
- When a packet exits on that port, the Dataplane service reports it with
  P4RT ID "1" (and dataplane port 1).
- No contradictions across gNMI, P4Runtime, and Dataplane interfaces.

*Why? Real switch behavior. Any switch that contradicts itself is broken.*

### R2: Mirror testbed connectivity

In a mirror testbed, the same gNMI interface name on both switches is
connected via the PacketBridge. SUT's "Ethernet0" connects to control
switch's "Ethernet0". The P4RT IDs and dataplane ports for "Ethernet0"
on each switch are independent — they don't need to match.

*Why? DVaaS assumes the mirror testbed connects matching interfaces by
name (e.g. SUT's "Ethernet0" ↔ control's "Ethernet0").*

### R3: gNMI is the source of truth for naming

gNMI config defines the interface name ↔ P4RT ID mapping.

*Why? Real PINS switch behavior. gNMI is how operators assign P4RT
port IDs to interfaces.*

### R4: gNMI config/state convergence

When a port mapping is changed via gNMI Set (e.g. reassign P4RT ID of an
interface), the state path eventually converges to reflect the new config,
provided no table entries reference the affected P4RT port IDs.

*Why? On a real switch, gNMI config and state converge. DVaaS depends on
this — it calls `WaitForEnabledEthernetInterfacesToBeUp` after mirroring
port configs, polling gNMI state until convergence. The precondition
(no entries referencing old IDs) reflects that a real PINS switch also cannot safely and will not
remap ports with active forwarding entries.*

### R5: Determinism

Given the same gNMI config, the same P4RT IDs and dataplane ports are
assigned every time.

*Why? Design choice for testability. Not a real-switch requirement.*

## Design decisions

### P4RT ↔ dataplane: static identity mapping

All P4RT port IDs are decimal strings. The mapping is the obvious one:
"N" ↔ N, pre-populated in the TypeTranslator at startup for all ports
up to 2^16. Never changes.

This is a simplifying assumption — real switches have platform-specific
mappings, but the identity mapping is sufficient for testing.

### gNMI name ↔ P4RT ID: dynamic via gNMI Set

FakeGnmiService updates its state path on Set. The mapping is
established at switch creation (from the `FakeInterface` list) and can be
changed via gNMI Set (e.g. by DVaaS mirroring SUT port config to the
control switch).

### No gNMI/P4RT coupling

The gNMI and P4Runtime control planes are deliberately decoupled:

- **gNMI Set succeeds regardless of installed entries.** DVaaS always
  clears entries before remapping ports, so stale entries are not a
  problem in practice. We do not enforce this ordering for simplicity.
- **P4Runtime Writes succeed regardless of gNMI state.** An entry
  referencing P4RT port "99" is accepted even if no gNMI interface has
  that ID.
- **Unmapped ports are dropped in the dataplane.** If a packet is
  forwarded to a P4RT port ID that has no corresponding gNMI interface,
  the packet is dropped and a warning is logged. This catches
  misconfigurations at the point they matter (packet forwarding) without
  complicating the control plane.

This is a good tradeoff for our use case: DVaaS sequences its operations
correctly, so enforcement would add complexity without catching real bugs.

## PacketBridge design

The bridge connects interfaces by gNMI name across the two switches.
On each packet forward, it:

1. Reads the source switch's gNMI to find the interface name for the
   packet's egress dataplane port.
2. Reads the target switch's gNMI to find the dataplane port for that
   interface name.
3. Injects the packet on the target switch's dataplane port via
   `InjectPacket` (unary).

Using unary `InjectPacket` (not streaming `InjectPackets`) ensures the
bridge doesn't hold the target switch's write lock across multiple
packets, allowing gNMI Set and P4Runtime Write to interleave.

The bridge reads gNMI per packet. This is simple and correct — no
caching, no staleness. Performance is not a concern (test vehicle).

We do not protect against races between gNMI Set and packet forwarding,
for simplicity. This should be fine because DVaaS does not update gNMI
concurrently with injecting packets. In contrast, 4ward already has
built-in protection against P4Runtime Write vs dataplane races (via its
read/write lock that serializes control plane writes with packet
processing).
