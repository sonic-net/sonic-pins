# FourwardPinsSwitch: Auxiliary Entry Design

**Status: proposal**

## Goal

`FourwardPinsSwitch` should behave like a real PINS switch. gNMI
configuration that affects P4 forwarding (VLAN membership, port state, etc.)
must be automatically reflected in the P4 tables — transparently, without
manual intervention from the user.

## Background

A real PINS switch has three layers:

1. **P4 data plane** — forwarding tables
2. **gNMI config** — port state, VLAN membership, etc.
3. **Control plane glue** — translates gNMI config into forwarding state
   (table entries, multicast groups, clone sessions, and other constructs
   that the P4 program assumes are configured). On a real PINS switch,
   this happens through SAI APIs and vendor SDKs — not P4Runtime. In our
   simulation, we use P4Runtime to install these entries on the 4ward
   server.

`FourwardPinsSwitch` currently has (1) and (2) but is missing (3). The
auxiliary P4 entries are derived by `sai::CreateV1ModelAuxiliaryEntities`,
which takes gNMI state + installed P4 entities and produces the auxiliary
entries.

## Naming

- `FourwardPinsSwitch` — simulated PINS switch (server + fake gNMI +
  control plane glue). Implements `thinkit::Switch`.
- `FourwardPinsMirrorTestbed` — two switches + packet bridge.
- `FourwardOracle` — bare prediction engine (no PINS behavior). Separate
  concern.

## P4Runtime roles

Auxiliary entries are installed under a dedicated P4Runtime role
(`"pins_auxiliary"`), separate from the user's controller role
(`"sdn_controller"`). This provides:

- **Independent arbitration.** The switch's internal session and the user's
  DVaaS session don't compete for primary.
- **Invisible to users.** Wildcard reads by a `sdn_controller` session
  don't return auxiliary entries — matching real switch behavior where
  gNMI-derived entries aren't exposed through P4Runtime.
- **Scoped access.** Each role can only touch its own tables.

## North star: race-free reactive reconciliation

### Two locks

- **4ward write lock** — protects P4 state. Already exists (ReadWriteMutex
  shared between P4RuntimeService and DataplaneService).
- **gNMI lock** — protects gNMI state. New, owned by `FakeGnmiService`.

### Pre-packet hook

4ward provides a generic gRPC hook on the Dataplane service: before
processing any packet (whether via `InjectPacket`, `InjectPackets`, or
`PacketOut`), the server fires a callback. The client (control plane
glue in `FourwardPinsSwitch`) uses it to reconcile auxiliary entries.

### Protocol

```
InjectPackets stream starts
  │
  ▼
Server acquires 4ward write lock
  │
  ▼
Server fires pre-packet hook ──────▶ Client callback runs
                                       │
                                       ▼
                                     Client acquires gNMI lock
                                       │
                                       ▼
                                     Client reads gNMI state + entities
                                       │
                                       ▼
                                     Client derives auxiliary entries
                                       │
                                       ▼
                                     Client responds with WriteRequest
                                       │
◄──────────────────────────────────────┘
  │
  ▼
Server applies WriteRequest updates
  │
  ▼
Server processes packet(s)
  │
  ▼
Client releases gNMI lock
  │
  ▼
Server releases 4ward write lock
```

### Race-freedom

Both locks are held from hook invocation through packet processing:

- **gNMI Set** blocks on the gNMI lock — can't change gNMI state while
  packets are being processed.
- **P4Runtime Write** blocks on the 4ward write lock — can't change entities
  while packets are being processed.
- **Concurrent packets** block on the 4ward write lock — serialized with
  the hook.

Lock ordering (4ward lock → gNMI lock) is consistent: gNMI Set only
takes the gNMI lock, P4Runtime Write only takes the 4ward lock. The hook
is the only place both are held, always in the same order. No deadlock.

### Hook RPC

```protobuf
service Dataplane {
  // Registers a pre-packet hook. The server calls back before processing
  // any dataplane RPC (InjectPacket, InjectPackets, PacketOut) while
  // holding the write lock. The client responds with P4Runtime updates
  // to apply atomically before packet processing.
  rpc RegisterPrePacketHook(stream PrePacketHookResponse)
      returns (stream PrePacketHookInvocation);
}

// Sent by the server before processing packets. The server holds the
// write lock and waits for the client's response before proceeding.
message PrePacketHookInvocation {}

// Sent by the client in response to a PrePacketHookInvocation. Contains
// P4Runtime updates to apply before packet processing. An empty
// updates list means no changes needed.
message PrePacketHookResponse {
  repeated p4.v1.Update updates = 1;
}
```

The response reuses the standard `p4.v1.Update` proto — no new entity
types. The server applies updates under the existing write lock.

### Performance

The hook fires before every dataplane RPC. The client always re-derives
auxiliary entries from the current state and diffs against what's
installed. The derivation + diff is in-process (fake gNMI, local state)
— microseconds.

For `InjectPackets` (streaming), the hook fires once at the start of
the stream, amortizing the cost across all packets in the stream. For
`InjectPacket` (unary), the hook fires per call. Users should prefer
streaming for performance.

When no hook is registered, the existing read lock optimization applies —
packets process concurrently with no overhead.

### Blocking gNMI Set during packet batches

The gNMI lock is held through the entire dataplane RPC, blocking gNMI
Set for the duration. This is acceptable for a simulator — tests don't
typically do concurrent gNMI Set + packet injection, and the
serialization is correct behavior (config changes don't take effect
mid-packet on real switches either).

## TODO: Clarify FourwardPinsSwitch contract

The class header and docs need to clearly communicate what
`FourwardPinsSwitch` is: **a simulated PINS switch**, not just a thin
wrapper around a 4ward server. It implements `thinkit::Switch` with the
same observable behavior as a real PINS switch — P4 data plane, gNMI
config, and the control plane glue that bridges them. Tests using a
`FourwardPinsSwitch` should not need to know it's simulated.

## Implementation plan

1. **Rename** `FourwardSwitch` → `FourwardPinsSwitch`,
   `FourwardMirrorTestbed` → `FourwardPinsMirrorTestbed`.
2. **Add `pins_auxiliary` role** to SAI P4 for auxiliary tables.
3. **4ward:** add pre-packet hook RPC to Dataplane service, add gNMI lock
   to FakeGnmiService.
4. **sonic-pins:** register hook in `FourwardPinsSwitch`, call
   `sai::CreateV1ModelAuxiliaryEntities` in the callback, respond with
   updates.
