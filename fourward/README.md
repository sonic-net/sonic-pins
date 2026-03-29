# 4ward Integration for DVaaS

This directory integrates [4ward](https://github.com/smolkaj/4ward) — a P4
behavioral simulator — into sonic-pins as a replacement for BMv2 in DVaaS.

## Architecture

```
  DVaaS frontend (dataplane_validation.cc)
      │
      ├─ output prediction ──▶ FourwardOracle
      │                            │
      │                            ├─ P4Runtime gRPC (pipeline, entries)
      │                            └─ Dataplane gRPC (InjectPackets → outputs + TraceTree)
      │
      └─ trace prediction ───▶ FourwardTraceTreeToDvaasPacketTrace
```

4ward runs as a **subprocess** managed by `FourwardServer`. DVaaS talks to it
over gRPC — standard P4Runtime for pipeline config and table entries, plus
4ward's Dataplane service for packet injection and trace collection.

## Components

### FourwardServer (`fourward_server.h`)

RAII wrapper for a 4ward P4Runtime server subprocess. Handles the full
lifecycle: resolve the binary from Bazel runfiles, fork/exec with `--port=0`,
parse the port from the startup banner, and kill the process on destruction
(SIGTERM → SIGKILL after 5s).

### FourwardSwitch (`fourward_switch.h`)

`thinkit::Switch` backed by a `FourwardServer`. Starts its own server
subprocess via `FourwardSwitch::Create()`.

### FourwardOracle (`fourward_oracle.h`)

Manages a 4ward server and provides packet output prediction with traces.
Handles the full setup: start server, establish P4Runtime session, load
pipeline, install entries. Prediction uses the streaming `InjectPackets` +
`SubscribeResults` RPCs for high throughput.

### FakeGnmiService (`fake_gnmi_service.h`)

Minimal in-process gNMI server modeling configurable Ethernet interfaces with
P4RT port IDs. DVaaS uses gNMI to discover switch ports and check that they
are up. This fake serves just enough to satisfy those queries.

### PacketBridge (`packet_bridge.h`)

Emulates back-to-back physical links between two 4ward instances. When the SUT
outputs a packet on port X, the bridge injects it into the control switch on
port X (and vice versa). Two threads, one per direction, subscribe to
`SubscribeResults` and forward via `InjectPacket`.

### FourwardMirrorTestbed (`fourward_mirror_testbed.h`)

`thinkit::MirrorTestbed` backed by two 4ward instances with fake gNMI and a
packet bridge. The development vehicle — exercises all integration code without
a real switch.

`Create()` handles the full setup transparently: starts servers, loads
pipelines, installs SAI P4 auxiliary entries (mirroring the fake gNMI config
via `sai::CreateV1ModelAuxiliaryEntities`), and starts the packet bridge.
DVaaS sees a standard `thinkit::MirrorTestbed` — it doesn't know it's
running on simulated switches.

### Trace Conversion (`trace_conversion.h`)

Flattens 4ward's recursive `TraceTree` into DVaaS's flat `PacketTrace`.
Parallel forks (clone, multicast) follow all branches; alternative forks
(action selectors) follow the first branch.

### fourward_pipeline (Bazel rule)

```starlark
load("@fourward//bazel:fourward_pipeline.bzl", "fourward_pipeline")

fourward_pipeline(
    name = "sai_middleblock_fourward",
    src = "//sai_p4/instantiations/google:middleblock.p4",
    out = "sai_middleblock_fourward.binpb",
    out_format = "p4runtime",
)
```

Compiles a P4 program at build time. `out_format` selects the proto type:
`"native"` for `fourward.ir.PipelineConfig`, `"p4runtime"` for
`p4.v1.ForwardingPipelineConfig`.

## How It Fits Into DVaaS

DVaaS validates switch behavior by comparing a switch under test (SUT) against
a reference P4 simulator. Today that reference is BMv2. 4ward replaces it with:

1. **Spec compliance.** Full `@p4runtime_translation` support (including string
   ports), `@entry_restriction` / `@action_restriction` validation, all
   v1model features SAI P4 uses.

2. **Trace trees.** 4ward produces structured trace trees natively — all
   possible outputs at non-deterministic choice points in a single pass.

3. **Hermetic build.** `bazel_dep` that just works — no Docker, no system
   packages, no BMv2 build headaches.

The integration is **opt-in and backward compatible**: when `fourward_config`
is present in `P4Specification`, DVaaS uses 4ward; otherwise, the existing
BMv2 backend path works unchanged.

See [designs/migration_plan.md](designs/migration_plan.md) for the
BMv2 → 4ward migration plan.
