# 4ward Integration for DVaaS

This directory integrates [4ward](https://github.com/smolkaj/4ward) — a P4
behavioral simulator — into sonic-pins as a replacement for BMv2 in DVaaS.

## Architecture

```
  DVaaS frontend (dataplane_validation.cc)
      │
      ├─ output prediction ──▶ FourwardServer (subprocess)
      │                            │
      │                            ├─ P4Runtime gRPC (pipeline, entries)
      │                            └─ Dataplane gRPC (InjectPacket → outputs + TraceTree)
      │
      └─ trace prediction ───▶ TraceTree → PacketTrace conversion
```

4ward runs as a **subprocess** managed by `FourwardServer`. DVaaS talks to it
over gRPC — standard P4Runtime for pipeline config and table entries, plus
4ward's Dataplane service for packet injection and trace collection.

## Key Components

### FourwardServer (`fourward_server.h`)

RAII wrapper for a 4ward P4Runtime server subprocess. Handles the full
lifecycle: fork/exec the server binary with `--port=0`, parse the actual port
from the server's startup banner, and kill the process on destruction (SIGTERM
→ SIGKILL after 5s).

Used by both the `FourwardMirrorTestbed` (development vehicle) and the DVaaS
frontend (production path).

### FourwardSwitch (`fourward_switch.h`)

Adapts a running 4ward server to the `thinkit::Switch` interface. P4Runtime is
served by 4ward; gNMI is served by a separate stub (typically
`FakeGnmiService`) since 4ward doesn't implement gNMI. This split mirrors
the real-world architecture where P4Runtime and gNMI are independent services.

### fourward_pipeline (Bazel rule)

```starlark
load("@fourward//bazel:fourward_pipeline.bzl", "fourward_pipeline")

fourward_pipeline(
    name = "sai_middleblock_fourward",
    src = "//sai_p4/instantiations/google:middleblock.p4",
    includes = ["//sai_p4/fixed:v1model_sai.p4"],
    extra_srcs = ["//sai_p4:sai_p4_srcs"],
)
```

Compiles a P4 program at build time using `p4c-4ward`. Produces two outputs:
- `name.pipeline.txtpb` — 4ward-native PipelineConfig (text proto)
- `name.p4rt.binpb` — P4Runtime ForwardingPipelineConfig (binary proto)

The SAI P4 middleblock compilation uses `v1model_sai.p4` — a minimal fork of
stock v1model that defines typed `port_id_t` with `@p4runtime_translation`,
eliminating the port encoding hacks BMv2 requires.

## How It Fits Into DVaaS

DVaaS validates switch behavior by comparing a switch under test (SUT) against
a reference P4 simulator. Today that reference is BMv2. 4ward replaces it with
three improvements:

1. **Spec compliance.** Full `@p4runtime_translation` support (including string
   ports), `@entry_restriction` / `@action_restriction` validation, all
   v1model features SAI P4 uses.

2. **Trace trees.** 4ward produces structured trace trees natively — all
   possible outputs at non-deterministic choice points in a single pass. DVaaS
   currently uses brittle hacks to extract traces from BMv2.

3. **Hermetic build.** `bazel_dep` that just works — no Docker, no system
   packages, no BMv2 build headaches.

The integration is **opt-in and backward compatible**: when a 4ward pipeline
config is present in `P4Specification`, DVaaS uses 4ward; otherwise, the
existing BMv2 backend path works unchanged.
