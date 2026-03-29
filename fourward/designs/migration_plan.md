# BMv2 → 4ward Migration Plan

**Status: proposal**

## Overview

Replace BMv2 with 4ward as the reference simulator in DVaaS. The migration
has three workstreams that can proceed in parallel:

1. **Import 4ward into google3** via copybara
2. **Submit integration code** to google3 (staged on GitHub fork)
3. **Phase the BMv2 → 4ward cutover** in production

## Workstream 1: Import 4ward into google3

### What to import

4ward is a self-contained Bazel project. The google3 import needs:

| 4ward path | Purpose | Notes |
|---|---|---|
| `simulator/ir.proto` | Behavioral IR | The core contract |
| `simulator/simulator.proto` | Shared types (TraceTree, OutputPacket) | Used by sonic-pins C++ |
| `p4runtime/dataplane.proto` | Dataplane gRPC service | InjectPackets, SubscribeResults |
| `simulator/*.kt` | Kotlin simulator | Heart of 4ward |
| `p4runtime/*.kt` | P4Runtime + Dataplane gRPC server | The subprocess sonic-pins talks to |
| `p4c_backend/*.{h,cpp}` | p4c backend plugin | Compiles P4 → IR |
| `bazel/fourward_pipeline.bzl` | Build rule for P4 compilation | Needs Blaze adaptation |

### What to exclude

Dev tools, CI, docs, examples, e2e tests, web playground — these stay
external. The google3 import is the minimal runtime needed by sonic-pins.

### Copybara config sketch

```python
core.workflow(
    name = "import_fourward",
    origin = git.origin(
        url = "https://github.com/smolkaj/4ward.git",
        ref = "main",
    ),
    destination = # google3 destination
    origin_files = glob(
        include = [
            "simulator/**",
            "p4runtime/**",
            "p4c_backend/**",
            "bazel/fourward_pipeline.bzl",
            "MODULE.bazel",
            "BUILD.bazel",
        ],
        exclude = [
            "**/*Test.kt",
            "**/*Benchmark.kt",
            "**/test/**",
            "web/**",
            "cli/**",
            "e2e_tests/**",
            "examples/**",
            "docs/**",
            "tools/**",
        ],
    ),
    authoring = # ...
)
```

### google3 BUILD adaptation

google3 doesn't use `MODULE.bazel` or Bzlmod. The copybara transform needs
to generate google3-compatible BUILD files (no `.bazel` extension). Key
differences:

- No `bazel_dep` — deps are direct paths in the monorepo
- `kt_jvm_library` / `kt_jvm_binary` — same rule names, different load paths
- Proto rules — google3 has its own proto build rules
- The `fourward_pipeline` rule needs a Blaze-native equivalent

### google3 dependencies

| Dependency | In google3? | Notes |
|---|---|---|
| protobuf | Yes | Standard |
| grpc-java | Yes | |
| grpc_kotlin | Needs checking | Kotlin gRPC runtime for the P4Runtime server |
| p4runtime | Yes, outdated | Proto definitions for P4Runtime API |
| p4c | Yes, outdated | 4ward's backend links against p4c frontend/midend |
| p4_constraints | Yes, outdated | `@entry_restriction` / `@action_restriction` validation via JNI |
| Kotlin toolchain | Yes | Verify version compatibility |

### Open questions

- **google3 path**: `third_party/fourward/`
- **Kotlin version**: Is google3's Kotlin version compatible with 4ward's
  code (coroutines, sealed classes, proto-kotlin extensions)?
- **Proto version skew**: google3's protobuf vs 4ward's 33.5 — the
  `optional bool` fields (PR #455) require proto3 optional support.
- **p4c version**: 4ward's backend uses p4c APIs that may have changed
  between the google3 version and the version 4ward builds against.
- **p4_constraints**: 4ward calls p4-constraints via a C++ subprocess.
  The p4-constraints library needs to be available in google3.

## Workstream 2: Submit integration code to google3

The integration code lives in sonic-pins (`fourward/` and
`dvaas/portable_pins_backend/`). It needs to be submitted to google3 so
copybara can export it to `sonic-net/sonic-pins`.

### Submission order

Each step is a separate CL:

1. **`fourward/fourward_server.{h,cc}`** — subprocess manager. Pure C++,
   no 4ward-specific deps beyond the server binary path. Includes test.

2. **`fourward/fourward_switch.{h,cc}`** — `thinkit::Switch` adapter.
   Depends on `fourward_server`. Includes test.

3. **`fourward/fourward_oracle.{h,cc}`** — prediction via gRPC. Depends
   on `fourward_server` + proto stubs. Includes test.

4. **`fourward/trace_conversion.{h,cc}`** + `trace_summary.{h,cc}` —
   proto-to-proto conversion + debugging helper. Includes tests + golden.

5. **`fourward/fake_gnmi_service.h`** + `packet_bridge.{h,cc}` +
   `fourward_mirror_testbed.{h,cc}` — testbed infrastructure. Includes
   tests.

6. **`fourward/test_vector_generation.{h,cc}`** — test vector generation
   using oracle. Depends on oracle + packetlib.

7. **`dvaas/dataplane_validation.{h,cc}`** changes — add `fourward_config`
   to `P4Specification`, add frontend code path. This is the critical CL
   that touches DVaaS core.

8. **`dvaas/portable_pins_backend/`** — the open-source backend.

9. **`fourward_pipeline` build rule** — compile SAI P4 for 4ward at build
   time.

### Why this order

- Steps 1-5 are additive — they add new code without touching existing code.
  Easy to review, easy to roll back.
- Step 6 depends on the oracle and packetlib.
- Step 7 is the only change to existing code. It's gated by `fourward_config`
  being present, so it's zero-risk to existing users.
- Step 8 is the first thing that actually *uses* 4ward for DVaaS.
- Step 9 enables building the 4ward pipeline config from SAI P4 source.

## Workstream 3: BMv2 → 4ward cutover

### Phase 1: Side-by-side validation

**Goal:** Prove 4ward matches BMv2 on real traffic.

- Run DVaaS with both BMv2 and 4ward simultaneously.
- For each test packet, compare BMv2's prediction against 4ward's.
- Log mismatches but don't fail tests.
- Measure: mismatch rate, latency comparison, trace quality comparison.

**Implementation:** Add a `DataplaneValidationParams::also_validate_with_fourward`
flag. When set, `GenerateTestVectors` runs both BMv2 and 4ward, compares
their predictions, and writes the results as test artifacts:

- `fourward_comparison_summary.txt` — match rate, mismatch categories
  (extra output, missing output, wrong port, trace-only diff).
- `fourward_mismatches.txt` — full BMv2 vs 4ward predictions for each
  disagreement (packets, ports, traces).

The test outcome is still determined by BMv2 (the current source of truth).
The 4ward comparison is informational — mismatches are logged but don't
cause test failures.

**Exit criteria:** Zero mismatches on the full DVaaS test suite for SAI P4
middleblock, and no significant performance regression (4ward validation
time within 2x of BMv2).

### Phase 2: 4ward as primary

**Goal:** 4ward is the default reference simulator.

- Flip the default: `fourward_config` is populated by default when a 4ward
  pipeline config is available.
- BMv2 path remains as a fallback (users can unset `fourward_config`).
- Monitor for regressions.

**Exit criteria:** No correctness or performance regressions after 2 weeks
of 4ward as primary.

### Phase 3: Remove BMv2

**Goal:** Simplify the codebase.

- `P4Specification` changes: `fourward_config` becomes non-optional (the
  required config), `bmv2_config` is removed.
- Remove the BMv2 code path from `dataplane_validation.cc`.
- Simplify the `DataplaneValidationBackend` interface: remove
  `GeneratePacketTestVectors` and `AugmentPacketTestVectorsWithPacketTraces`
  (prediction and traces are now frontend concerns). The backend reduces to
  SAI P4-specific helpers: `GetEntitiesToPuntAllPackets`,
  `CreateV1ModelAuxiliaryEntities`, `InferP4Specification`, and
  `SynthesizePackets`.
- Remove BMv2-related code and configuration from sonic-pins and DVaaS
  backends.

**Exit criteria:** All tests pass without BMv2.

### Migration timeline

```
  Phase 1          Phase 2          Phase 3
  side-by-side     4ward primary    remove BMv2
  ┌──────────┐     ┌──────────┐    ┌──────────┐
  │ compare  │     │ flip     │    │ delete   │
  │ both     │────▶│ default  │───▶│ BMv2     │
  │ outputs  │     │ monitor  │    │ code     │
  └──────────┘     └──────────┘    └──────────┘
       ▲
       │
  Workstreams 1+2 complete
```

Phase 1 can start as soon as workstreams 1 and 2 are complete. Phases 2
and 3 are gated by Phase 1's exit criteria.

## Performance

4ward adds ~1-2s of JVM startup per oracle. The `DataplaneValidator` must
own the `FourwardOracle` and reuse it across the validation run —
including failure post-processing, which re-runs individual failing
packets. Without reuse, N failures would mean N × 2s of JVM startup
overhead (a regression vs BMv2, where the backend owns the process).
Phase 1 (side-by-side) will measure both BMv2 and 4ward latencies as
test artifacts for comparison.

**Follow-up:** The failure post-processing code in `dataplane_validation.cc`
currently creates a fresh backend invocation per failure. With the validator
owning the oracle, this is a natural opportunity to simplify the
post-processing flow — reusing the oracle and its installed entities
rather than reconstructing state from scratch each time.

## Risks

1. **4ward correctness.** If 4ward produces different outputs than BMv2 for
   valid programs, Phase 1 will surface this. 4ward already passes all 186
   v1model corpus tests + BMv2 differential testing, so large gaps are
   unlikely.

2. **Performance.** 4ward meets the 1k pps target, but it's a JVM subprocess
   with startup cost (~1s). Mitigation: validator owns the oracle (see
   Performance section above).

3. **google3 compatibility.** Kotlin in google3, proto version skew, Blaze
   BUILD rules. These are solvable but may require iteration.

4. **Copybara complexity.** The BUILD file transformation from Bazel to Blaze
   is the hardest part of the import. May need manual BUILD files in google3.
