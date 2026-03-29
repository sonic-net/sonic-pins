# Portable PINS Backend for DVaaS

An open-source `DataplaneValidationBackend` implementation for
[PINS](https://github.com/sonic-net/sonic-pins) switches running
[SAI P4](https://github.com/sonic-net/sonic-pins/tree/main/sai_p4).

## Motivation

DVaaS validates switch dataplane behavior by comparing a switch under test
against a reference P4 simulator. The `DataplaneValidationBackend` interface
abstracts the simulator and supporting infrastructure. Until now, no
open-source implementation existed — users had to bring their own.

This backend provides a fully portable implementation:

- **Output prediction:** [4ward](https://github.com/smolkaj/4ward) via
  `FourwardOracle` (when `fourward_config` is set in `P4Specification`).
- **Packet traces:** Produced by 4ward alongside output prediction — no
  separate trace collection step.
- **Punt-all entries:** SAI P4 ACL entries that cause all packets to be
  punted to the CPU (needed by DVaaS for the control switch).
- **Auxiliary entries:** SAI P4 table entries that mirror gNMI configuration
  knobs affecting P4 forwarding (VLAN membership, port admin state, etc.).
  On a real switch, gNMI Set populates these tables; in testing, the backend
  synthesizes equivalent entries from the gNMI config.
- **P4 specification inference:** Reads P4Info from the switch and bundles
  it with the 4ward pipeline config.
- **Packet synthesis:** Not yet implemented. Use
  `DataplaneValidationParams::packet_test_vector_override` to provide test
  vectors manually, or wait for
  [p4-symbolic](https://github.com/sonic-net/sonic-pins/tree/main/p4_symbolic)
  integration.

## Architecture

```
  DataplaneValidator
      │
      ├─ SynthesizePackets ──────▶ (TODO: p4-symbolic)
      │
      ├─ GeneratePacketTestVectors
      │   └─ bypassed by frontend ──▶ FourwardOracle.PredictAll
      │
      ├─ GetEntitiesToPuntAllPackets
      │   └─ SAI P4 ACL punt entries (sai::EntryBuilder)
      │
      ├─ InferP4Specification
      │   └─ P4Info from switch + fourward_config
      │
      ├─ AugmentPacketTestVectorsWithPacketTraces
      │   └─ no-op (traces attached during prediction)
      │
      └─ CreateV1ModelAuxiliaryEntities
          └─ sai::CreateV1ModelAuxiliaryEntities (shared, see below)
```

## Auxiliary entries and the FourwardMirrorTestbed

SAI P4 has tables that model gNMI configuration knobs affecting forwarding:
VLAN membership, port admin state, loopback mode, etc. On a real switch,
gNMI Set populates these tables. On a simulated switch (4ward), the same
entries must be installed explicitly — otherwise packets get dropped by
checks the P4 program performs (e.g. ingress VLAN membership).

The core logic lives in
[`sai_p4/tools/auxiliary_entries_for_v1model_targets.h`](../../sai_p4/tools/auxiliary_entries_for_v1model_targets.h):

```cpp
// Takes IR entities + gNMI stub, returns auxiliary P4 entries.
absl::StatusOr<pdpi::IrEntities> sai::CreateV1ModelAuxiliaryEntities(
    pdpi::IrEntities ir_entities, gnmi::gNMI::StubInterface& gnmi_stub);
```

This function is shared by two consumers:

1. **This backend** (`CreateV1ModelAuxiliaryEntities` method) — called by
   DVaaS during validation to augment the SUT's entities with auxiliary
   entries for the reference simulator.

2. **`FourwardMirrorTestbed`** (`fourward/fourward_mirror_testbed.h`) —
   calls it during `Create()` to install auxiliary entries on both 4ward
   servers transparently. DVaaS doesn't know it's running on simulated
   switches — it just sees a `thinkit::MirrorTestbed`. The testbed's
   `FakeGnmiService` provides the gNMI stub that
   `CreateV1ModelAuxiliaryEntities` reads from.

```
  FourwardMirrorTestbed::Create()
      │
      ├─ Start 2 FourwardServers
      ├─ Start 2 FakeGnmiServers
      ├─ Load pipeline on both servers
      ├─ sai::CreateV1ModelAuxiliaryEntities(entities, fake_gnmi)
      │   └─ reads fake gNMI → produces VLAN/port entries
      ├─ Install auxiliary entries on both servers
      └─ Start PacketBridge
```

## Usage

```cpp
#include "dvaas/portable_pins_backend/portable_pins_backend.h"

// Load the 4ward-compiled pipeline config.
p4::v1::ForwardingPipelineConfig fourward_config = ...;

// Create the backend and validator.
std::unique_ptr<DataplaneValidationBackend> backend =
    CreatePortablePinsBackend(fourward_config);
DataplaneValidator validator(std::move(backend));

// Run validation with user-provided test vectors.
DataplaneValidationParams params;
params.specification_override = ...;
params.packet_test_vector_override = ...;
ASSIGN_OR_RETURN(ValidationResult result,
                 validator.ValidateDataplane(testbed, params));
```

## Known limitations

- **Auxiliary entries are computed once.** Both the backend and
  `FourwardMirrorTestbed` currently compute auxiliary entries at
  creation/validation time. If entities are installed or gNMI config changes
  later (e.g. during failure post-processing or multi-round validation), the
  auxiliary entries may become stale. A reactive approach — updating auxiliary
  entries in response to P4Runtime Write or gNMI Set — would be more correct
  but is not yet implemented.

## Roadmap

1. **Packet synthesis via p4-symbolic.** Replace hardcoded test vectors with
   automatically synthesized packets that cover all table entries.
2. **Full auxiliary entry coverage.** Ensure all gNMI-derived tables in SAI P4
   are covered by `CreateV1ModelAuxiliaryEntities`.
3. **Reactive auxiliary entries.** Update auxiliary entries when entities or
   gNMI config change, rather than computing them once up front.
4. **Non-SAI P4 support.** Generalize punt-all and auxiliary entries for other
   P4 programs (requires parameterizing by P4 program).
