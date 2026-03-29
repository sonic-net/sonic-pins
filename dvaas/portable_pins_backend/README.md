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
- **Auxiliary entries:** VLAN check disable entries and other SAI P4-specific
  table entries that model switch behavior not captured by the P4 program
  alone.
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
          └─ VLAN disable entries (sai::EntryBuilder)
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

## Roadmap

1. **Packet synthesis via p4-symbolic.** Replace hardcoded test vectors with
   automatically synthesized packets that cover all table entries.
2. **Full gNMI integration.** Model port loopback mode and other gNMI-derived
   state in auxiliary entries.
3. **Non-SAI P4 support.** Generalize punt-all and auxiliary entries for other
   P4 programs (requires parameterizing by P4 program).
