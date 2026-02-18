// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Native v1model targets (like BMv2 or p4-symbolic) require some auxiliary
// table entries -- e.g. for configuring v1model's Packet Replication Engine to
// enable punting packets to the controller -- that are not required by
// PINS targets, as PINS has such config built-in.
//
// This library provides such table entries.

#ifndef PINS_SAI_P4_TOOLS_AUXILIARY_ENTRIES_FOR_V1MODEL_TARGETS_H_
#define PINS_SAI_P4_TOOLS_AUXILIARY_ENTRIES_FOR_V1MODEL_TARGETS_H_

#include "absl/status/statusor.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "proto/gnmi/gnmi.grpc.pb.h"

namespace sai {

// Returns a Packet Replication Engine entry (see the P4Runtime standard)
// that is required by the SAI P4 copy/trap actions to clone a copy of the input
// packet to the CPU port.
//
// Required by native v1model targets (e.g. BMv2, p4-symbolic).
// Not required by PINS targets, since PINS has this config built-in.
p4::v1::Entity MakeV1modelPacketReplicationEngineEntryRequiredForPunts();

// Creates entities for v1Model auxiliary tables that model the effects of the
// given entities (e.g. VLAN membership) and gNMI configuration (e.g. port
// loopback mode).
absl::StatusOr<pdpi::IrEntities> CreateV1ModelAuxiliaryEntities(
    pdpi::IrEntities ir_entities, gnmi::gNMI::StubInterface& gnmi_stub);

}  // namespace sai

#endif  // PINS_SAI_P4_TOOLS_AUXILIARY_ENTRIES_FOR_V1MODEL_TARGETS_H_
