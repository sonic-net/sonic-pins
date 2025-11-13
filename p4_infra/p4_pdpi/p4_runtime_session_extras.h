// Copyright 2025 Google LLC
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
// =============================================================================
// Convenience functions to simplify working with `P4RuntimeSession`.
//
// These functions are in a separate file since they pull in additional
// dependencies that some users may wish to avoid.
//
// NOTE: Like `P4RuntimeSession` itself, these function are optimized for
// convenience, not for performance. They are intended for use in testing &
// experimentation, not for use in production.

#ifndef PINS_P4_INFRA_P4_PDPI_P4_RUNTIME_SESSION_EXTRAS_H_
#define PINS_P4_INFRA_P4_PDPI_P4_RUNTIME_SESSION_EXTRAS_H_

#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/types/span.h"
#include "google/protobuf/message.h"
#include "google/protobuf/repeated_field.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/p4_pdpi/p4_runtime_session_extras.pb.h"

namespace pdpi {

// -- Installing table entries in PD format ------------------------------------

// Installs the given `pd_table_entries` via the given `P4RuntimeSession`.
//
// Assumes `pd_table_entries` is a `TableEntries` message whose schema is
// defined in a .proto file produced by PD generator. Assumes that the switch is
// pre-configured with a `P4Info` that supports the given entries. The `P4Info`
// is read from the switch.
absl::Status InstallPdTableEntries(
    P4RuntimeSession& p4rt, const google::protobuf::Message& pd_table_entries);

// Like the `InstallPdTableEntries` overload above, but takes in the
// `TableEntries` message of type `T` in proto text format.
// This function is generic over `T` since its concrete type is
// P4 program-dependent.
template <typename T>
absl::Status InstallPdTableEntries(P4RuntimeSession& p4rt,
                                   absl::string_view pd_table_entries);

// Like `InstallPdTableEntries`, but for a single entry, which must
// be a `TableEntry` message with a PD generator-produced .proto definition.
absl::Status InstallPdTableEntry(
    P4RuntimeSession& p4rt, const google::protobuf::Message& pd_table_entry);

// Like `InstallPdTableEntries` but for a single `TableEntry` message of type
// `T` given in proto text format.
// This function is generic over `T` since its concrete type is
// P4 program-dependent.
template <typename T>
absl::Status InstallPdTableEntry(P4RuntimeSession& p4rt,
                                 absl::string_view pd_table_entry);

// Like `InstallPdTableEntries`, but for IR table entries. Reads the P4Info used
// in translation from the switch.
absl::Status InstallIrTableEntries(P4RuntimeSession& p4rt,
                                   const IrTableEntries& ir_table_entries);
absl::Status InstallIrEntities(P4RuntimeSession& p4rt,
                               const IrEntities& ir_entities);

// Like `InstallIrEntities`, but for a single entity.
absl::Status InstallIrEntity(P4RuntimeSession& p4rt, const IrEntity& ir_entity);

// Like `InstallIrTableEntries`, but for a single entry.
absl::Status InstallIrTableEntry(P4RuntimeSession& p4rt,
                                 const IrTableEntry& ir_table_entry);

// Installs the given `entities` via the given `P4RuntimeSession`.
absl::Status InstallPiEntities(P4RuntimeSession& p4rt,
                               const PiEntities& entities);
absl::Status InstallPiEntities(P4RuntimeSession& p4rt,
                               absl::Span<const p4::v1::Entity> entities);

// Like the `InstallPiEntities` above, but takes in the `PiEntities` message in
// text format.
absl::Status InstallPiEntities(P4RuntimeSession& p4rt,
                               absl::string_view entities);

// Reads control plane entities from the switch using `p4rt` and returns them in
// PI representation in an order determined by `pdpi::EntityKey`.
absl::StatusOr<std::vector<p4::v1::Entity>> ReadPiEntitiesSorted(
    P4RuntimeSession& p4rt);

// Reads table entries from the switch using `p4rt` and returns them in PI
// representation in an order determined by `pdpi::TableEntryKey`.
ABSL_DEPRECATED("Prefer ReadPiEntitiesSorted instead.")
absl::StatusOr<std::vector<p4::v1::TableEntry>> ReadPiTableEntriesSorted(
    P4RuntimeSession& p4rt);

// Reads control plane entities from the switch using `p4rt` and returns them in
// IR representation. Reads the P4Info used in translation from the switch.
absl::StatusOr<IrEntities> ReadIrEntities(P4RuntimeSession& p4rt);

// Reads table entries from the switch using `p4rt` and returns them in IR
// representation. Reads the P4Info used in translation from the switch.
ABSL_DEPRECATED("Prefer ReadIrEntities instead.")
absl::StatusOr<IrTableEntries> ReadIrTableEntries(P4RuntimeSession& p4rt);

// Reads control plane entities from the switch using `p4rt` and returns them in
// IR representation in an order determined `by pdpi::EntityKey` on the
// corresponding PI representation. Reads the P4Info used in translation from
// the switch.
absl::StatusOr<IrEntities> ReadIrEntitiesSorted(P4RuntimeSession& p4rt);

// Reads table entries from the switch using `p4rt` and returns them in IR
// representation in an order determined by `pdpi::TableEntryKey` on the
// corresponding PI representation. Reads the P4Info used in translation from
// the switch.
ABSL_DEPRECATED("Prefer ReadIrEntitiesSorted instead.")
absl::StatusOr<IrTableEntries> ReadIrTableEntriesSorted(P4RuntimeSession& p4rt);

// Constructs a write request with metadata from `p4rt` and sends it to the
// switch, returning a response containing the per-update status (in the same
// order as the input `updates`).
absl::StatusOr<IrWriteRpcStatus> SendPiUpdatesAndReturnPerUpdateStatus(
    P4RuntimeSession& p4rt, absl::Span<const p4::v1::Update> updates);
absl::StatusOr<IrWriteRpcStatus> SendPiUpdatesAndReturnPerUpdateStatus(
    P4RuntimeSession& p4rt,
    const google::protobuf::RepeatedPtrField<p4::v1::Update>& updates);

// Reads the P4Info currently configured on the switch and returns it, or
// returns an error if no P4Info is configured.
absl::StatusOr<p4::config::v1::P4Info> GetP4Info(P4RuntimeSession& p4rt);

// Reads the P4Info currently configured on the switch, converts it to IR
// format, and returns it, or returns an error if no P4Info is configured or the
// conversion fails.
absl::StatusOr<IrP4Info> GetIrP4Info(P4RuntimeSession& p4rt);

// Returns the P4Info on the switch. If the switch does not have a P4Info,
// pushes the supplied P4Info to the switch and returns the supplied P4Info.
absl::StatusOr<p4::config::v1::P4Info> GetOrSetP4Info(
    pdpi::P4RuntimeSession& p4rt_session,
    const p4::config::v1::P4Info& default_p4info);

// Deletes the given `ir_entity` from the switch.
absl::Status DeleteIrEntity(P4RuntimeSession& p4rt, const IrEntity& ir_entity);

// Deletes the given `pi_entity` from the switch.
absl::Status DeletePiEntity(P4RuntimeSession& p4rt,
                            const p4::v1::Entity& pi_entity);

// == END OF PUBLIC INTERFACE ==================================================

// -- Internal implementation details follow -----------------------------------

template <typename T>
absl::Status InstallPdTableEntries(P4RuntimeSession& p4rt,
                                   absl::string_view pd_table_entries) {
  ASSIGN_OR_RETURN(T parsed_pd_table_entries,
                   gutil::ParseTextProto<T>(pd_table_entries));
  return InstallPdTableEntries(p4rt, parsed_pd_table_entries);
}

template <typename T>
absl::Status InstallPdTableEntry(P4RuntimeSession& p4rt,
                                 absl::string_view pd_table_entry) {
  ASSIGN_OR_RETURN(T parsed_pd_table_entry,
                   gutil::ParseTextProto<T>(pd_table_entry));
  return InstallPdTableEntry(p4rt, parsed_pd_table_entry);
}

}  // namespace pdpi

#endif  // PINS_P4_INFRA_P4_PDPI_P4_RUNTIME_SESSION_EXTRAS_H_
