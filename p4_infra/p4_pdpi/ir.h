// Copyright 2020 Google LLC
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

#ifndef PINS_P4_PDPI_IR_H_
#define PINS_P4_PDPI_IR_H_
// P4 intermediate representation definitions for use in conversion to and from
// Program-Independent to either Program-Dependent or App-DB formats

#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/types/span.h"
#include "grpcpp/support/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/translation_options.h"

namespace pdpi {

// -- IrP4Info utilities -------------------------------------------------------

// Removes all `@unsupported` tables/match fields/actions from the given
// `p4_info`.
void RemoveUnsupportedEntities(IrP4Info &p4_info);

// -- Conversions from PI to IR ------------------------------------------------

// Creates IrP4Info for a PI P4Info and validates that the p4_info has no
// errors.
absl::StatusOr<IrP4Info> CreateIrP4Info(const p4::config::v1::P4Info &p4_info);

absl::StatusOr<IrEntity> PiEntityToIr(
    const IrP4Info &info, const p4::v1::Entity &pi,
    const TranslationOptions &options PDPI_TRANSLATION_OPTIONS_DEFAULT);
absl::StatusOr<IrEntities> PiEntitiesToIr(
    const IrP4Info &info, absl::Span<const p4::v1::Entity> pi,
    const TranslationOptions &options PDPI_TRANSLATION_OPTIONS_DEFAULT);

absl::StatusOr<IrTableEntry> PiTableEntryToIr(
    const IrP4Info &info, const p4::v1::TableEntry &pi,
    const TranslationOptions &options PDPI_TRANSLATION_OPTIONS_DEFAULT);
absl::StatusOr<IrTableEntries> PiTableEntriesToIr(
    const IrP4Info &info, absl::Span<const p4::v1::TableEntry> pi,
    const TranslationOptions &options PDPI_TRANSLATION_OPTIONS_DEFAULT);

absl::StatusOr<IrPacketReplicationEngineEntry>
PiPacketReplicationEngineEntryToIr(
    const IrP4Info &info, const p4::v1::PacketReplicationEngineEntry &pi,
    const TranslationOptions &options PDPI_TRANSLATION_OPTIONS_DEFAULT);

absl::StatusOr<IrMulticastGroupEntry> PiMulticastGroupEntryToIr(
    const IrP4Info &info, const p4::v1::MulticastGroupEntry &pi,
    const TranslationOptions &options PDPI_TRANSLATION_OPTIONS_DEFAULT);

absl::StatusOr<IrPacketIn> PiPacketInToIr(
    const IrP4Info &info, const p4::v1::PacketIn &packet,
    const TranslationOptions &options PDPI_TRANSLATION_OPTIONS_DEFAULT);

absl::StatusOr<IrPacketOut> PiPacketOutToIr(
    const IrP4Info &info, const p4::v1::PacketOut &packet,
    const TranslationOptions &options PDPI_TRANSLATION_OPTIONS_DEFAULT);

absl::StatusOr<IrReadRequest> PiReadRequestToIr(
    const IrP4Info &info, const p4::v1::ReadRequest &read_request,
    const TranslationOptions &options PDPI_TRANSLATION_OPTIONS_DEFAULT);

absl::StatusOr<IrReadResponse> PiReadResponseToIr(
    const IrP4Info &info, const p4::v1::ReadResponse &read_response,
    const TranslationOptions &options PDPI_TRANSLATION_OPTIONS_DEFAULT);

absl::StatusOr<IrUpdate> PiUpdateToIr(
    const IrP4Info &info, const p4::v1::Update &update,
    const TranslationOptions &options PDPI_TRANSLATION_OPTIONS_DEFAULT);

absl::StatusOr<IrWriteRequest> PiWriteRequestToIr(
    const IrP4Info &info, const p4::v1::WriteRequest &write_request,
    const TranslationOptions &options PDPI_TRANSLATION_OPTIONS_DEFAULT);

absl::StatusOr<IrStreamMessageRequest> PiStreamMessageRequestToIr(
    const IrP4Info &info,
    const p4::v1::StreamMessageRequest &stream_message_request,
    const TranslationOptions &options PDPI_TRANSLATION_OPTIONS_DEFAULT);

absl::StatusOr<IrStreamMessageResponse> PiStreamMessageResponseToIr(
    const IrP4Info &info,
    const p4::v1::StreamMessageResponse &stream_message_response,
    const TranslationOptions &options PDPI_TRANSLATION_OPTIONS_DEFAULT);

// -- Conversions from IR to PI ------------------------------------------------
absl::StatusOr<p4::v1::Entity> IrEntityToPi(
    const IrP4Info &info, const IrEntity &ir,
    const TranslationOptions &options PDPI_TRANSLATION_OPTIONS_DEFAULT);
absl::StatusOr<std::vector<p4::v1::Entity>> IrEntitiesToPi(
    const IrP4Info &info, const IrEntities &ir,
    const TranslationOptions &options PDPI_TRANSLATION_OPTIONS_DEFAULT);

absl::StatusOr<p4::v1::TableEntry> IrTableEntryToPi(
    const IrP4Info &info, const IrTableEntry &ir,
    const TranslationOptions &options PDPI_TRANSLATION_OPTIONS_DEFAULT);
absl::StatusOr<std::vector<p4::v1::TableEntry>> IrTableEntriesToPi(
    const IrP4Info &info, const IrTableEntries &ir,
    const TranslationOptions &options PDPI_TRANSLATION_OPTIONS_DEFAULT);
absl::StatusOr<std::vector<p4::v1::TableEntry>> IrTableEntriesToPi(
    const IrP4Info &info, absl::Span<const IrTableEntry> ir,
    const TranslationOptions &options PDPI_TRANSLATION_OPTIONS_DEFAULT);

absl::StatusOr<p4::v1::PacketReplicationEngineEntry>
IrPacketReplicationEngineEntryToPi(
    const IrP4Info &info, const IrPacketReplicationEngineEntry &ir,
    const TranslationOptions &options PDPI_TRANSLATION_OPTIONS_DEFAULT);

absl::StatusOr<p4::v1::MulticastGroupEntry> IrMulticastGroupEntryToPi(
    const IrP4Info &info, const IrMulticastGroupEntry &ir,
    const TranslationOptions &options PDPI_TRANSLATION_OPTIONS_DEFAULT);

absl::StatusOr<p4::v1::PacketIn> IrPacketInToPi(
    const IrP4Info &info, const IrPacketIn &packet,
    const TranslationOptions &options PDPI_TRANSLATION_OPTIONS_DEFAULT);

absl::StatusOr<p4::v1::PacketOut> IrPacketOutToPi(
    const IrP4Info &info, const IrPacketOut &packet,
    const TranslationOptions &options PDPI_TRANSLATION_OPTIONS_DEFAULT);

absl::StatusOr<p4::v1::ReadRequest> IrReadRequestToPi(
    const IrP4Info &info, const IrReadRequest &read_request,
    const TranslationOptions &options PDPI_TRANSLATION_OPTIONS_DEFAULT);

absl::StatusOr<p4::v1::ReadResponse> IrReadResponseToPi(
    const IrP4Info &info, const IrReadResponse &read_response,
    const TranslationOptions &options PDPI_TRANSLATION_OPTIONS_DEFAULT);

absl::StatusOr<p4::v1::Update> IrUpdateToPi(
    const IrP4Info &info, const IrUpdate &update,
    const TranslationOptions &options PDPI_TRANSLATION_OPTIONS_DEFAULT);

absl::StatusOr<p4::v1::WriteRequest> IrWriteRequestToPi(
    const IrP4Info &info, const IrWriteRequest &write_request,
    const TranslationOptions &options PDPI_TRANSLATION_OPTIONS_DEFAULT);

absl::StatusOr<p4::v1::StreamMessageRequest> IrStreamMessageRequestToPi(
    const IrP4Info &info,
    const IrStreamMessageRequest &ir_stream_message_request,
    const TranslationOptions &options PDPI_TRANSLATION_OPTIONS_DEFAULT);

absl::StatusOr<p4::v1::StreamMessageResponse> IrStreamMessageResponseToPi(
    const IrP4Info &info,
    const IrStreamMessageResponse &ir_stream_message_response,
    const TranslationOptions &options PDPI_TRANSLATION_OPTIONS_DEFAULT);

// Formats a grpc status about write request into a readible string.
std::string WriteRequestGrpcStatusToString(const grpc::Status &grpc_status);

// RPC-level conversion functions for write response.
absl::StatusOr<IrWriteRpcStatus>
GrpcStatusToIrWriteRpcStatus(const grpc::Status &status,
                             int number_of_updates_in_write_request);

absl::StatusOr<grpc::Status>
IrWriteRpcStatusToGrpcStatus(const IrWriteRpcStatus &ir_write_status);

// Translates a Write RPC result (a gRPC status; see P4RT spec for details) into
// a absl::Status. This is useful if one does not care about the individual
// update statuses and only is interested if everything succeeded, or if at
// least one update failed.
absl::Status
WriteRpcGrpcStatusToAbslStatus(const grpc::Status &grpc_status,
                               int number_of_updates_in_write_request);

// -- Conversions from IR to IR ------------------------------------------------

// Converts IrTableEntries to IrEntities.
pdpi::IrEntities
IrTableEntriesToEntities(const pdpi::IrTableEntries &ir_table_entries);

// Convert control plane entries to table entries. Throws an error if there
// entities presents which are not a table entry.
absl::StatusOr<pdpi::IrTableEntries>
IrEntitiesToTableEntries(const pdpi::IrEntities &control_plane_entries);

} // namespace pdpi
#endif // PINS_P4_PDPI_IR_H_
