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

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/types/span.h"
#include "grpcpp/grpcpp.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"

namespace pdpi {

// Creates IrP4Info and validates that the p4_info has no errors.
absl::StatusOr<IrP4Info> CreateIrP4Info(const p4::config::v1::P4Info& p4_info);

// -- Conversions from PI to IR ------------------------------------------------
absl::StatusOr<IrTableEntry> PiTableEntryToIr(const IrP4Info& info,
                                              const p4::v1::TableEntry& pi,
                                              bool key_only = false);
absl::StatusOr<std::vector<IrTableEntry>> PiTableEntriesToIr(
    const IrP4Info& info, absl::Span<const p4::v1::TableEntry> pi,
    bool key_only = false);

absl::StatusOr<IrPacketIn> PiPacketInToIr(const IrP4Info& info,
                                          const p4::v1::PacketIn& packet);

absl::StatusOr<IrPacketOut> PiPacketOutToIr(const IrP4Info& info,
                                            const p4::v1::PacketOut& packet);

absl::StatusOr<IrReadRequest> PiReadRequestToIr(
    const IrP4Info& info, const p4::v1::ReadRequest& read_request);

absl::StatusOr<IrReadResponse> PiReadResponseToIr(
    const IrP4Info& info, const p4::v1::ReadResponse& read_response);

absl::StatusOr<IrUpdate> PiUpdateToIr(const IrP4Info& info,
                                      const p4::v1::Update& update);

absl::StatusOr<IrWriteRequest> PiWriteRequestToIr(
    const IrP4Info& info, const p4::v1::WriteRequest& write_request);

absl::StatusOr<IrStreamMessageRequest> PiStreamMessageRequestToIr(
    const IrP4Info& info,
    const p4::v1::StreamMessageRequest& stream_message_request);

absl::StatusOr<IrStreamMessageResponse> PiStreamMessageResponseToIr(
    const IrP4Info& info,
    const p4::v1::StreamMessageResponse& stream_message_response);

// -- Conversions from IR to PI ------------------------------------------------
absl::StatusOr<p4::v1::TableEntry> IrTableEntryToPi(const IrP4Info& info,
                                                    const IrTableEntry& ir,
                                                    bool key_only = false);
absl::StatusOr<std::vector<p4::v1::TableEntry>> IrTableEntriesToPi(
    const IrP4Info& info, absl::Span<const IrTableEntry> ir,
    bool key_only = false);

absl::StatusOr<p4::v1::PacketIn> IrPacketInToPi(const IrP4Info& info,
                                                const IrPacketIn& packet);

absl::StatusOr<p4::v1::PacketOut> IrPacketOutToPi(const IrP4Info& info,
                                                  const IrPacketOut& packet);

absl::StatusOr<p4::v1::ReadRequest> IrReadRequestToPi(
    const IrP4Info& info, const IrReadRequest& read_request);

absl::StatusOr<p4::v1::ReadResponse> IrReadResponseToPi(
    const IrP4Info& info, const IrReadResponse& read_response);

absl::StatusOr<p4::v1::Update> IrUpdateToPi(const IrP4Info& info,
                                            const IrUpdate& update);

absl::StatusOr<p4::v1::WriteRequest> IrWriteRequestToPi(
    const IrP4Info& info, const IrWriteRequest& write_request);

absl::StatusOr<p4::v1::StreamMessageRequest> IrStreamMessageRequestToPi(
    const IrP4Info& info,
    const IrStreamMessageRequest& ir_stream_message_request);

absl::StatusOr<p4::v1::StreamMessageResponse> IrStreamMessageResponseToPi(
    const IrP4Info& info,
    const IrStreamMessageResponse& ir_stream_message_response);

// Formats a grpc status about write request into a readible string.
std::string WriteRequestGrpcStatusToString(const grpc::Status& grpc_status);

// RPC-level conversion functions for write response.
absl::StatusOr<IrWriteRpcStatus> GrpcStatusToIrWriteRpcStatus(
    const grpc::Status& status, int number_of_updates_in_write_request);

absl::StatusOr<grpc::Status> IrWriteRpcStatusToGrpcStatus(
    const IrWriteRpcStatus& ir_write_status);

// Translates a Write RPC result (a gRPC status; see P4RT spec for details) into
// a absl::Status. This is useful if one does not care about the individual
// update statuses and only is interested if everything succeeded, or if at
// least one update failed.
absl::Status WriteRpcGrpcStatusToAbslStatus(
    const grpc::Status& grpc_status, int number_of_updates_in_write_request);
}  // namespace pdpi
#endif  // PINS_P4_PDPI_IR_H_
