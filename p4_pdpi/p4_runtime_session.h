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

#ifndef GOOGLE_P4_PDPI_P4_RUNTIME_SESSION_H_
#define GOOGLE_P4_PDPI_P4_RUNTIME_SESSION_H_

#include <stdint.h>

#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/memory/memory.h"
#include "absl/numeric/int128.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/optional.h"
#include "absl/types/span.h"
#include "grpcpp/security/credentials.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "sai_p4/fixed/roles.h"

namespace pdpi {
// The maximum metadata size that a P4Runtime client should accept.  This is
// necessary, because the P4Runtime protocol returns individual errors to
// requests in a batch all wrapped in a single status, which counts towards the
// metadata size limit.  For large batches, this easily exceeds the default of
// 8KB.
constexpr int P4GRPCMaxMetadataSize() {
  // 1MB.  Assuming 100 bytes per error, this will support batches of around
  // 10000 entries without exceeding the maximum metadata size.
  return 1024 * 1024;
}

// Generates an election id that is monotonically increasing with time.
// Specifically, the upper 64 bits are the unix timestamp in seconds, and the
// lower 64 bits are the remaining milliseconds. This is compatible with
// election-systems that use the same epoch-based election IDs, and in that
// case, this election ID will be guaranteed to be higher than any previous
// election ID.
inline absl::uint128 TimeBasedElectionId() {
  uint64_t msec = absl::ToUnixMillis(absl::Now());
  return absl::MakeUint128(msec / 1000, msec % 1000);
}

// Returns the gRPC ChannelArguments for P4Runtime by setting
// `GRPC_ARG_KEEPALIVE_TIME_MS` (to avoid connection problems) and
// `GRPC_ARG_MAX_METADATA_SIZE` (P4RT returns batch element status in the
// grpc::Status, which can require a large metadata size).
inline grpc::ChannelArguments GrpcChannelArgumentsForP4rt() {
  grpc::ChannelArguments args;
  args.SetInt(GRPC_ARG_MAX_METADATA_SIZE, P4GRPCMaxMetadataSize());
  args.SetInt(GRPC_ARG_KEEPALIVE_TIME_MS, 300000 /*5 minutes*/);

  return args;
}

// Returns the gRPC ChannelArguments for P4Runtime by setting
// `GRPC_ARG_KEEPALIVE_TIME_MS` to 1s to avoid connection problems and serve as
// reverse path signalling.
// `GRPC_ARG_HTTP2_MAX_PINGS_WITHOUT_DATA` to 0 to allow KeepAlive ping without
// traffic in the transport.
// `GRPC_ARG_MAX_METADATA_SIZE` to P4GRPCMaxMetadataSize because P4RT returns
// batch element status in the grpc::Status, which can require a large metadata
// size.
inline grpc::ChannelArguments
GrpcChannelArgumentsForP4rtWithAggressiveKeepAlive() {
  grpc::ChannelArguments args;
  args.SetInt(GRPC_ARG_MAX_METADATA_SIZE, P4GRPCMaxMetadataSize());
  // Allows grpc::channel to send keepalive ping without on-going traffic.
  args.SetInt(GRPC_ARG_HTTP2_MAX_PINGS_WITHOUT_DATA, 0);
  args.SetInt(GRPC_ARG_KEEPALIVE_TIME_MS, 1000 /*1 second*/);
  return args;
}

// This struct contains election id and role string with default values. The
// client can also override them as needed.
struct P4RuntimeSessionOptionalArgs {
  absl::uint128 election_id = TimeBasedElectionId();
  // If client want to use default role to have "full pipeline access", this
  // field needs to be overriden to empty string.
  // See:
  // https://p4.org/p4runtime/spec/main/P4Runtime-Spec.html#sec-default-role.
  std::string role = P4RUNTIME_ROLE_SDN_CONTROLLER;
};

// A P4Runtime session
class P4RuntimeSession {
 public:
  // Creates a session with the switch, which lasts until the session object is
  // destructed. Performs primary arbitration and, if `error_if_not_primary` is
  // set, as it is by default, then if the session is not the primary switch
  // controller:
  // * `ALREADY_EXISTS` will be returned if there is already a primary.
  // * `NOT_FOUND` will be returned if there is no primary.
  static absl::StatusOr<std::unique_ptr<P4RuntimeSession>> Create(
      std::unique_ptr<p4::v1::P4Runtime::StubInterface> stub,
      uint32_t device_id, const P4RuntimeSessionOptionalArgs& metadata = {},
      bool error_if_not_primary = true);
  static absl::StatusOr<std::unique_ptr<P4RuntimeSession>> Create(
      const std::string& address,
      const std::shared_ptr<grpc::ChannelCredentials>& credentials,
      uint32_t device_id, const P4RuntimeSessionOptionalArgs& metadata = {},
      bool error_if_not_primary = true);

  // Connects to the default session on the switch, which has no election_id
  // and which cannot be terminated. This should only be used for testing.
  // The stream_channel and stream_channel_context will be the nullptr.
  static std::unique_ptr<P4RuntimeSession> Default(
      std::unique_ptr<p4::v1::P4Runtime::StubInterface> stub,
      uint32_t device_id,
      const std::string& role = "P4RUNTIME_ROLE_SDN_CONTROLLER");

  // Disables copy semantics.
  P4RuntimeSession(const P4RuntimeSession&) = delete;
  P4RuntimeSession& operator=(const P4RuntimeSession&) = delete;

  // Allows move semantics.
  P4RuntimeSession(P4RuntimeSession&&) = default;
  P4RuntimeSession& operator=(P4RuntimeSession&&) = default;

  // Returns the id of the node that this session belongs to.
  uint32_t DeviceId() const { return device_id_; }
  // Returns the election id that has been used to perform arbitration.
  p4::v1::Uint128 ElectionId() const { return election_id_; }
  // Returns the role of this session.
  std::string Role() const { return role_; }
  // Returns the P4Runtime stub.
  p4::v1::P4Runtime::StubInterface& Stub() { return *stub_; }
  // Reads back stream message response.
  ABSL_MUST_USE_RESULT bool StreamChannelRead(
      p4::v1::StreamMessageResponse& response) {
    return stream_channel_->Read(&response);
  }
  // Writes stream message request.
  ABSL_MUST_USE_RESULT bool StreamChannelWrite(
      const p4::v1::StreamMessageRequest& request) {
    return stream_channel_->Write(request);
  }
  // Cancels the RPC. It is done in a best-effort fashion.
  void TryCancel() { stream_channel_context_->TryCancel(); }
  // Closes the RPC connection by telling the server it is done writing. Once
  // the server finishes handling all outstanding writes it will close.
  absl::Status Finish();

 private:
  P4RuntimeSession(uint32_t device_id,
                   std::unique_ptr<p4::v1::P4Runtime::StubInterface> stub,
                   absl::uint128 election_id, const std::string& role)
      : device_id_(device_id),
        role_(role),
        stub_(std::move(stub)),
        stream_channel_context_(absl::make_unique<grpc::ClientContext>()),
        stream_channel_(stub_->StreamChannel(stream_channel_context_.get())) {
    election_id_.set_high(absl::Uint128High64(election_id));
    election_id_.set_low(absl::Uint128Low64(election_id));
  }

  // The id of the node that this session belongs to.
  uint32_t device_id_;
  // The election id that has been used to perform arbitration.
  p4::v1::Uint128 election_id_;
  // The role of this session.
  std::string role_;
  // The P4Runtime stub of the switch that this session belongs to.
  std::unique_ptr<p4::v1::P4Runtime::StubInterface> stub_;

  // This stream channel and context are used to perform arbitration,
  // but can now also be used for packet IO.
  std::unique_ptr<grpc::ClientContext> stream_channel_context_;
  std::unique_ptr<grpc::ClientReaderWriterInterface<
      p4::v1::StreamMessageRequest, p4::v1::StreamMessageResponse>>
      stream_channel_;
};

// Create P4Runtime stub.
std::unique_ptr<p4::v1::P4Runtime::Stub> CreateP4RuntimeStub(
    const std::string& address,
    const std::shared_ptr<grpc::ChannelCredentials>& credentials);

// -- Helper functions mainly used with `P4RuntimeSession` ---------------------

// Create PI updates from PI table entries.
std::vector<p4::v1::Update> CreatePiUpdates(
    absl::Span<const p4::v1::TableEntry> pi_entries,
    p4::v1::Update_Type update_type);

// Sets the request's metadata (i.e. device id, role). And sends a PI
// (program independent) read request.
absl::StatusOr<p4::v1::ReadResponse> SetMetadataAndSendPiReadRequest(
    P4RuntimeSession* session, p4::v1::ReadRequest& read_request);

// Sets the request's metadata (i.e. device id, role and election id).
// And sends a PI (program independent) write request.
absl::Status SetMetadataAndSendPiWriteRequest(
    P4RuntimeSession* session, p4::v1::WriteRequest& write_request);

// Sends a PI (program independent) write request with given stub.
absl::Status SendPiWriteRequest(p4::v1::P4Runtime::StubInterface* stub,
                                const p4::v1::WriteRequest& request);

// Sets the requests' metadata (i.e. device id, role and election id). And sends
// PI (program independent) write requests.
absl::Status SetMetadataAndSendPiWriteRequests(
    P4RuntimeSession* session,
    std::vector<p4::v1::WriteRequest>& write_requests);

// Reads PI (program independent) table entries.
absl::StatusOr<std::vector<p4::v1::TableEntry>> ReadPiTableEntries(
    P4RuntimeSession* session);

// Reads and returns the `CounterData` for the table entry whose `table_id`,
// `match`, and `priority` fields match `target_entry_signature`, or returns
// NotFoundError if no such table entry exists. Note that on P4Runtime
// standard-compliant targets, at most one matching table entry can exist.
// Other fields of `target_entry_signature` -- e.g. the `action` -- are ignored.
absl::StatusOr<p4::v1::CounterData> ReadPiCounterData(
    P4RuntimeSession* session,
    const p4::v1::TableEntry& target_entry_signature);

// Removes PI (program independent) table entries on the switch.
absl::Status RemovePiTableEntries(
    P4RuntimeSession* session, const IrP4Info& info,
    absl::Span<const p4::v1::TableEntry> pi_entries);

// Checks that there are no table entries.
absl::Status CheckNoTableEntries(P4RuntimeSession* session);

// Clears the table entries.
absl::Status ClearTableEntries(P4RuntimeSession* session);

// Installs the given PI (program independent) table entry on the switch.
absl::Status InstallPiTableEntry(P4RuntimeSession* session,
                                 const p4::v1::TableEntry& pi_entry);

// Installs the given PI (program independent) table entries on the switch.
absl::Status InstallPiTableEntries(
    P4RuntimeSession* session, const IrP4Info& info,
    absl::Span<const p4::v1::TableEntry> pi_entries);

// Sends the given PI updates to the switch.
absl::Status SendPiUpdates(P4RuntimeSession* session,
                           absl::Span<const p4::v1::Update> pi_updates);

// Sets the forwarding pipeline to the given P4 info and, optionally, device
// configuration.
absl::Status SetForwardingPipelineConfig(
    P4RuntimeSession* session,
    p4::v1::SetForwardingPipelineConfigRequest::Action action,
    const p4::config::v1::P4Info& p4info,
    absl::optional<absl::string_view> p4_device_config = absl::nullopt);

// Sets the forwarding pipeline to the given one.
absl::Status SetForwardingPipelineConfig(
    P4RuntimeSession* session,
    p4::v1::SetForwardingPipelineConfigRequest::Action action,
    const p4::v1::ForwardingPipelineConfig& config);

// Gets the forwarding pipeline from the device.
absl::StatusOr<p4::v1::GetForwardingPipelineConfigResponse>
GetForwardingPipelineConfig(
    P4RuntimeSession* session,
    p4::v1::GetForwardingPipelineConfigRequest::ResponseType type =
        p4::v1::GetForwardingPipelineConfigRequest::ALL);

}  // namespace pdpi
#endif  // GOOGLE_P4_PDPI_P4_RUNTIME_SESSION_H_
