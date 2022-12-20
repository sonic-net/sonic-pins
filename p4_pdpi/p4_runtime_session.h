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
#include <optional>
#include <queue>
#include <string>
#include <thread>  // NOLINT: third_party code.
#include <utility>
#include <vector>

#include "absl/base/thread_annotations.h"
#include "absl/memory/memory.h"
#include "absl/numeric/int128.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/synchronization/mutex.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/optional.h"
#include "absl/types/span.h"
#include "grpcpp/security/credentials.h"
#include "gutil/version.h"
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

// Returns the gRPC ChannelArguments for P4Runtime by setting the following:
// - `GRPC_ARG_KEEPALIVE_TIME_MS` to 1s to avoid connection problems and serve
// as reverse path signalling.
// - `GRPC_ARG_HTTP2_MAX_PINGS_WITHOUT_DATA` to 0 to allow KeepAlive ping
// without traffic in the transport,
// - `GRPC_ARG_KEEPALIVE_TIMEOUT_MS` to 10s,
// - `GRPC_ARG_KEEPALIVE_PERMIT_WITHOUT_CALLS` to 1 to allow keepalive on
// grpc::Channel without ongoing RPCs,
// - `GRPC_ARG_MAX_METADATA_SIZE` to P4GRPCMaxMetadataSize because P4RT returns
// batch element status in the grpc::Status, which can require a large metadata
// size.
inline grpc::ChannelArguments
GrpcChannelArgumentsForP4rtWithAggressiveKeepAlive() {
  grpc::ChannelArguments args;
  args.SetInt(GRPC_ARG_MAX_METADATA_SIZE, P4GRPCMaxMetadataSize());
  // Allows grpc::channel to send keepalive ping without on-going traffic.
  args.SetInt(GRPC_ARG_HTTP2_MAX_PINGS_WITHOUT_DATA, 0);
  args.SetInt(GRPC_ARG_KEEPALIVE_PERMIT_WITHOUT_CALLS, 1);
  args.SetInt(GRPC_ARG_KEEPALIVE_TIMEOUT_MS, 4'000 /*4 seconds*/);
  args.SetInt(GRPC_ARG_KEEPALIVE_TIME_MS, 1'000 /*1 second*/);
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

  // Cleanly closes the P4RT stream connection if it hasn't already been
  // stopped.
  ~P4RuntimeSession();

  // Disables copy semantics.
  P4RuntimeSession(const P4RuntimeSession&) = delete;
  P4RuntimeSession& operator=(const P4RuntimeSession&) = delete;

  // Allows move semantics.
  P4RuntimeSession(P4RuntimeSession&&) = default;
  P4RuntimeSession& operator=(P4RuntimeSession&&) = default;

  // Sends the write request, and returns OK if all requests in the batch were
  // handled successfully. If you need to evaluate the result of each request
  // individually consider using WriteAndReturnGrpcStatus.
  absl::Status Write(const p4::v1::WriteRequest& request);

  // Sends the write request, and returns the raw gRPC response from the switch.
  // Notice that the status only means the request was sent and handled
  // correctly, but NOT that the flow was successfully programmed.
  //
  // https://p4.org/p4-spec/p4runtime/main/P4Runtime-Spec.html#sec-error-reporting
  grpc::Status WriteAndReturnGrpcStatus(const p4::v1::WriteRequest& request);

  // Sends the read request, and aggregates all the read responses into a
  // single response. Will return an error if an issue is detected with the
  // stream.
  absl::StatusOr<p4::v1::ReadResponse> Read(const p4::v1::ReadRequest& request);

  // Set/Get methods for the forwarding pipeline.
  absl::Status SetForwardingPipelineConfig(
      const p4::v1::SetForwardingPipelineConfigRequest& request);
  absl::StatusOr<p4::v1::GetForwardingPipelineConfigResponse>
  GetForwardingPipelineConfig(
      const p4::v1::GetForwardingPipelineConfigRequest& request);

  // Returns the id of the node that this session belongs to.
  uint32_t DeviceId() const { return device_id_; }
  // Returns the election id that has been used to perform arbitration.
  p4::v1::Uint128 ElectionId() const { return election_id_; }
  // Returns the role of this session.
  std::string Role() const { return role_; }
  // Thread-safe wrapper around the stream channel's `Read` method.
  // It blocks until the stream message queue is non-empty, the
  // stream channel is closed, or (if specified) the `timeout` is expired .
  ABSL_MUST_USE_RESULT bool StreamChannelRead(
      p4::v1::StreamMessageResponse& response,
      std::optional<absl::Duration> timeout = std::nullopt)
      ABSL_LOCKS_EXCLUDED(stream_read_lock_);
  // Thread-safe wrapper around the stream channel's `Write` method.
  ABSL_MUST_USE_RESULT bool StreamChannelWrite(
      const p4::v1::StreamMessageRequest& request)
      ABSL_LOCKS_EXCLUDED(stream_write_lock_);

  // Closes the RPC connection by telling the server it is done writing, then
  // reads and logs any outstanding messages from the server. Once the server
  // finishes handling all outstanding writes it will close.
  absl::Status Finish()
      ABSL_LOCKS_EXCLUDED(stream_write_lock_, stream_read_lock_);

  // Like `Finish`, but returns any outstanding message from the server.
  absl::StatusOr<std::vector<p4::v1::StreamMessageResponse>>
  ReadStreamChannelResponsesAndFinish()
      ABSL_LOCKS_EXCLUDED(stream_write_lock_, stream_read_lock_);

 private:
  P4RuntimeSession(uint32_t device_id,
                   std::unique_ptr<p4::v1::P4Runtime::StubInterface> stub,
                   absl::uint128 election_id, const std::string& role);

  // Updates the internal state for RPC stream. Logs any changes (e.g. up->down,
  // down->up, but not up->up).
  void set_is_stream_up(bool value)
      ABSL_EXCLUSIVE_LOCKS_REQUIRED(stream_read_lock_);

  // This method should:
  //   * Be Only run inside the `stream_read_thread_`.
  //   * Be the only place where stream_channel_->Read() is called.
  //
  // Collects all messages sent from the server to the client in a queue.
  // Clients can then consume them as needed.
  void CollectStreamReadMessages() ABSL_LOCKS_EXCLUDED(stream_read_lock_);

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

  // Used to ensure atomic reads & writes on the stream_messages_ and writes on
  // the stream channel_. Write lock must be acquired before read lock in cases
  // where both locks are acquired.
  absl::Mutex stream_read_lock_;
  absl::Mutex stream_write_lock_ ABSL_ACQUIRED_BEFORE(stream_read_lock_);

  // Indicates that `WritesDone` and `Finish` have previously been called on the
  // stream channel. We track this since precisely a single call to these
  // methods is allowed.
  bool is_finished_ ABSL_GUARDED_BY(stream_write_lock_) = false;

  // Indicates that the `stream_read_thread_` is active, and still collecting
  // messages from the device.
  bool is_stream_up_ ABSL_GUARDED_BY(stream_read_lock_) = false;

  // We spawn a thread to handle stream read events which arrive asynchronously
  // from the device. It should only ever be running the
  // CollectStreamReadMessages() function.
  std::thread stream_read_thread_;

  // All stream messages are queued by the P4RuntimeSession (ensuring the gRPC
  // stream is flushed and can be cleanly closed) for users to read at their
  // discression.
  std::queue<p4::v1::StreamMessageResponse> stream_messages_
      ABSL_GUARDED_BY(stream_read_lock_);
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

// Checks that there are no table entries.
absl::Status CheckNoTableEntries(P4RuntimeSession* session);

// Clears the table entries. Optionally, `max_batch_size` can be used to limit
// the number of updates in a single write request.
absl::Status ClearTableEntries(
    P4RuntimeSession* session,
    std::optional<int> max_batch_size = std::nullopt);

// Installs the given PI (program independent) table entry on the switch.
absl::Status InstallPiTableEntry(P4RuntimeSession* session,
                                 p4::v1::TableEntry pi_entry);

// Installs the given PI (program independent) table entries on the switch.
absl::Status InstallPiTableEntries(
    P4RuntimeSession* session, const IrP4Info& info,
    absl::Span<const p4::v1::TableEntry> pi_entries);

// Installs the given PI (program independent) entity on the switch.
absl::Status InstallPiEntity(P4RuntimeSession* session,
                             p4::v1::Entity pi_entity);

// Sends the given PI updates to the switch.
absl::Status SendPiUpdates(P4RuntimeSession* session,
                           absl::Span<const p4::v1::Update> pi_updates);

// Sets the forwarding pipeline to the given P4 info and, optionally, device
// configuration.
absl::Status SetMetadataAndSetForwardingPipelineConfig(
    P4RuntimeSession* session,
    p4::v1::SetForwardingPipelineConfigRequest::Action action,
    const p4::config::v1::P4Info& p4info,
    absl::optional<absl::string_view> p4_device_config = absl::nullopt);

// Sets the forwarding pipeline to the given one.
absl::Status SetMetadataAndSetForwardingPipelineConfig(
    P4RuntimeSession* session,
    p4::v1::SetForwardingPipelineConfigRequest::Action action,
    const p4::v1::ForwardingPipelineConfig& config);

// Gets the forwarding pipeline from the device.
absl::StatusOr<p4::v1::GetForwardingPipelineConfigResponse>
GetForwardingPipelineConfig(
    P4RuntimeSession* session,
    p4::v1::GetForwardingPipelineConfigRequest::ResponseType type =
        p4::v1::GetForwardingPipelineConfigRequest::ALL);

// Gets the P4 Info from the device, then parses and returns the `version` field
// specified in the `PkgInfo` message.
// Assumes semantic versioning, i.e. that the `version` field is a string of the
// the form `MAJOR.MINOR.PATCH`.
absl::StatusOr<gutil::Version> GetPkgInfoVersion(P4RuntimeSession* session);

}  // namespace pdpi
#endif  // GOOGLE_P4_PDPI_P4_RUNTIME_SESSION_H_
