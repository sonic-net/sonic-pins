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

#include "p4_pdpi/p4_runtime_session.h"

#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_join.h"
#include "absl/strings/substitute.h"
#include "absl/types/span.h"
#include "google/protobuf/descriptor.h"
#include "google/protobuf/repeated_field.h"
#include "google/protobuf/util/message_differencer.h"
#include "grpcpp/channel.h"
#include "grpcpp/create_channel.h"
#include "gutil/status.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/sequencing.h"
#include "p4_pdpi/utils/ir.h"
#include "sai_p4/fixed/roles.h"

namespace pdpi {

using ::p4::config::v1::P4Info;
using ::p4::v1::P4Runtime;
using ::p4::v1::ReadRequest;
using ::p4::v1::ReadResponse;
using ::p4::v1::SetForwardingPipelineConfigRequest;
using ::p4::v1::SetForwardingPipelineConfigResponse;
using ::p4::v1::TableEntry;
using ::p4::v1::Update;
using ::p4::v1::Update_Type;
using ::p4::v1::WriteRequest;
using ::p4::v1::WriteResponse;

// Create P4Runtime Stub.
std::unique_ptr<P4Runtime::Stub> CreateP4RuntimeStub(
    const std::string& address,
    const std::shared_ptr<grpc::ChannelCredentials>& credentials) {
  return P4Runtime::NewStub(grpc::CreateCustomChannel(
      address, credentials, GrpcChannelArgumentsForP4rt()));
}

// Creates a session with the switch, which lasts until the session object is
// destructed.
absl::StatusOr<std::unique_ptr<P4RuntimeSession>> P4RuntimeSession::Create(
    std::unique_ptr<P4Runtime::StubInterface> stub, uint32_t device_id,
    const P4RuntimeSessionOptionalArgs& metadata, bool error_if_not_primary) {
  // Open streaming channel.
  // Using `new` to access a private constructor.
  std::unique_ptr<P4RuntimeSession> session =
      absl::WrapUnique(new P4RuntimeSession(
          device_id, std::move(stub), metadata.election_id, metadata.role));

  // Send arbitration request.
  p4::v1::StreamMessageRequest request;
  auto arbitration = request.mutable_arbitration();
  arbitration->set_device_id(device_id);
  arbitration->mutable_role()->set_name(metadata.role);
  *arbitration->mutable_election_id() = session->election_id_;
  if (!session->stream_channel_->Write(request)) {
    return gutil::UnavailableErrorBuilder()
           << "Unable to initiate P4RT connection to device ID " << device_id
           << "; gRPC stream channel closed.";
  }

  // Wait for arbitration response.
  p4::v1::StreamMessageResponse response;
  if (!session->stream_channel_->Read(&response)) {
    return gutil::InternalErrorBuilder()
           << "P4RT stream closed while awaiting arbitration response: "
           << gutil::GrpcStatusToAbslStatus(session->stream_channel_->Finish());
  }
  if (response.update_case() != p4::v1::StreamMessageResponse::kArbitration) {
    return gutil::InternalErrorBuilder()
           << "No arbitration update received but received the update of "
           << response.update_case() << ": " << response.ShortDebugString();
  }
  if (response.arbitration().device_id() != session->device_id_) {
    return gutil::InternalErrorBuilder() << "Received device id doesn't match: "
                                         << response.ShortDebugString();
  }
  // TODO Enable this check once p4rt app supports role.
  // if (response.arbitration().role().name() != session->role_) {
  //   return gutil::InternalErrorBuilder() << "Received role doesn't match: "
  //                                        << response.ShortDebugString();
  // }
  // If we want to ensure that this session has become primary, then we check,
  // returning the error that we get in the response otherwise.
  if (error_if_not_primary) {
    RETURN_IF_ERROR(gutil::ToAbslStatus(response.arbitration().status()))
            .SetPrepend()
        << absl::Substitute(
               "failed to become primary because given election id '$0' was "
               "less than highest seen election id '$1': ",
               session->election_id_.DebugString(),
               response.arbitration().election_id().DebugString());
  }

  // When object returned doesn't have the same type as the function's return
  // type (i.e. unique_ptr vs StatusOr in this case), certain old compilers
  // won't implicitly wrap the return expressions in std::move(). Then, the case
  // here will trigger the copy of the unique_ptr, which is invalid. Thus, we
  // need to explicitly std::move the returned object here.
  // See:go/totw/labs/should-i-return-std-move.
  return std::move(session);
}

// Creates a session with the switch, which lasts until the session object is
// destructed.
absl::StatusOr<std::unique_ptr<P4RuntimeSession>> P4RuntimeSession::Create(
    const std::string& address,
    const std::shared_ptr<grpc::ChannelCredentials>& credentials,
    uint32_t device_id, const P4RuntimeSessionOptionalArgs& metadata,
    bool error_if_not_primary) {
  return Create(CreateP4RuntimeStub(address, credentials), device_id, metadata,
                error_if_not_primary);
}

// Create the default session with the switch.
std::unique_ptr<P4RuntimeSession> P4RuntimeSession::Default(
    std::unique_ptr<P4Runtime::StubInterface> stub, uint32_t device_id,
    const std::string& role) {
  // Using `new` to access a private constructor.
  return absl::WrapUnique(
      new P4RuntimeSession(device_id, std::move(stub), device_id, role));
}

absl::Status P4RuntimeSession::Finish() {
  stream_channel_->WritesDone();

  // WritesDone() or TryCancel() can close the stream with a CANCELLED status.
  // Because this case is expected we treat CANCELED as OKAY.
  grpc::Status finish = stream_channel_->Finish();
  if (finish.error_code() == grpc::StatusCode::CANCELLED) {
    return absl::OkStatus();
  }
  return gutil::GrpcStatusToAbslStatus(finish);
}

std::vector<Update> CreatePiUpdates(absl::Span<const TableEntry> pi_entries,
                                    Update_Type update_type) {
  std::vector<Update> pi_updates;
  pi_updates.reserve(pi_entries.size());
  for (const auto& pi_entry : pi_entries) {
    Update update;
    update.set_type(update_type);
    *update.mutable_entity()->mutable_table_entry() = pi_entry;
    pi_updates.push_back(std::move(update));
  }
  return pi_updates;
}

absl::StatusOr<ReadResponse> SetMetadataAndSendPiReadRequest(
    P4RuntimeSession* session, ReadRequest& read_request) {
  read_request.set_device_id(session->DeviceId());
  read_request.set_role(session->Role());
  grpc::ClientContext context;
  auto reader = session->Stub().Read(&context, read_request);

  ReadResponse response;
  ReadResponse partial_response;
  while (reader->Read(&partial_response)) {
    response.MergeFrom(partial_response);
  }

  grpc::Status reader_status = reader->Finish();
  if (!reader_status.ok()) {
    return gutil::GrpcStatusToAbslStatus(reader_status);
  }
  return response;
}

absl::Status SendPiWriteRequest(P4Runtime::StubInterface* stub,
                                const p4::v1::WriteRequest& request) {
  grpc::ClientContext context;
  // Empty message; intentionally discarded.
  WriteResponse pi_response;
  RETURN_IF_ERROR(WriteRpcGrpcStatusToAbslStatus(
      stub->Write(&context, request, &pi_response), request.updates_size()))
      << "Failed write request: " << request.DebugString();
  return absl::OkStatus();
}

absl::Status SetMetadataAndSendPiWriteRequest(P4RuntimeSession* session,
                                              WriteRequest& write_request) {
  write_request.set_device_id(session->DeviceId());
  write_request.set_role(session->Role());
  *write_request.mutable_election_id() = session->ElectionId();

  return SendPiWriteRequest(&session->Stub(), write_request);
}

absl::Status SetMetadataAndSendPiWriteRequests(
    P4RuntimeSession* session, std::vector<WriteRequest>& write_requests) {
  for (auto& request : write_requests) {
    RETURN_IF_ERROR(SetMetadataAndSendPiWriteRequest(session, request));
  }
  return absl::OkStatus();
}

absl::StatusOr<std::vector<TableEntry>> ReadPiTableEntries(
    P4RuntimeSession* session) {
  ReadRequest read_request;
  read_request.add_entities()->mutable_table_entry();
  ASSIGN_OR_RETURN(ReadResponse read_response,
                   SetMetadataAndSendPiReadRequest(session, read_request));

  std::vector<TableEntry> table_entries;
  table_entries.reserve(read_response.entities().size());
  for (const auto& entity : read_response.entities()) {
    if (!entity.has_table_entry())
      return gutil::InternalErrorBuilder()
             << "Entity in the read response has no table entry: "
             << entity.DebugString();
    table_entries.push_back(std::move(entity.table_entry()));
  }
  return table_entries;
}

absl::StatusOr<p4::v1::CounterData> ReadPiCounterData(
    P4RuntimeSession* session,
    const p4::v1::TableEntry& target_entry_signature) {
  // Some targets only support wildcard reads, so we read back all entries
  // before looking for the one we are interested in.
  ASSIGN_OR_RETURN(std::vector<TableEntry> entries,
                   ReadPiTableEntries(session));

  // We use a protobuf differ to find the entry we are interested in based on
  // its "signature", given by the `table_id`, `match`, and `priority` fields.
  using google::protobuf::util::MessageDifferencer;
  MessageDifferencer differ;
  differ.set_repeated_field_comparison(MessageDifferencer::AS_SET);
  std::vector<const google::protobuf::FieldDescriptor*> signature_fields;
  for (std::string field_name : {"table_id", "match", "priority"}) {
    const google::protobuf::FieldDescriptor* field_descriptor =
        TableEntry::descriptor()->FindFieldByName(field_name);
    if (field_descriptor == nullptr) {
      return gutil::InternalErrorBuilder()
             << "failed to obtain FieldDescriptor for field '" << field_name
             << "' of p4::v1::TableEntry";
    }
    signature_fields.push_back(field_descriptor);
  }

  for (const auto& entry : entries) {
    if (differ.CompareWithFields(entry, target_entry_signature,
                                 signature_fields, signature_fields)) {
      return entry.counter_data();
    }
  }
  return gutil::NotFoundErrorBuilder()
         << "failed to read counter data for the table entry with the "
            "following signature, since no table entry matching the signature "
            "exists: <"
         << target_entry_signature.ShortDebugString() << ">";
}

absl::Status CheckNoTableEntries(P4RuntimeSession* session) {
  ASSIGN_OR_RETURN(
      p4::v1::GetForwardingPipelineConfigResponse response,
      GetForwardingPipelineConfig(
          session,
          p4::v1::GetForwardingPipelineConfigRequest::P4INFO_AND_COOKIE));
  // If the switch does not have a p4info, then it cannot have any table
  // entries.
  if (!response.has_config()) return absl::OkStatus();

  // If the switch has a p4info, we read all table entries to ensure that there
  // are none.
  ASSIGN_OR_RETURN(auto table_entries, ReadPiTableEntries(session));
  if (!table_entries.empty()) {
    return gutil::UnknownErrorBuilder()
           << "expected no table entries on switch, but "
           << table_entries.size() << " entries remain:\n"
           << absl::StrJoin(table_entries, "",
                            [](std::string* out, auto& entry) {
                              absl::StrAppend(out, entry.DebugString());
                            });
  }
  return absl::OkStatus();
}

absl::Status ClearTableEntries(P4RuntimeSession* session) {
  // Get P4Info from Switch. It is needed to sequence the delete requests.
  ASSIGN_OR_RETURN(
      p4::v1::GetForwardingPipelineConfigResponse response,
      GetForwardingPipelineConfig(
          session, p4::v1::GetForwardingPipelineConfigRequest::ALL));

  // If no p4info has been pushed to the switch, then it cannot have any table
  // entries to clear. Furthermore, reading table entries (i.e. part of the
  // statement after this one) will fail if no p4info has been pushed.
  if (!response.has_config()) return absl::OkStatus();

  // Get table entries.
  ASSIGN_OR_RETURN(auto table_entries, ReadPiTableEntries(session));

  // Early return if there is nothing to clear.
  if (table_entries.empty()) return absl::OkStatus();

  // Convert into IrP4Info.
  ASSIGN_OR_RETURN(IrP4Info info, CreateIrP4Info(response.config().p4info()));

  RETURN_IF_ERROR(RemovePiTableEntries(session, info, table_entries));

  // Verify that all entries were cleared successfully.
  RETURN_IF_ERROR(CheckNoTableEntries(session)).SetPrepend()
      << "cleared all table entries: ";

  return absl::OkStatus();
}

absl::Status RemovePiTableEntries(P4RuntimeSession* session,
                                  const IrP4Info& info,
                                  absl::Span<const TableEntry> pi_entries) {
  std::vector<Update> pi_updates = CreatePiUpdates(pi_entries, Update::DELETE);
  ASSIGN_OR_RETURN(std::vector<WriteRequest> sequenced_clear_requests,
                   pdpi::SequencePiUpdatesIntoWriteRequests(info, pi_updates));
  return SetMetadataAndSendPiWriteRequests(session, sequenced_clear_requests);
}

absl::Status InstallPiTableEntry(P4RuntimeSession* session,
                                 const TableEntry& pi_entry) {
  WriteRequest request;
  Update& update = *request.add_updates();
  update.set_type(Update::INSERT);
  *update.mutable_entity()->mutable_table_entry() = pi_entry;

  return SetMetadataAndSendPiWriteRequest(session, request);
}

absl::Status SendPiUpdates(P4RuntimeSession* session,
                           absl::Span<const p4::v1::Update> updates) {
  WriteRequest request;
  for (const p4::v1::Update& update : updates) {
    *request.add_updates() = update;
  }
  return SetMetadataAndSendPiWriteRequest(session, request);
}

absl::Status InstallPiTableEntries(P4RuntimeSession* session,
                                   const IrP4Info& info,
                                   absl::Span<const TableEntry> pi_entries) {
  std::vector<Update> pi_updates = CreatePiUpdates(pi_entries, Update::INSERT);
  ASSIGN_OR_RETURN(std::vector<WriteRequest> sequenced_write_requests,
                   pdpi::SequencePiUpdatesIntoWriteRequests(info, pi_updates));
  return SetMetadataAndSendPiWriteRequests(session, sequenced_write_requests);
}

absl::Status SetForwardingPipelineConfig(
    P4RuntimeSession* session,
    p4::v1::SetForwardingPipelineConfigRequest::Action action,
    const p4::v1::ForwardingPipelineConfig& config) {
  SetForwardingPipelineConfigRequest request;
  request.set_device_id(session->DeviceId());
  request.set_role(session->Role());
  *request.mutable_election_id() = session->ElectionId();
  request.set_action(action);
  *request.mutable_config() = config;

  // Empty message; intentionally discarded.
  SetForwardingPipelineConfigResponse response;
  grpc::ClientContext context;
  return gutil::GrpcStatusToAbslStatus(
      session->Stub().SetForwardingPipelineConfig(&context, request,
                                                  &response));
}

absl::Status SetForwardingPipelineConfig(
    P4RuntimeSession* session,
    p4::v1::SetForwardingPipelineConfigRequest::Action action,
    const P4Info& p4info, absl::optional<absl::string_view> p4_device_config) {
  p4::v1::ForwardingPipelineConfig config;
  *config.mutable_p4info() = p4info;
  if (p4_device_config.has_value()) {
    *config.mutable_p4_device_config() = *p4_device_config;
  }

  return SetForwardingPipelineConfig(session, action, config);
}

absl::StatusOr<p4::v1::GetForwardingPipelineConfigResponse>
GetForwardingPipelineConfig(
    P4RuntimeSession* session,
    p4::v1::GetForwardingPipelineConfigRequest::ResponseType type) {
  p4::v1::GetForwardingPipelineConfigRequest request;
  request.set_device_id(session->DeviceId());
  request.set_response_type(type);

  grpc::ClientContext context;
  p4::v1::GetForwardingPipelineConfigResponse response;
  grpc::Status response_status =
      session->Stub().GetForwardingPipelineConfig(&context, request, &response);
  if (!response_status.ok()) {
    return gutil::GrpcStatusToAbslStatus(response_status);
  }
  return response;
}

}  // namespace pdpi
