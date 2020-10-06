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
#include "p4rt_app/p4runtime/p4runtime_impl.h"

#include <endian.h>

#include <iomanip>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <type_traits>

#include "absl/memory/memory.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/substitute.h"
#include "glog/logging.h"
#include "google/protobuf/descriptor.h"
#include "google/protobuf/util/message_differencer.h"
#include "google/rpc/code.pb.h"
#include "grpcpp/impl/codegen/status.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_constraints/backend/constraint_info.h"
#include "p4_constraints/backend/interpreter.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/utils/annotation_parser.h"
#include "p4_pdpi/utils/ir.h"
#include "p4rt_app/p4runtime/ir_translation.h"
#include "p4rt_app/p4runtime/p4info_verification.h"
#include "p4rt_app/sonic/app_db_acl_def_table_manager.h"
#include "p4rt_app/sonic/app_db_manager.h"
#include "p4rt_app/sonic/packetio_port.h"
#include "p4rt_app/sonic/response_handler.h"
#include "p4rt_app/sonic/vrf_entry_translation.h"
#include "p4rt_app/utils/status_utility.h"
#include "p4rt_app/utils/table_utility.h"
#include "sai_p4/fixed/ids.h"
#include "sai_p4/fixed/roles.h"

namespace p4rt_app {
namespace {

using ::google::protobuf::util::MessageDifferencer;

absl::Status SupportedTableEntryRequest(const p4::v1::TableEntry& table_entry) {
  if (table_entry.table_id() != 0 || !table_entry.match().empty() ||
      table_entry.priority() != 0 || !table_entry.metadata().empty() ||
      table_entry.has_action() || table_entry.is_default_action() != false) {
    return gutil::UnimplementedErrorBuilder()
           << "Read request for table entry: "
           << table_entry.ShortDebugString();
  }
  return absl::OkStatus();
}

absl::Status AllowRoleAccessToTable(const std::string& role_name,
                                    const std::string& table_name,
                                    const pdpi::IrP4Info& p4_info) {
  // The defulat role can access any table.
  if (role_name.empty()) return absl::OkStatus();

  auto table_def = p4_info.tables_by_name().find(table_name);
  if (table_def == p4_info.tables_by_name().end()) {
    return gutil::InternalErrorBuilder()
           << "Could not find table '" << table_name
           << "' when checking role access. Did an IR translation fail "
              "somewhere?";
  }

  if (table_def->second.role() != role_name) {
    return gutil::PermissionDeniedErrorBuilder()
           << "Role '" << role_name << "' is not allowd access to table '"
           << table_name << "'.";
  }

  return absl::OkStatus();
}

sonic::AppDbTableType GetAppDbTableType(
    const pdpi::IrTableEntry& ir_table_entry) {
  if (ir_table_entry.table_name() == "vrf_table") {
    return sonic::AppDbTableType::VRF_TABLE;
  }

  // By default we assume and AppDb P4RT entry.
  return sonic::AppDbTableType::P4RT;
}

// Read P4Runtime table entries out of the AppDb, and append them to the read
// response.
absl::Status AppendTableEntryReads(
    p4::v1::ReadResponse& response, const p4::v1::TableEntry& pi_table_entry,
    const pdpi::IrP4Info& p4_info, const std::string& role_name,
    bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    swss::DBConnectorInterface& app_db_client,
    swss::DBConnectorInterface& counters_db_client) {
  RETURN_IF_ERROR(SupportedTableEntryRequest(pi_table_entry));

  // Get all P4RT keys from the AppDb.
  for (const auto& app_db_key :
       sonic::GetAllAppDbP4TableEntryKeys(app_db_client)) {
    // Read a single table entry out of the AppDb
    ASSIGN_OR_RETURN(
        pdpi::IrTableEntry ir_table_entry,
        sonic::ReadAppDbP4TableEntry(p4_info, app_db_client, counters_db_client,
                                     app_db_key));

    // Only attach the entry if the role expects it.
    auto allow_access =
        AllowRoleAccessToTable(role_name, ir_table_entry.table_name(), p4_info);
    if (!allow_access.ok()) {
      VLOG(2) << "Ignoring read: " << allow_access;
      continue;
    }

    RETURN_IF_ERROR(TranslateTableEntry(
        TranslateTableEntryOptions{
            .direction = TranslationDirection::kForController,
            .ir_p4_info = p4_info,
            .translate_port_ids = translate_port_ids,
            .port_map = port_translation_map},
        ir_table_entry));

    auto translate_status = pdpi::IrTableEntryToPi(p4_info, ir_table_entry);
    if (!translate_status.ok()) {
      LOG(ERROR) << "PDPI could not translate IR table entry to PI: "
                 << ir_table_entry.DebugString();
      return gutil::StatusBuilder(translate_status.status().code())
             << "[P4RT/PDPI] " << translate_status.status().message();
    }
    *response.add_entities()->mutable_table_entry() = *translate_status;
  }

  // Get all VRF_TABLE entries from the AppDb.
  ASSIGN_OR_RETURN(std::vector<pdpi::IrTableEntry> vrf_entries,
                   sonic::GetAllAppDbVrfTableEntries(app_db_client));
  for (const auto& ir_table_entry : vrf_entries) {
    auto translate_status = pdpi::IrTableEntryToPi(p4_info, ir_table_entry);
    if (!translate_status.ok()) {
      LOG(ERROR) << "PDPI could not translate IR table entry to PI: "
                 << ir_table_entry.DebugString();
      return gutil::StatusBuilder(translate_status.status().code())
             << "[P4RT/PDPI] " << translate_status.status().message();
    }
    *response.add_entities()->mutable_table_entry() = *translate_status;
  }
  return absl::OkStatus();
}

absl::StatusOr<p4::v1::ReadResponse> DoRead(
    const p4::v1::ReadRequest& request, const pdpi::IrP4Info p4_info,
    bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    swss::DBConnectorInterface& app_db_client,
    swss::DBConnectorInterface& counters_db_client) {
  p4::v1::ReadResponse response;
  for (const auto& entity : request.entities()) {
    LOG(INFO) << "Read request: " << entity.ShortDebugString();
    switch (entity.entity_case()) {
      case p4::v1::Entity::kTableEntry: {
        RETURN_IF_ERROR(AppendTableEntryReads(
            response, entity.table_entry(), p4_info, request.role(),
            translate_port_ids, port_translation_map, app_db_client,
            counters_db_client));
        break;
      }
      default:
        return gutil::UnimplementedErrorBuilder()
               << "Read has not been implemented for: "
               << entity.ShortDebugString();
    }
  }
  return response;
}

// Generates a StreamMessageResponse error based on an absl::Status.
p4::v1::StreamMessageResponse GenerateErrorResponse(absl::Status status) {
  grpc::Status grpc_status = gutil::AbslStatusToGrpcStatus(status);
  p4::v1::StreamMessageResponse response;
  auto error = response.mutable_error();
  error->set_canonical_code(grpc_status.error_code());
  error->set_message(grpc_status.error_message());
  return response;
}

// Generates StreamMessageResponse with errors for PacketIO
p4::v1::StreamMessageResponse GenerateErrorResponse(
    absl::Status status, const p4::v1::PacketOut& packet) {
  p4::v1::StreamMessageResponse response = GenerateErrorResponse(status);
  *response.mutable_error()->mutable_packet_out()->mutable_packet_out() =
      packet;
  return response;
}

// Compares two P4Info protobufs and returns true if they represent the
// same information. Differences are reported in the optional string.
bool P4InfoEquals(const p4::config::v1::P4Info& left,
                  const p4::config::v1::P4Info& right,
                  std::string* diff_report) {
  google::protobuf::util::MessageDifferencer differencer;
  differencer.set_repeated_field_comparison(
      google::protobuf::util::MessageDifferencer::AS_SMART_SET);
  differencer.set_report_matches(false);
  differencer.set_report_moves(false);
  if (diff_report != nullptr) {
    differencer.ReportDifferencesToString(diff_report);
  }
  return differencer.Compare(left, right);
}

absl::StatusOr<pdpi::IrTableEntry> DoPiTableEntryToIr(
    const p4::v1::TableEntry& pi_table_entry, const pdpi::IrP4Info& p4_info,
    const std::string& role_name, bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    bool translate_key_only) {
  auto translate_status =
      pdpi::PiTableEntryToIr(p4_info, pi_table_entry, translate_key_only);
  if (!translate_status.ok()) {
    LOG(WARNING) << "PDPI could not translate PI table entry to IR: "
                 << pi_table_entry.DebugString();
    return gutil::StatusBuilder(translate_status.status().code())
           << "[P4RT/PDPI] " << translate_status.status().message();
  }
  pdpi::IrTableEntry ir_table_entry = *translate_status;

  // Verify the table entry can be written to the table.
  RETURN_IF_ERROR(
      AllowRoleAccessToTable(role_name, ir_table_entry.table_name(), p4_info));

  RETURN_IF_ERROR(TranslateTableEntry(
      TranslateTableEntryOptions{
          .direction = TranslationDirection::kForOrchAgent,
          .ir_p4_info = p4_info,
          .translate_port_ids = translate_port_ids,
          .port_map = port_translation_map},
      ir_table_entry));
  return ir_table_entry;
}

sonic::AppDbUpdates PiTableEntryUpdatesToIr(
    const p4::v1::WriteRequest& request, const pdpi::IrP4Info& p4_info,
    const p4_constraints::ConstraintInfo& constraint_info,
    bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    pdpi::IrWriteResponse* response) {
  sonic::AppDbUpdates ir_updates;
  for (const auto& update : request.updates()) {
    // An RPC response should be created for every updater.
    auto entry_status = response->add_statuses();
    ++ir_updates.total_rpc_updates;

    // If the constraints are not met then we should just report an error (i.e.
    // do not try to handle the entry in lower layers).
    absl::StatusOr<bool> meets_constraint =
        p4_constraints::EntryMeetsConstraint(update.entity().table_entry(),
                                             constraint_info);
    if (!meets_constraint.ok()) {
      // A status failure implies that the TableEntry was not formatted
      // correctly. So we could not check the constraints.
      LOG(WARNING) << "Could not verify P4 constraint: "
                   << update.entity().table_entry().DebugString();
      *entry_status = GetIrUpdateStatus(meets_constraint.status());
      continue;
    }
    if (*meets_constraint == false) {
      // A false result implies the constraints were not met.
      LOG(WARNING) << "Entry does not meet P4 constraint: "
                   << update.entity().table_entry().DebugString();
      *entry_status = GetIrUpdateStatus(
          gutil::InvalidArgumentErrorBuilder()
          << "Does not meet constraints required for the table entry.");
      continue;
    }

    // If we cannot translate it then we should just report an error (i.e. do
    // not try to handle it in lower layers). When doing a DELETE, translate
    // only the key part of the table entry because, from the specs, the control
    // plane is not required to send the full entry.
    auto ir_table_entry = DoPiTableEntryToIr(
        update.entity().table_entry(), p4_info, request.role(),
        translate_port_ids, port_translation_map,
        update.type() == p4::v1::Update::DELETE);
    *entry_status = GetIrUpdateStatus(ir_table_entry.status());
    if (!ir_table_entry.ok()) {
      LOG(WARNING) << "Could not translate PI to IR: "
                   << update.entity().table_entry().DebugString();
      continue;
    }

    int rpc_index = response->statuses_size() - 1;
    ir_updates.entries.push_back(sonic::AppDbEntry{
        .rpc_index = rpc_index,
        .entry = *ir_table_entry,
        .update_type = update.type(),
        .appdb_table = GetAppDbTableType(*ir_table_entry),
    });
  }
  return ir_updates;
}

}  // namespace

P4RuntimeImpl::P4RuntimeImpl(
    std::unique_ptr<swss::DBConnectorInterface> app_db_client,
    std::unique_ptr<swss::DBConnectorInterface> state_db_client,
    std::unique_ptr<swss::DBConnectorInterface> counter_db_client,
    std::unique_ptr<swss::ProducerStateTableInterface> app_db_table_p4rt,
    std::unique_ptr<swss::ConsumerNotifierInterface> app_db_notifier_p4rt,
    std::unique_ptr<swss::ProducerStateTableInterface> app_db_table_vrf,
    std::unique_ptr<swss::ConsumerNotifierInterface> app_db_notifier_vrf,
    std::unique_ptr<sonic::PacketIoInterface> packetio_impl, bool use_genetlink,
    bool translate_port_ids)
    : app_db_client_(std::move(app_db_client)),
      state_db_client_(std::move(state_db_client)),
      counter_db_client_(std::move(counter_db_client)),
      app_db_table_p4rt_(std::move(app_db_table_p4rt)),
      app_db_notifier_p4rt_(std::move(app_db_notifier_p4rt)),
      app_db_table_vrf_(std::move(app_db_table_vrf)),
      app_db_notifier_vrf_(std::move(app_db_notifier_vrf)),
      packetio_impl_(std::move(packetio_impl)),
      translate_port_ids_(translate_port_ids) {
  absl::optional<std::string> init_failure;

  // Start the controller manager.
  controller_manager_ = absl::make_unique<SdnControllerManager>();

  // Spawn the receiver thread to receive In packets.
  auto status_or = StartReceive(use_genetlink);
  if (status_or.ok()) {
    receive_thread_ = std::move(*status_or);
  } else {
    init_failure = absl::StrCat("Failed to spawn Receive thread, error: ",
                                status_or.status().ToString());
  }
}

absl::Status SendPacketOut(
    const pdpi::IrP4Info& p4_info, bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    sonic::PacketIoInterface* const packetio_impl,
    const p4::v1::PacketOut& packet) {
  // Convert to IR to check validity of PacketOut message (e.g. duplicate or
  // missing metadata fields).
  auto translate_status = pdpi::PiPacketOutToIr(p4_info, packet);
  if (!translate_status.ok()) {
    LOG(WARNING) << "PDPI PacketOutToIr failure: " << translate_status.status();
    LOG(WARNING) << "PDPI could not translate PacketOut packet: "
                 << packet.DebugString();
    return gutil::StatusBuilder(translate_status.status().code())
           << "[P4RT/PDPI] " << translate_status.status().message();
  }
  auto ir = *translate_status;

  std::string egress_port_id;
  int submit_to_ingress = 0;
  // Parse the packet metadata to get the value of different attributes,
  for (const auto& meta : packet.metadata()) {
    switch (meta.metadata_id()) {
      case PACKET_OUT_EGRESS_PORT_ID: {
        egress_port_id = meta.value();
        break;
      }
      case PACKET_OUT_SUBMIT_TO_INGRESS_ID: {
        ASSIGN_OR_RETURN(
            submit_to_ingress,
            pdpi::ArbitraryByteStringToUint(meta.value(), /*bitwidth=*/1),
            _ << "Unable to get inject_ingress from the packet metadata");
        break;
      }
      case PACKET_OUT_UNUSED_PAD_ID: {
        // Nothing to do.
        break;
      }
      default:
        return gutil::InvalidArgumentErrorBuilder()
               << "Unexpected Packet Out metadata id " << meta.metadata_id();
    }
  }

  std::string sonic_port_name;
  if (submit_to_ingress == 1) {
    // Use submit_to_ingress attribute value netdev port.
    sonic_port_name = std::string(sonic::kSubmitToIngress);
  } else {
    // Use egress_port_id attribute value.
    if (translate_port_ids) {
      ASSIGN_OR_RETURN(sonic_port_name,
                       TranslatePort(TranslationDirection::kForOrchAgent,
                                     port_translation_map, egress_port_id));
    } else {
      sonic_port_name = egress_port_id;
    }
  }

  // Send packet out via the socket.
  RETURN_IF_ERROR(
      packetio_impl->SendPacketOut(sonic_port_name, packet.payload()));

  return absl::OkStatus();
}

// Adds the given metadata to the PacketIn.
absl::StatusOr<p4::v1::PacketIn> CreatePacketInMessage(
    const std::string& source_port_id, const std::string& target_port_id) {
  p4::v1::PacketIn packet;
  p4::v1::PacketMetadata* metadata = packet.add_metadata();
  // Add Ingress port id.
  metadata->set_metadata_id(PACKET_IN_INGRESS_PORT_ID);
  metadata->set_value(source_port_id);

  // Add target egress port id.
  metadata = packet.add_metadata();
  metadata->set_metadata_id(PACKET_IN_TARGET_EGRESS_PORT_ID);
  metadata->set_value(target_port_id);

  return packet;
}

grpc::Status P4RuntimeImpl::Write(grpc::ServerContext* context,
                                  const p4::v1::WriteRequest* request,
                                  p4::v1::WriteResponse* response) {
#ifdef __EXCEPTIONS
  try {
#endif
    absl::MutexLock l(&server_state_lock_);

    // Verify the request comes from the primary connection.
    auto connection_status = controller_manager_->AllowRequest(*request);
    if (!connection_status.ok()) {
      return connection_status;
    }

    // We can only program the flow if the forwarding pipeline has been set.
    if (!ir_p4info_.has_value()) {
      return grpc::Status(grpc::StatusCode::FAILED_PRECONDITION,
                          "Switch has not configured the forwarding pipeline.");
    }

    pdpi::IrWriteRpcStatus rpc_status;
    pdpi::IrWriteResponse* rpc_response = rpc_status.mutable_rpc_response();
    sonic::AppDbUpdates app_db_updates = PiTableEntryUpdatesToIr(
        *request, *ir_p4info_, *p4_constraint_info_, translate_port_ids_,
        port_translation_map_, rpc_response);

    // Any AppDb update failures should be appended to the `rpc_response`. If
    // UpdateAppDb fails we should go critical.
    auto app_db_write_status = sonic::UpdateAppDb(
        app_db_updates, *ir_p4info_, *app_db_table_p4rt_,
        *app_db_notifier_p4rt_, *app_db_client_, *state_db_client_,
        *app_db_table_vrf_, *app_db_notifier_vrf_, rpc_response);

    auto grpc_status = pdpi::IrWriteRpcStatusToGrpcStatus(rpc_status);
    if (!grpc_status.ok()) {
      LOG(ERROR) << "PDPI failed to translate RPC status to gRPC status: "
                 << rpc_status.DebugString();
    }
    return *grpc_status;
#ifdef __EXCEPTIONS
  } catch (const std::exception& e) {
    LOG(FATAL) << "Exception caught in " << __func__ << ", error:" << e.what();
  } catch (...) {
    LOG(FATAL) << "Unknown exception caught in " << __func__ << ".";
  }
#endif
}

grpc::Status P4RuntimeImpl::Read(
    grpc::ServerContext* context, const p4::v1::ReadRequest* request,
    grpc::ServerWriter<p4::v1::ReadResponse>* response_writer) {
  absl::MutexLock l(&server_state_lock_);
#ifdef __EXCEPTIONS
  try {
#endif
    if (!ir_p4info_.has_value()) {
      return grpc::Status(grpc::StatusCode::FAILED_PRECONDITION,
                          "Switch has no ForwardingPipelineConfig.");
    }
    if (request == nullptr) {
      return grpc::Status(grpc::StatusCode::INVALID_ARGUMENT,
                          "ReadRequest cannot be a nullptr.");
    }
    if (response_writer == nullptr) {
      return grpc::Status(grpc::StatusCode::INVALID_ARGUMENT,
                          "ReadResponse writer cannot be a nullptr.");
    }

    auto response_status =
        DoRead(*request, ir_p4info_.value(), translate_port_ids_,
               port_translation_map_, *app_db_client_, *counter_db_client_);
    if (!response_status.ok()) {
      LOG(WARNING) << "Read failure: " << response_status.status();
      return grpc::Status(
          grpc::StatusCode::UNKNOWN,
          absl::StrCat("Read failure: ", response_status.status().ToString()));
    }

    response_writer->Write(response_status.value());
    return grpc::Status::OK;
#ifdef __EXCEPTIONS
  } catch (const std::exception& e) {
    LOG(FATAL) << "Exception caught in " << __func__ << ", error:" << e.what();
  } catch (...) {
    LOG(FATAL) << "Unknown exception caught in " << __func__ << ".";
  }
#endif
}

grpc::Status P4RuntimeImpl::StreamChannel(
    grpc::ServerContext* context,
    grpc::ServerReaderWriter<p4::v1::StreamMessageResponse,
                             p4::v1::StreamMessageRequest>* stream) {
#ifdef __EXCEPTIONS
  try {
#endif
    // We create a unique SDN connection object for every active connection.
    auto sdn_connection = absl::make_unique<SdnConnection>(context, stream);

    // While the connection is active we can receive and send requests.
    p4::v1::StreamMessageRequest request;
    while (stream->Read(&request)) {
      absl::MutexLock l(&server_state_lock_);

      switch (request.update_case()) {
        case p4::v1::StreamMessageRequest::kArbitration: {
          LOG(INFO) << "Received arbitration request: "
                    << request.ShortDebugString();

          auto status = controller_manager_->HandleArbitrationUpdate(
              request.arbitration(), sdn_connection.get());
          if (!status.ok()) {
            LOG(WARNING) << "Failed arbitration request: "
                         << status.error_message();
            controller_manager_->Disconnect(sdn_connection.get());
            return status;
          }
          break;
        }
        case p4::v1::StreamMessageRequest::kPacket: {
          // Returns with an error if the write request was not received from a
          // primary connection
          bool is_primary = controller_manager_
                                ->AllowRequest(sdn_connection->GetRoleName(),
                                               sdn_connection->GetElectionId())
                                .ok();
          if (!is_primary) {
            sdn_connection->SendStreamMessageResponse(GenerateErrorResponse(
                gutil::PermissionDeniedErrorBuilder()
                    << "Cannot process request. Only the primary connection "
                       "can send PacketOuts.",
                request.packet()));
          } else {
            if (!ir_p4info_.has_value()) {
              sdn_connection->SendStreamMessageResponse(GenerateErrorResponse(
                  gutil::FailedPreconditionErrorBuilder()
                  << "Cannot send packet out. Switch has no "
                     "ForwardingPipelineConfig."));
            } else {
              auto status =
                  SendPacketOut(ir_p4info_.value(), translate_port_ids_,
                                port_translation_map_, packetio_impl_.get(),
                                request.packet());
              if (!status.ok()) {
                // Get the primary streamchannel and write into the stream.
                controller_manager_->SendStreamMessageToPrimary(
                    sdn_connection->GetRoleName(),
                    GenerateErrorResponse(gutil::StatusBuilder(status)
                                              << "Failed to send packet out.",
                                          request.packet()));
              }
            }
          }
          break;
        }
        case p4::v1::StreamMessageRequest::kDigestAck:
        case p4::v1::StreamMessageRequest::kOther:
        default:
          sdn_connection->SendStreamMessageResponse(
              GenerateErrorResponse(gutil::UnimplementedErrorBuilder()
                                    << "Stream update type is not supported."));
          LOG(ERROR) << "Received unhandled stream channel message: "
                     << request.DebugString();
      }
    }

    {
      absl::MutexLock l(&server_state_lock_);
      controller_manager_->Disconnect(sdn_connection.get());
    }
    return grpc::Status::OK;
#ifdef __EXCEPTIONS
  } catch (const std::exception& e) {
    LOG(FATAL) << "Exception caught in " << __func__ << ", error:" << e.what();
  } catch (...) {
    LOG(FATAL) << "Unknown exception caught in " << __func__ << ".";
  }
#endif
}

grpc::Status P4RuntimeImpl::SetForwardingPipelineConfig(
    grpc::ServerContext* context,
    const p4::v1::SetForwardingPipelineConfigRequest* request,
    p4::v1::SetForwardingPipelineConfigResponse* response) {
#ifdef __EXCEPTIONS
  try {
#endif
    absl::MutexLock l(&server_state_lock_);
    LOG(INFO)
        << "Received SetForwardingPipelineConfig request from election id: "
        << request->election_id().ShortDebugString();
    auto connection_status = controller_manager_->AllowRequest(*request);
    if (!connection_status.ok()) {
      return connection_status;
    }

    if (request->action() !=
            p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT &&
        request->action() !=
            p4::v1::SetForwardingPipelineConfigRequest::VERIFY_AND_COMMIT) {
      return AbslStatusToGrpcStatus(
          gutil::UnimplementedErrorBuilder().LogError()
          << "Only Action RECONCILE_AND_COMMIT or VERIFY_AND_COMMIT is "
             "supported for "
          << "SetForwardingPipelineConfig.");
    }

    {
      absl::Status validate_result = ValidateP4Info(request->config().p4info());
      if (!validate_result.ok()) {
        // TODO (b/181241450): Re-enable verification checks before SB400 DVT
        // end.
        LOG(WARNING) << "P4Info is not valid. Details: " << validate_result;
        /*
        return gutil::AbslStatusToGrpcStatus(
            gutil::StatusBuilder(validate_result.code()).LogError()
            << "P4Info is not valid. Details: " << validate_result.message());
        */
      }
    }

    // Fail if the new forwarding pipeline is different from the current one.
    std::string diff_report;
    if (forwarding_pipeline_config_.has_value() &&
        !P4InfoEquals(forwarding_pipeline_config_->p4info(),
                      request->config().p4info(), &diff_report)) {
      return gutil::AbslStatusToGrpcStatus(
          gutil::UnimplementedErrorBuilder().LogError()
          << "Modifying a configured forwarding pipeline is not currently "
             "supported. Please reboot the device. Configuration "
             "differences:\n"
          << diff_report);
    }

    // Collect any P4RT constraints from the P4Info.
    auto constraint_info =
        p4_constraints::P4ToConstraintInfo(request->config().p4info());
    if (!constraint_info.ok()) {
      LOG(WARNING) << "Could not get constraint info from P4Info: "
                   << constraint_info.status();
      return gutil::AbslStatusToGrpcStatus(
          absl::Status(constraint_info.status().code(),
                       absl::StrCat("[P4 Constraint] ",
                                    constraint_info.status().message())));
    }
    p4_constraint_info_ = *std::move(constraint_info);

    auto ir_p4info_result = pdpi::CreateIrP4Info(request->config().p4info());
    if (!ir_p4info_result.ok())
      return gutil::AbslStatusToGrpcStatus(ir_p4info_result.status());
    pdpi::IrP4Info new_ir_p4info = std::move(ir_p4info_result.value());
    TranslateIrP4InfoForOrchAgent(new_ir_p4info);

    if (!ir_p4info_.has_value()) {
      // Apply a config if we don't currently have one.
      absl::Status config_result = ApplyForwardingPipelineConfig(new_ir_p4info);
      if (!config_result.ok()) {
        // TODO: cleanup P4RT table definitions.
        LOG(FATAL) << "Failed to apply ForwardingPipelineConfig: "
                   << config_result;
      }
      ir_p4info_ = std::move(new_ir_p4info);
    }
    forwarding_pipeline_config_ = request->config();
    LOG(INFO) << "SetForwardingPipelineConfig completed successfully.";

    // Collect any port ID to port name translations;
    if (translate_port_ids_) {
      auto port_map_result = sonic::GetPortIdTranslationMap(*app_db_client_);
      if (!port_map_result.ok()) {
        return gutil::AbslStatusToGrpcStatus(port_map_result.status());
      }
      port_translation_map_ = *port_map_result;
      LOG(INFO) << "Collected port ID to port name mappings.";
    }

#ifdef __EXCEPTIONS
  } catch (const std::exception& e) {
    LOG(FATAL) << "Exception caught in " << __func__ << ", error:" << e.what();
  } catch (...) {
    LOG(FATAL) << "Unknown exception caught in " << __func__ << ".";
  }
#endif

  return grpc::Status(grpc::StatusCode::OK, "");
}

grpc::Status P4RuntimeImpl::GetForwardingPipelineConfig(
    grpc::ServerContext* context,
    const p4::v1::GetForwardingPipelineConfigRequest* request,
    p4::v1::GetForwardingPipelineConfigResponse* response) {
  absl::MutexLock l(&server_state_lock_);
#ifdef __EXCEPTIONS
  try {
#endif
    if (ir_p4info_.has_value()) {
      switch (request->response_type()) {
        case p4::v1::GetForwardingPipelineConfigRequest::COOKIE_ONLY:
          *response->mutable_config()->mutable_cookie() =
              forwarding_pipeline_config_.value().cookie();
          break;
        default:
          *response->mutable_config() = forwarding_pipeline_config_.value();
          break;
      }
    }
    return grpc::Status(grpc::StatusCode::OK, "");
#ifdef __EXCEPTIONS
  } catch (const std::exception& e) {
    LOG(FATAL) << "Exception caught in " << __func__ << ", error:" << e.what();
  } catch (...) {
    LOG(FATAL) << "Unknown exception caught in " << __func__ << ".";
  }
#endif
}

absl::Status P4RuntimeImpl::ApplyForwardingPipelineConfig(
    const pdpi::IrP4Info& ir_p4info) {
  // Setup definitions for each each P4 ACL table.
  for (const auto& pair : ir_p4info.tables_by_name()) {
    std::string table_name = pair.first;
    pdpi::IrTableDefinition table = pair.second;
    ASSIGN_OR_RETURN(table::Type table_type, GetTableType(table),
                     _ << "Failed to configure table " << table_name << ".");

    // Add ACL table definition to AppDb (if applicable).
    if (table_type == table::Type::kAcl) {
      LOG(INFO) << "Configuring ACL table: " << table_name;
      ASSIGN_OR_RETURN(
          std::string acl_key,
          sonic::InsertAclTableDefinition(*app_db_table_p4rt_, table),
          _ << "Failed to add ACL table definition [" << table_name
            << "] to AppDb.");

      // Wait for OA to confirm it can realize the table updates.
      ASSIGN_OR_RETURN(
          pdpi::IrUpdateStatus status,
          sonic::GetAndProcessResponseNotification(
              app_db_table_p4rt_->get_table_name(), *app_db_notifier_p4rt_,
              *app_db_client_, *state_db_client_, acl_key));

      // Any issue with the forwarding config should be sent back to the
      // controller as an INVALID_ARGUMENT.
      if (status.code() != google::rpc::OK) {
        return gutil::InvalidArgumentErrorBuilder() << status.message();
      }
    }
  }

  return absl::OkStatus();
}

absl::StatusOr<std::thread> P4RuntimeImpl::StartReceive(bool use_genetlink) {
  // Define the lambda function for the callback to be executed for every
  // receive packet.
  auto SendPacketInToController =
      [this](const std::string& source_port_name,
             const std::string& target_port_name,
             const std::string& payload) -> absl::Status {
    absl::MutexLock l(&server_state_lock_);

    // Convert Sonic port name to controller port number.
    std::string source_port_id;
    if (translate_port_ids_) {
      ASSIGN_OR_RETURN(source_port_id,
                       TranslatePort(TranslationDirection::kForController,
                                     port_translation_map_, source_port_name),
                       _.SetCode(absl::StatusCode::kInternal).LogError()
                           << "Failed to parse source port");
    } else {
      source_port_id = source_port_name;
    }

    // TODO: Until string port names are supported, re-assign empty
    // target egress port names to match the ingress port.
    std::string target_port_id = source_port_id;
    if (!target_port_name.empty()) {
      if (translate_port_ids_) {
        ASSIGN_OR_RETURN(target_port_id,
                         TranslatePort(TranslationDirection::kForController,
                                       port_translation_map_, target_port_name),
                         _.SetCode(absl::StatusCode::kInternal).LogError()
                             << "Failed to parse target port");
      } else {
        target_port_id = target_port_name;
      }
    }

    // Form the PacketIn metadata fields before writing into the
    // stream.
    ASSIGN_OR_RETURN(auto packet_in,
                     CreatePacketInMessage(source_port_id, target_port_id));
    p4::v1::StreamMessageResponse response;
    *response.mutable_packet() = packet_in;
    *response.mutable_packet()->mutable_payload() = payload;
    // Get the primary streamchannel and write into the stream.
    controller_manager_->SendStreamMessageToPrimary(
        P4RUNTIME_ROLE_SDN_CONTROLLER, response);
    return absl::OkStatus();
  };

  absl::MutexLock l(&server_state_lock_);
  // Now that all packet io ports have been discovered, start the receive thread
  // that will wait for in packets.
  return packetio_impl_->StartReceive(SendPacketInToController, use_genetlink);
}

}  // namespace p4rt_app
