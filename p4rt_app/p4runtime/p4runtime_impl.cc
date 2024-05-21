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

#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <vector>

#include "absl/memory/memory.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "boost/bimap.hpp"
#include "glog/logging.h"
#include "google/protobuf/descriptor.h"
#include "google/protobuf/util/json_util.h"
#include "google/protobuf/util/message_differencer.h"
#include "google/rpc/code.pb.h"
#include "grpcpp/impl/codegen/status.h"
#include "grpcpp/support/status.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "gutil/table_entry_key.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_constraints/backend/constraint_info.h"
#include "p4_constraints/backend/interpreter.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4rt_app/p4runtime/ir_translation.h"
#include "p4rt_app/p4runtime/p4info_verification.h"
#include "p4rt_app/p4runtime/packetio_helpers.h"
#include "p4rt_app/sonic/app_db_acl_def_table_manager.h"
#include "p4rt_app/sonic/app_db_manager.h"
#include "p4rt_app/sonic/packetio_interface.h"
#include "p4rt_app/sonic/redis_connections.h"
#include "p4rt_app/sonic/response_handler.h"
#include "p4rt_app/sonic/state_verification.h"
#include "p4rt_app/utils/status_utility.h"
#include "p4rt_app/utils/table_utility.h"
#include "swss/json.h"
#include <nlohmann/json.hpp>

namespace p4rt_app {
namespace {

using TableEntryMap =
    absl::flat_hash_map<gutil::TableEntryKey, p4::v1::TableEntry>;

grpc::Status EnterCriticalState(const std::string& message) {
  // TODO: report critical state somewhere an don't crash the process.
  LOG(FATAL) << "Entering critical state: " << message;
  return grpc::Status::OK;
}

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
  // The default role can access any table.
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
           << "Role '" << role_name << "' is not allowed access to table '"
           << table_name << "'.";
  }

  return absl::OkStatus();
}

sonic::AppDbTableType GetAppDbTableType(
    const pdpi::IrTableEntry& ir_table_entry) {

  // By default we assume and AppDb P4RT entry.
  return sonic::AppDbTableType::P4RT;
}

absl::StatusOr<pdpi::IrTableEntry> TranslatePiTableEntryForOrchAgent(
    const p4::v1::TableEntry& pi_table_entry, const pdpi::IrP4Info& ir_p4_info,
    bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    bool translate_key_only) {
  auto ir_table_entry =
      pdpi::PiTableEntryToIr(ir_p4_info, pi_table_entry, translate_key_only);
  if (!ir_table_entry.ok()) {
    LOG(ERROR) << "PDPI could not translate PI table entry to IR: "
               << pi_table_entry.ShortDebugString();
    return gutil::StatusBuilder(ir_table_entry.status().code())
           << "[P4RT/PDPI] " << ir_table_entry.status().message();
  }

  // TODO: Remove this when P4Info uses 64-bit IPv6 ACL matchess.
  // We don't allow overwriting of the p4info, so static is ok here.
  Convert64BitIpv6AclMatchFieldsTo128Bit(*ir_table_entry);

  RETURN_IF_ERROR(TranslateTableEntry(
      TranslateTableEntryOptions{
          .direction = TranslationDirection::kForOrchAgent,
          .ir_p4_info = ir_p4_info,
          .translate_port_ids = translate_port_ids,
          .port_map = port_translation_map},
      *ir_table_entry));
  return *ir_table_entry;
}

absl::Status AppendAclCounterData(
    p4::v1::TableEntry& pi_table_entry, const pdpi::IrP4Info& ir_p4_info,
    bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    sonic::P4rtTable& p4rt_table) {
  ASSIGN_OR_RETURN(
      pdpi::IrTableEntry ir_table_entry,
      TranslatePiTableEntryForOrchAgent(
          pi_table_entry, ir_p4_info, translate_port_ids, port_translation_map,
          /*translate_key_only=*/false));

  RETURN_IF_ERROR(sonic::AppendCounterDataForTableEntry(
      ir_table_entry, p4rt_table, ir_p4_info));
  if (ir_table_entry.has_counter_data()) {
    *pi_table_entry.mutable_counter_data() = ir_table_entry.counter_data();
  }

  return absl::OkStatus();
}

absl::Status AppendTableEntryReads(
    p4::v1::ReadResponse& response, const p4::v1::TableEntry& cached_entry,
    const std::string& role_name, const pdpi::IrP4Info& ir_p4_info,
    bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    sonic::P4rtTable& p4rt_table, sonic::VrfTable& vrf_table) {
  // Fetch the table defintion since it will inform how we process the read
  // request.
  auto table_def = ir_p4_info.tables_by_id().find(cached_entry.table_id());
  if (table_def == ir_p4_info.tables_by_id().end()) {
    return gutil::InternalErrorBuilder() << absl::StreamFormat(
               "Could not find table ID %u when checking role access. Did an "
               "IR translation fail somewhere?",
               cached_entry.table_id());
  }

  // Multiple roles can be connected to a switch so we need to ensure the
  // reader has access to the table. Otherwise, we just ignore reporting it.
  if (!role_name.empty() && table_def->second.role() != role_name) {
    VLOG(2) << absl::StreamFormat(
        "Role '%s' is not allowed access to table '%s'.", role_name,
        table_def->second.preamble().name());
    return absl::OkStatus();
  }

  // Update the response to include the table entry.
  p4::v1::TableEntry* response_entry =
      response.add_entities()->mutable_table_entry();
  *response_entry = cached_entry;

  // For ACL tables we need to check for counter/meter data, and append it as
  // needed.
  ASSIGN_OR_RETURN(table::Type table_type, GetTableType(table_def->second),
                   _ << "Could not determine table type for table '"
                     << table_def->second.preamble().name() << "'.");
  if (table_type == table::Type::kAcl) {
    RETURN_IF_ERROR(AppendAclCounterData(*response_entry, ir_p4_info,
                                         translate_port_ids,
                                         port_translation_map, p4rt_table));
  }

  return absl::OkStatus();
}

absl::StatusOr<p4::v1::ReadResponse> DoRead(
    sonic::P4rtTable& p4rt_table, sonic::VrfTable& vrf_table,
    const p4::v1::ReadRequest& request, const pdpi::IrP4Info& ir_p4_info,
    const TableEntryMap& table_entry_cache, bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map) {
  p4::v1::ReadResponse response;
  for (const auto& entity : request.entities()) {
    VLOG(1) << "Read request: " << entity.ShortDebugString();
    switch (entity.entity_case()) {
      case p4::v1::Entity::kTableEntry: {
        RETURN_IF_ERROR(SupportedTableEntryRequest(entity.table_entry()));
        for (const auto& [_, entry] : table_entry_cache) {
          RETURN_IF_ERROR(AppendTableEntryReads(
              response, entry, request.role(), ir_p4_info, translate_port_ids,
              port_translation_map, p4rt_table, vrf_table));
        }
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
  ASSIGN_OR_RETURN(pdpi::IrTableEntry ir_table_entry,
                   TranslatePiTableEntryForOrchAgent(
                       pi_table_entry, p4_info, translate_port_ids,
                       port_translation_map, translate_key_only));

  // Verify the table entry can be written to the table.
  absl::Status role_access =
      AllowRoleAccessToTable(role_name, ir_table_entry.table_name(), p4_info);
  if (!role_access.ok()) {
    LOG(WARNING) << role_access
                 << " IR Table Entry: " << ir_table_entry.ShortDebugString();
    return role_access;
  }

  return ir_table_entry;
}

sonic::AppDbUpdates PiTableEntryUpdatesToIr(
    const p4::v1::WriteRequest& request, const pdpi::IrP4Info& p4_info,
    const p4_constraints::ConstraintInfo& constraint_info,
    bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    pdpi::IrWriteResponse* response) {
  bool fail_on_first_error = false;
  sonic::AppDbUpdates ir_updates;
  for (const auto& update : request.updates()) {
    // An RPC response should be created for every updater.
    auto entry_status = response->add_statuses();

    // Just update the statuses as not attempted if any entry in the batch
    // failed earlier.
    if (fail_on_first_error) {
      *entry_status =
          GetIrUpdateStatus(absl::StatusCode::kAborted, "Not attempted");
      continue;
    }

    ++ir_updates.total_rpc_updates;

    // If the constraints are not met then we should just report an error (i.e.
    // do not try to handle the entry in lower layers).
    absl::StatusOr<std::string> reason_entry_violates_constraint =
        p4_constraints::ReasonEntryViolatesConstraint(
            update.entity().table_entry(), constraint_info);
    if (!reason_entry_violates_constraint.ok()) {
      // A status failure implies that the TableEntry was not formatted
      // correctly. So we could not check the constraints.
      LOG(WARNING) << "Could not verify P4 constraint: "
                   << update.entity().table_entry().ShortDebugString();
      *entry_status =
          GetIrUpdateStatus(reason_entry_violates_constraint.status());
      fail_on_first_error = true;
      continue;
    }
    if (!reason_entry_violates_constraint->empty()) {
      // A non-empty result implies the constraints were not met.
      LOG(WARNING) << "Entry does not meet P4 constraint: "
                   << *reason_entry_violates_constraint
                   << update.entity().table_entry().ShortDebugString();
      *entry_status = GetIrUpdateStatus(gutil::InvalidArgumentErrorBuilder()
                                        << *reason_entry_violates_constraint);
      fail_on_first_error = true;
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
      LOG(WARNING) << "Failed to translate table entry. Entry: "
                   << update.entity().table_entry().ShortDebugString();
      fail_on_first_error = true;
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

absl::Status CacheWriteResults(
    absl::flat_hash_map<gutil::TableEntryKey, p4::v1::TableEntry>& cache,
    const pdpi::IrP4Info& ir_p4finfo, const p4::v1::WriteRequest& request,
    const pdpi::IrWriteResponse& results) {
  if (request.updates_size() != results.statuses_size()) {
    return gutil::InternalErrorBuilder()
           << "The number of requests (" << request.updates_size()
           << ") does not match the number of status results ("
           << results.statuses_size() << ").";
  }

  // We only update the cache if the request passes. If it fails then the state
  // should have been restored by the lower layers, or gone critical (i.e. the
  // cache state doesn't really matter anymore).
  for (int i = 0; i < request.updates_size(); ++i) {
    if (results.statuses(i).code() != google::rpc::Code::OK) {
      continue;
    }

    const auto& update = request.updates(i);

    // Get the canonical form of the key by converting it to an IR and back.
    ASSIGN_OR_RETURN(
        auto ir_table_entry,
        pdpi::PiTableEntryToIr(ir_p4finfo, update.entity().table_entry(),
                               /*key_only=*/true));
    ASSIGN_OR_RETURN(
        auto pi_table_entry,
        pdpi::IrTableEntryToPi(ir_p4finfo, ir_table_entry, /*key_only=*/true));
    gutil::TableEntryKey key(pi_table_entry);

    switch (update.type()) {
      case p4::v1::Update::INSERT:
      case p4::v1::Update::MODIFY:
        cache[key] = update.entity().table_entry();
        break;
      case p4::v1::Update::DELETE:
        cache.erase(key);
        break;
      default:
        return gutil::InternalErrorBuilder()
               << "Invalid Update Type: "
               << p4::v1::Update::Type_Name(update.type());
    }
  }

  return absl::OkStatus();
}

}  // namespace

P4RuntimeImpl::P4RuntimeImpl(
    sonic::P4rtTable p4rt_table, sonic::VrfTable vrf_table,
    sonic::HashTable hash_table, sonic::SwitchTable switch_table,
    std::unique_ptr<sonic::PacketIoInterface> packetio_impl,
    const P4RuntimeImplOptions& p4rt_options)
    : p4rt_table_(std::move(p4rt_table)),
      vrf_table_(std::move(vrf_table)),
      hash_table_(std::move(hash_table)),
      switch_table_(std::move(switch_table)),
      forwarding_config_full_path_(p4rt_options.forwarding_config_full_path),
      packetio_impl_(std::move(packetio_impl)),
      translate_port_ids_(p4rt_options.translate_port_ids) {
  absl::optional<std::string> init_failure;

  // Start the controller manager.
  controller_manager_ = absl::make_unique<SdnControllerManager>();

  // Spawn the receiver thread to receive In packets.
  auto status_or = StartReceive(p4rt_options.use_genetlink);
  if (status_or.ok()) {
    receive_thread_ = std::move(*status_or);
  } else {
    init_failure = absl::StrCat("Failed to spawn Receive thread, error: ",
                                status_or.status().ToString());
  }
}

grpc::Status P4RuntimeImpl::Write(grpc::ServerContext* context,
                                  const p4::v1::WriteRequest* request,
                                  p4::v1::WriteResponse* response) {
  absl::MutexLock l(&server_state_lock_);

#ifdef __EXCEPTIONS
  try {
#endif
    absl::Time write_start_time = absl::Now();

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
        p4rt_table_, vrf_table_, app_db_updates, *ir_p4info_, rpc_response);
    if (!app_db_write_status.ok()) {
      return EnterCriticalState(
          absl::StrCat("Unexpected error calling UpdateAppDb: ",
                       app_db_write_status.ToString()));
    }

    auto grpc_status = pdpi::IrWriteRpcStatusToGrpcStatus(rpc_status);
    if (!grpc_status.ok()) {
      LOG(ERROR) << "PDPI failed to translate RPC status to gRPC status: "
                 << rpc_status.ShortDebugString();
      return EnterCriticalState(grpc_status.status().ToString());
    }

    absl::Status cache_status = CacheWriteResults(
        table_entry_cache_, *ir_p4info_, *request, *rpc_response);
    if (!cache_status.ok()) {
      LOG(ERROR) << "Could not caching write results: " << cache_status;
      return EnterCriticalState(cache_status.ToString());
    }

    absl::Duration write_execution_time = absl::Now() - write_start_time;
    write_batch_requests_ += 1;
    write_total_requests_ += app_db_updates.total_rpc_updates;
    write_execution_time_ += write_execution_time;

    // Log a warning for any batch requests that are taking "too long" so we can
    // have an accurate time of when it happened.
    if (write_execution_time > absl::Milliseconds(100)) {
      LOG(WARNING) << absl::StreamFormat(
          "Batch request (%d entries) took >100ms: %lldms",
          app_db_updates.total_rpc_updates,
          absl::ToInt64Milliseconds(write_execution_time));
      for (const auto& entry : app_db_updates.entries) {
        LOG(WARNING) << "entry " << entry.rpc_index << ": "
                     << entry.entry.ShortDebugString();
      }
    }

    return *grpc_status;
#ifdef __EXCEPTIONS
  } catch (const std::exception& e) {
    return EnterCriticalState(
        absl::StrCat("Exception caught in ", __func__, ", error:", e.what()));
  } catch (...) {
    return EnterCriticalState(
        absl::StrCat("Unknown exception caught in ", __func__, "."));
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
    absl::Time read_start_time = absl::Now();

    auto connection_status = controller_manager_->AllowRequest(*request);
    if (!connection_status.ok()) {
      return connection_status;
    }

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
        DoRead(p4rt_table_, vrf_table_, *request, *ir_p4info_, table_entry_cache_, translate_port_ids_,
               port_translation_map_);
    if (!response_status.ok()) {
      LOG(WARNING) << "Read failure: " << response_status.status();
      return grpc::Status(
          grpc::StatusCode::UNKNOWN,
          absl::StrCat("Read failure: ", response_status.status().ToString()));
    }

    response_writer->Write(response_status.value());

    absl::Duration read_execution_time = absl::Now() - read_start_time;
    read_total_requests_ += 1;
    read_execution_time_ += read_execution_time;

    return grpc::Status::OK;
#ifdef __EXCEPTIONS
  } catch (const std::exception& e) {
    return EnterCriticalState(
        absl::StrCat("Exception caught in ", __func__, ", error:", e.what()));
  } catch (...) {
    return EnterCriticalState(
        absl::StrCat("Unknown exception caught in ", __func__, "."));
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
    if (context == nullptr) {
      LOG(WARNING) << "StreamChannel context is a nullptr.";
      return grpc::Status(grpc::StatusCode::INVALID_ARGUMENT,
                          "Context cannot be nullptr.");
    }

    // We create a unique SDN connection object for every active connection.
    auto sdn_connection = absl::make_unique<SdnConnection>(context, stream);
    LOG(INFO) << "StreamChannel is open with peer '" << context->peer() << "'.";

    // While the connection is active we can receive and send requests.
    p4::v1::StreamMessageRequest request;
    while (stream->Read(&request)) {
      absl::MutexLock l(&server_state_lock_);

      switch (request.update_case()) {
        case p4::v1::StreamMessageRequest::kArbitration: {
          LOG(INFO) << "Received arbitration request from '" << context->peer()
                    << "': " << request.ShortDebugString();

          auto status = controller_manager_->HandleArbitrationUpdate(
              request.arbitration(), sdn_connection.get());
          if (!status.ok()) {
            LOG(WARNING) << "Failed arbitration request for '"
                         << context->peer() << "': " << status.error_message();
            controller_manager_->Disconnect(sdn_connection.get());
            return status;
          }
          break;
        }
        case p4::v1::StreamMessageRequest::kPacket: {
          if (controller_manager_
                  ->AllowMutableRequest(controller_manager_->GetDeviceId(),
                                        sdn_connection->GetRoleName(),
                                        sdn_connection->GetElectionId())
                  .ok()) {
            // If we're the primary connection we can try to handle the
            // PacketOut request.
            absl::Status packet_out_status =
                HandlePacketOutRequest(request.packet());
            if (!packet_out_status.ok()) {
              LOG(WARNING) << "Could not handle PacketOut request: "
                           << packet_out_status;
              sdn_connection->SendStreamMessageResponse(
                  GenerateErrorResponse(packet_out_status, request.packet()));
            }
          } else {
            // Otherwise, if it's not the primary connection trying to send a
            // message so we return a PERMISSION_DENIED error.
            LOG(WARNING) << "Non-primary controller '" << context->peer()
                         << "' is trying to send PacketOut requests.";
            sdn_connection->SendStreamMessageResponse(
                GenerateErrorResponse(gutil::PermissionDeniedErrorBuilder()
                                          << "Only the primary connection can "
                                             "send PacketOut requests.",
                                      request.packet()));
          }
          break;
        }
        default:
          LOG(WARNING) << "Stream Channel '" << context->peer()
                       << "' has sent a request that was unhandled: "
                       << request.ShortDebugString();
          sdn_connection->SendStreamMessageResponse(
              GenerateErrorResponse(gutil::UnimplementedErrorBuilder()
                                    << "Stream update type is not supported."));
      }
    }

    // Disconnect the controller from the list of available connections, and
    // inform any other connections about arbitration changes.
    {
      absl::MutexLock l(&server_state_lock_);
      controller_manager_->Disconnect(sdn_connection.get());
    }

    LOG(INFO) << "Closing stream to peer '" << context->peer() << "'.";
    if (context->IsCancelled()) {
      LOG(WARNING)
          << "Stream was canceled and the peer may not have been informed.";
    }
    return grpc::Status::OK;
#ifdef __EXCEPTIONS
  } catch (const std::exception& e) {
    return EnterCriticalState(
        absl::StrCat("Exception caught in ", __func__, ", error:", e.what()));
  } catch (...) {
    return EnterCriticalState(
        absl::StrCat("Unknown exception caught in ", __func__, "."));
  }
#endif
}

grpc::Status P4RuntimeImpl::SetForwardingPipelineConfig(
    grpc::ServerContext* context,
    const p4::v1::SetForwardingPipelineConfigRequest* request,
    p4::v1::SetForwardingPipelineConfigResponse* response) {
  absl::MutexLock l(&server_state_lock_);

#ifdef __EXCEPTIONS
  try {
#endif
    LOG(INFO)
        << "Received SetForwardingPipelineConfig request from election id: "
        << request->election_id().ShortDebugString();

    // Verify this connection is allowed to set the P4Info.
    auto connection_status = controller_manager_->AllowRequest(*request);
    if (!connection_status.ok()) {
      return connection_status;
    }

    // P4Runtime allows for the controller to configure the switch in multiple
    // ways. The expectations are outlined here:
    //
    // https://p4.org/p4-spec/p4runtime/main/P4Runtime-Spec.html#sec-setforwardingpipelineconfig-rpc
    grpc::Status action_status;
    VLOG(1) << "Request action: " << request->Action_Name(request->action());
    switch (request->action()) {
      case p4::v1::SetForwardingPipelineConfigRequest::VERIFY:
        action_status = VerifyPipelineConfig(*request);
        break;
      case p4::v1::SetForwardingPipelineConfigRequest::VERIFY_AND_COMMIT:
        action_status = VerifyAndCommitPipelineConfig(*request);
        break;
      case p4::v1::SetForwardingPipelineConfigRequest::COMMIT:
        action_status = CommitPipelineConfig(*request);
        break;
      case p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT: {
        action_status = ReconcileAndCommitPipelineConfig(*request);
        break;
      }
      default: {
        LOG(WARNING) << "Received SetForwardingPipelineConfigRequest with an "
                        "unsupported action: "
                     << request->Action_Name(request->action());
        return grpc::Status(
            grpc::StatusCode::UNIMPLEMENTED,
            absl::StrFormat(
                "SetForwardingPipelineConfig action '%s' is unsupported.",
                request->Action_Name(request->action())));
      }
    }

    if (action_status.error_code() == grpc::StatusCode::INTERNAL) {
      LOG(ERROR) << "Critically failed to apply ForwardingPipelineConfig: "
                 << action_status.error_message();
      return EnterCriticalState(action_status.error_message());
    } else if (!action_status.ok()) {
      LOG(WARNING) << "SetForwardingPipelineConfig failed: "
                   << action_status.error_message();
      return action_status;
    }

    LOG(INFO) << absl::StreamFormat(
        "SetForwardingPipelineConfig completed '%s' successfully.",
        p4::v1::SetForwardingPipelineConfigRequest::Action_Name(
            request->action()));

#ifdef __EXCEPTIONS
  } catch (const std::exception& e) {
    return EnterCriticalState(
        absl::StrCat("Exception caught in ", __func__, ", error:", e.what()));
  } catch (...) {
    return EnterCriticalState(
        absl::StrCat("Unknown exception caught in ", __func__, "."));
  }
#endif

  return grpc::Status::OK;
}

grpc::Status P4RuntimeImpl::GetForwardingPipelineConfig(
    grpc::ServerContext* context,
    const p4::v1::GetForwardingPipelineConfigRequest* request,
    p4::v1::GetForwardingPipelineConfigResponse* response) {
  absl::MutexLock l(&server_state_lock_);

#ifdef __EXCEPTIONS
  try {
#endif
    auto connection_status = controller_manager_->AllowRequest(*request);
    if (!connection_status.ok()) {
      return connection_status;
    }

    // If we have not set the forwarding pipeline. Then we don't return
    // anything on a get request.
    if (!forwarding_pipeline_config_.has_value()) {
      return grpc::Status(grpc::StatusCode::OK, "");
    }

    // Otherwise only return what the caller asks for.
    switch (request->response_type()) {
      case p4::v1::GetForwardingPipelineConfigRequest::ALL:
        *response->mutable_config() = *forwarding_pipeline_config_;
        break;
      case p4::v1::GetForwardingPipelineConfigRequest::COOKIE_ONLY:
        *response->mutable_config()->mutable_cookie() =
            forwarding_pipeline_config_->cookie();
        break;
      case p4::v1::GetForwardingPipelineConfigRequest::P4INFO_AND_COOKIE:
        *response->mutable_config()->mutable_p4info() =
            forwarding_pipeline_config_->p4info();
        *response->mutable_config()->mutable_cookie() =
            forwarding_pipeline_config_->cookie();
        break;
      case p4::v1::GetForwardingPipelineConfigRequest::DEVICE_CONFIG_AND_COOKIE:
        *response->mutable_config()->mutable_p4_device_config() =
            forwarding_pipeline_config_->p4_device_config();
        *response->mutable_config()->mutable_cookie() =
            forwarding_pipeline_config_->cookie();
        break;
      default:
        const std::string& response_type_name =
            p4::v1::GetForwardingPipelineConfigRequest::ResponseType_Name(
                request->response_type());
        LOG(WARNING) << "Unknown get forwarding config request type: "
                     << response_type_name;
        return grpc::Status(
            grpc::StatusCode::UNIMPLEMENTED,
            absl::StrFormat("No support provided for request type '%s'.",
                            response_type_name));
    }

#ifdef __EXCEPTIONS
  } catch (const std::exception& e) {
    return EnterCriticalState(
        absl::StrCat("Exception caught in ", __func__, ", error:", e.what()));
  } catch (...) {
    return EnterCriticalState(
        absl::StrCat("Unknown exception caught in ", __func__, "."));
  }
#endif

  return grpc::Status(grpc::StatusCode::OK, "");
}

absl::Status P4RuntimeImpl::UpdateDeviceId(uint64_t device_id) {
  absl::MutexLock l(&server_state_lock_);
  return controller_manager_->SetDeviceId(device_id);
}

absl::Status P4RuntimeImpl::AddPacketIoPort(const std::string& port_name) {
  absl::MutexLock l(&server_state_lock_);
  return packetio_impl_->AddPacketIoPort(port_name);
}

absl::Status P4RuntimeImpl::RemovePacketIoPort(const std::string& port_name) {
  absl::MutexLock l(&server_state_lock_);
  return packetio_impl_->RemovePacketIoPort(port_name);
}

absl::Status P4RuntimeImpl::AddPortTranslation(const std::string& port_name,
                                               const std::string& port_id) {
  absl::MutexLock l(&server_state_lock_);

  // Do not allow empty strings.
  if (port_name.empty()) {
    return absl::InvalidArgumentError(
        "Cannot add port translation without the port name.");
  } else if (port_id.empty()) {
    return absl::InvalidArgumentError(
        "Cannot add port translation without the port ID.");
  }

  // If the Port Name/ID pair already exists then the operation is a no-op.
  if (const auto iter = port_translation_map_.left.find(port_name);
      iter != port_translation_map_.left.end() && iter->second == port_id) {
    return absl::OkStatus();
  }

  // However, we do not accept reuse of existing values.
  if (const auto& [_, success] =
          port_translation_map_.insert({port_name, port_id});
      !success) {
    return gutil::AlreadyExistsErrorBuilder()
           << "Could not add port '" << port_name << "' with ID '" << port_id
           << "' because an entry already exists.";
  }
  LOG(INFO) << "Adding translation for '" << port_name << "' with ID '"
            << port_id << "'.";
  return absl::OkStatus();
}

absl::Status P4RuntimeImpl::RemovePortTranslation(
    const std::string& port_name) {
  absl::MutexLock l(&server_state_lock_);

  // Do not allow empty strings.
  if (port_name.empty()) {
    return absl::InvalidArgumentError(
        "Cannot remove port translation without the port name.");
  }

  if (auto port = port_translation_map_.left.find(port_name);
      port != port_translation_map_.left.end()) {
    LOG(INFO) << "Removing translation for '" << port->first << "' with ID '"
              << port->second << "'.";
    port_translation_map_.left.erase(port);
  }

  return absl::OkStatus();
}

absl::Status P4RuntimeImpl::VerifyState() {
  absl::MutexLock l(&server_state_lock_);

  std::vector<std::string> failures = {"P4RT App State Verification failures:"};

  // Verify the VRF_TABLE entries.
  std::vector<std::string> vrf_table_failures =
      sonic::VerifyAppStateDbAndAppDbEntries(*vrf_table_.app_state_db,
                                             *vrf_table_.app_db);
  if (!vrf_table_failures.empty()) {
    failures.insert(failures.end(), vrf_table_failures.begin(),
                    vrf_table_failures.end());
  }

  // Verify the HASH_TABLE entries.
  std::vector<std::string> hash_table_failures =
      sonic::VerifyAppStateDbAndAppDbEntries(*hash_table_.app_state_db,
                                             *hash_table_.app_db);
  if (!hash_table_failures.empty()) {
    failures.insert(failures.end(), hash_table_failures.begin(),
                    hash_table_failures.end());
  }

  // Verify the SWITCH_TABLE entries.
  std::vector<std::string> switch_table_failures =
      sonic::VerifyAppStateDbAndAppDbEntries(*switch_table_.app_state_db,
                                             *switch_table_.app_db);
  if (!switch_table_failures.empty()) {
    failures.insert(failures.end(), switch_table_failures.begin(),
                    switch_table_failures.end());
  }

  if (failures.size() > 1) {
    return gutil::UnknownErrorBuilder() << absl::StrJoin(failures, "\n  ");
  }
  return absl::OkStatus();
}

absl::StatusOr<FlowProgrammingStatistics>
P4RuntimeImpl::GetFlowProgrammingStatistics() {
  absl::MutexLock l(&server_state_lock_);

  std::optional<absl::Duration> max_write_time =
      write_execution_time_.ReadMaxValue();
  FlowProgrammingStatistics stats{
      .write_batch_count = write_batch_requests_.ReadDataAndReset(),
      .write_requests_count = write_total_requests_.ReadDataAndReset(),
      .write_time = write_execution_time_.ReadDataAndReset(),
      .read_request_count = read_total_requests_.ReadDataAndReset(),
      .read_time = read_execution_time_.ReadDataAndReset(),
  };

  if (max_write_time.has_value()) {
    stats.max_write_time = *max_write_time;
  }
  return stats;
}

absl::Status P4RuntimeImpl::HandlePacketOutRequest(
    const p4::v1::PacketOut& packet_out) {
  if (!ir_p4info_.has_value()) {
    return gutil::FailedPreconditionErrorBuilder()
           << "Switch has not configured the forwarding pipeline.";
  }
  return SendPacketOut(*ir_p4info_, translate_port_ids_, port_translation_map_,
                       packetio_impl_.get(), packet_out);
}

grpc::Status P4RuntimeImpl::VerifyPipelineConfig(
    const p4::v1::SetForwardingPipelineConfigRequest& request) const {
  // In all cases where we need to verify a config the spec requires a config to
  // be set.
  if (!request.has_config()) {
    LOG(WARNING) << "ForwardingPipelineConfig is missing the config field.";
    return grpc::Status(
        grpc::StatusCode::INVALID_ARGUMENT,
        "ForwardingPipelineConfig is missing the config field.");
  }

  absl::Status validate_p4info = ValidateP4Info(request.config().p4info());
  if (!validate_p4info.ok()) {
    // Any failure to validate indicates an invalid P4Info.
    std::string library_prefix = LibraryPrefix(validate_p4info);
    LOG(WARNING) << library_prefix << "Failed to validate P4Info. "
                 << validate_p4info;
    return gutil::AbslStatusToGrpcStatus(
        gutil::StatusBuilder(absl::StatusCode::kInvalidArgument)
        << library_prefix
        << "Failed to validate P4Info. Details: " << validate_p4info.message());
  }
  return grpc::Status::OK;
}

grpc::Status P4RuntimeImpl::VerifyAndCommitPipelineConfig(
    const p4::v1::SetForwardingPipelineConfigRequest& request) {
  // Today we do not clear any forwarding state so if we detect any we return an
  // UNIMPLEMENTED error.
  if (forwarding_pipeline_config_.has_value()) {
    return grpc::Status(
        grpc::StatusCode::UNIMPLEMENTED,
        "Clearing existing forwarding state is not supported. Try using "
        "RECONCILE_AND_COMMIT instead.");
  }

  // Since we cannot have any state today we can use the same code path from
  // RECONCILE_AND_COMMIT to apply the forwarding config.
  return ReconcileAndCommitPipelineConfig(request);
}

grpc::Status P4RuntimeImpl::CommitPipelineConfig(
    const p4::v1::SetForwardingPipelineConfigRequest& request) {
  if (request.has_config()) {
    return grpc::Status(grpc::StatusCode::INVALID_ARGUMENT,
                        "The config field cannot be set when using the COMMIT "
                        "action. It can only be loaded from from a previously "
                        "saved file (e.g. VERIFY_AND_SAVE).");
  }

  if (!forwarding_config_full_path_.has_value()) {
    return grpc::Status(grpc::StatusCode::FAILED_PRECONDITION,
                        "P4RT App has not been configured to save forwarding "
                        "configs. The COMMIT action cannot be used.");
  }

  p4::v1::SetForwardingPipelineConfigRequest saved_config;
  absl::Status read_status = gutil::ReadProtoFromFile(
      *forwarding_config_full_path_, saved_config.mutable_config());
  if (!read_status.ok()) {
    LOG(WARNING) << "Could not read saved config: " << read_status;
    return gutil::AbslStatusToGrpcStatus(read_status);
  }

  return VerifyAndCommitPipelineConfig(saved_config);
}

grpc::Status P4RuntimeImpl::ReconcileAndCommitPipelineConfig(
    const p4::v1::SetForwardingPipelineConfigRequest& request) {
  grpc::Status verified = VerifyPipelineConfig(request);
  if (!verified.ok()) return verified;

  // We cannot reconcile any config today so if we see that the new forwarding
  // config is different from the current one we just return an error.
  std::string diff_report;
  if (forwarding_pipeline_config_.has_value() &&
      !P4InfoEquals(forwarding_pipeline_config_->p4info(),
                    request.config().p4info(), &diff_report)) {
    LOG(WARNING) << "Cannot modify P4Info once it has been configured.";
    return grpc::Status(
        grpc::StatusCode::UNIMPLEMENTED,
        absl::StrCat(
            "Modifying a configured forwarding pipeline is not currently "
            "supported. Please reboot the device. Configuration "
            "differences:\n",
            diff_report));
  }

  // If the IrP4Info hasn't been set then we need to configure the lower layers.
  if (!ir_p4info_.has_value()) {
    // Collect any P4RT constraints from the P4Info.
    auto constraint_info =
        p4_constraints::P4ToConstraintInfo(request.config().p4info());
    if (!constraint_info.ok()) {
      LOG(WARNING) << "Could not get constraint info from P4Info: "
                   << constraint_info.status();
      return gutil::AbslStatusToGrpcStatus(
          absl::Status(constraint_info.status().code(),
                       absl::StrCat("[P4 Constraint] ",
                                    constraint_info.status().message())));
    }

    // Convert the P4Info into an IrP4Info.
    auto ir_p4info = pdpi::CreateIrP4Info(request.config().p4info());
    if (!ir_p4info.ok()) {
      LOG(WARNING) << "Could not convert P4Info into IrP4Info: "
                   << ir_p4info.status();
      return gutil::AbslStatusToGrpcStatus(absl::Status(
          ir_p4info.status().code(),
          absl::StrCat("[P4RT/PDPI] ", ir_p4info.status().message())));
    }
    TranslateIrP4InfoForOrchAgent(*ir_p4info);

    // Apply a config if we don't currently have one.
    absl::Status config_result = ConfigureAppDbTables(*ir_p4info);
    if (!config_result.ok()) {
      LOG(ERROR) << "Failed to apply ForwardingPipelineConfig: "
                 << config_result;
      // TODO: cleanup P4RT table definitions instead of going
      // critical.
      return grpc::Status(grpc::StatusCode::INTERNAL, config_result.ToString());
    }

    // Update P4RuntimeImpl's state only if we succeed.
    p4_constraint_info_ = *std::move(constraint_info);
    ir_p4info_ = *std::move(ir_p4info);
  }

  // The ForwardingPipelineConfig is still updated incase the cookie value has
  // been changed.
  forwarding_pipeline_config_ = request.config();

  grpc::Status saved = SavePipelineConfig(*forwarding_pipeline_config_);
  if (!saved.ok()) {
    LOG(ERROR) << "Successfully applied, but could not save the "
               << "ForwardingPipelineConfig: " << saved.error_message();
    return saved;
  }

  return grpc::Status::OK;
}

grpc::Status P4RuntimeImpl::SavePipelineConfig(
    const p4::v1::ForwardingPipelineConfig& config) const {
  // If the save path is not set then there is nothing to do.
  if (!forwarding_config_full_path_.has_value()) {
    LOG(WARNING) << "Cannot save ForwardingPipelineConfig because the file "
                    "path was not set.";
    return grpc::Status::OK;
  }
  return gutil::AbslStatusToGrpcStatus(
      gutil::SaveProtoToFile(*forwarding_config_full_path_, config));
}

absl::Status P4RuntimeImpl::ConfigureAppDbTables(
    const pdpi::IrP4Info& ir_p4info) {
  nlohmann::json ext_tables_json = {};

  // Setup definitions for each each P4 ACL table.
  for (const auto& pair : ir_p4info.tables_by_name()) {
    std::string table_name = pair.first;
    pdpi::IrTableDefinition table = pair.second;
    ASSIGN_OR_RETURN(table::Type table_type, GetTableType(table),
                     _ << "Failed to configure table " << table_name << ".");

    // Add ACL table definition to AppDb (if applicable).
    if (table_type == table::Type::kAcl) {
      LOG(INFO) << "Configuring ACL table: " << table_name;
      ASSIGN_OR_RETURN(std::string acl_key,
                       sonic::InsertAclTableDefinition(p4rt_table_, table),
                       _ << "Failed to add ACL table definition '" << table_name
                         << "' to AppDb.");

      // Wait for OA to confirm it can realize the table updates.
      ASSIGN_OR_RETURN(
          pdpi::IrUpdateStatus status,
          sonic::GetAndProcessResponseNotificationWithoutRevertingState(
              *p4rt_table_.notification_consumer, acl_key));

      // Any issue with the forwarding config should be sent back to the
      // controller as an INVALID_ARGUMENT.
      if (status.code() != google::rpc::OK) {
        return gutil::InvalidArgumentErrorBuilder() << status.message();
      }
    }
    if (!ext_tables_json.dump().empty()) {
       // Publish all tables at once and get one success/failure response for them
      ASSIGN_OR_RETURN(
            std::string acl_key,
            sonic::PublishExtTablesDefinitionToAppDb(ext_tables_json, (uint64_t)0,
                       p4rt_table_),
            _ << "Could not publish Table Definition Set to APPDB");

      ASSIGN_OR_RETURN(
            pdpi::IrUpdateStatus status,
            sonic::GetAndProcessResponseNotificationWithoutRevertingState(
                 *p4rt_table_.notification_consumer, acl_key));

      // Any issue with the forwarding config should be sent back to the
      // controller as an INVALID_ARGUMENT.
      if (status.code() != google::rpc::OK) {
        return gutil::InvalidArgumentErrorBuilder() << status.message();
      }
    }
  }
  return absl::OkStatus();
}

absl::StatusOr<std::thread> P4RuntimeImpl::StartReceive(
    const bool use_genetlink) {
  // Define the lambda function for the callback to be executed for every
  // receive packet.
  auto SendPacketInToController =
      [this](const std::string& netdev_source_port_name,
             const std::string& netdev_target_port_name,
             const std::string& payload) -> absl::Status {
    absl::MutexLock l(&server_state_lock_);

    // The callback will have Linux netdev interfaces. So we first need to
    // convert it into a SONiC port name then if needed into the controller port
    // number.
    std::string sonic_source_port_name = netdev_source_port_name;
    std::string sonic_target_port_name = netdev_target_port_name;

    std::string source_port_id;
    if (translate_port_ids_) {
      ASSIGN_OR_RETURN(
          source_port_id,
          TranslatePort(TranslationDirection::kForController,
                        port_translation_map_, sonic_source_port_name),
          _ << "Could not send PacketIn request because of bad source port "
               "name.");
    } else {
      source_port_id = sonic_source_port_name;
    }

    // TODO: Until string port names are supported, re-assign empty
    // target egress port names to match the ingress port.
    std::string target_port_id = source_port_id;
    if (!sonic_target_port_name.empty()) {
      if (translate_port_ids_) {
        ASSIGN_OR_RETURN(
            target_port_id,
            TranslatePort(TranslationDirection::kForController,
                          port_translation_map_, sonic_target_port_name),
            _ << "Could not send PacketIn request because of bad target port "
                 "name.");
      } else {
        target_port_id = sonic_target_port_name;
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
    return controller_manager_->SendPacketInToPrimary(response);
  };

  absl::MutexLock l(&server_state_lock_);
  if (packetio_impl_ == nullptr) {
    return absl::InvalidArgumentError("PacketIoImpl is a required object");
  }

  // Spawn the receiver thread.
  return packetio_impl_->StartReceive(SendPacketInToController, use_genetlink);
}
}  // namespace p4rt_app
