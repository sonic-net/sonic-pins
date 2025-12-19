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

#include <algorithm>
#include <cstdint>
#include <cstring>
#include <memory>
#include <optional>
#include <string>
#include <thread>  // NOLINT
#include <utility>
#include <vector>

#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/log/log.h"
#include "absl/log/vlog_is_on.h"
#include "absl/memory/memory.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/escaping.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_join.h"
#include "absl/strings/substitute.h"
#include "absl/synchronization/mutex.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/optional.h"
#include "boost/bimap.hpp"
#include "google/protobuf/util/json_util.h"
#include "google/protobuf/message.h"
#include "google/protobuf/util/message_differencer.h"
#include "google/rpc/code.pb.h"
#include "grpcpp/impl/codegen/status.h"
#include "grpcpp/server_context.h"
#include "grpcpp/support/status.h"
#include "grpcpp/support/sync_stream.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/io.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "include/nlohmann/json.hpp"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_constraints/backend/constraint_info.h"
#include "p4_constraints/backend/interpreter.h"
#include "p4_pdpi/entity_keys.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/translation_options.h"
#include "p4rt_app/p4runtime/entity_update.h"
#include "p4rt_app/p4runtime/ir_translation.h"
#include "p4rt_app/p4runtime/p4info_reconcile.h"
#include "p4rt_app/p4runtime/p4info_verification.h"
#include "p4rt_app/p4runtime/p4runtime_read.h"
#include "p4rt_app/p4runtime/packetio_helpers.h"
#include "p4rt_app/p4runtime/queue_translator.h"
#include "p4rt_app/p4runtime/resource_utilization.h"
#include "p4rt_app/p4runtime/sdn_controller_manager.h"
#include "p4rt_app/sonic/adapters/warm_boot_state_adapter.h"
#include "p4rt_app/sonic/app_db_acl_def_table_manager.h"
#include "p4rt_app/sonic/app_db_manager.h"
#include "p4rt_app/sonic/hashing.h"
#include "p4rt_app/sonic/packet_replication_entry_translation.h"
#include "p4rt_app/sonic/packetio_interface.h"
#include "p4rt_app/sonic/redis_connections.h"
#include "p4rt_app/sonic/response_handler.h"
#include "p4rt_app/sonic/state_verification.h"
#include "p4rt_app/sonic/vrf_entry_translation.h"
#include "p4rt_app/utils/status_utility.h"
#include "p4rt_app/utils/table_utility.h"
//TODO(PINS): Add Component/Interface Translator
/*#include "swss/component_state_helper_interface.h"
#include "swss/intf_translator.h"*/
#include "swss/json.h"
#include "swss/warm_restart.h"

namespace p4rt_app {
namespace {

using EntityMap = absl::flat_hash_map<pdpi::EntityKey, p4::v1::Entity>;
using ActionProfileCapacityMap =
    absl::flat_hash_map<std::string, ActionProfileResourceCapacity>;

// Information processed from the forwarding pipeline configuration.
struct ConfigInfo {
  pdpi::IrP4Info ir_p4info;
  p4_constraints::ConstraintInfo constraints;
  absl::btree_set<sonic::HashPacketFieldConfig> hash_packet_field_configs;
  sonic::HashParamConfigs hash_param_configs;
};

std::string GetKeyErrorMessage(pdpi::IrEntity entity,
                               const std::string& extra) {
  switch (entity.entity_case()) {
    case pdpi::IrEntity::kTableEntry:
      return absl::Substitute(
          "[P4RT App] Table entry with the given key $0 in table '$1'", extra,
          entity.table_entry().table_name());
      break;
    case pdpi::IrEntity::kPacketReplicationEngineEntry:
      return absl::Substitute(
          "[P4RT App] Packet Replication Engine entry with key of multicast "
          "group ID '$0' $1",
          entity.packet_replication_engine_entry()
              .multicast_group_entry()
              .multicast_group_id(),
          extra);
      break;
    default:
      break;
  }
  return "[P4RT App] Unknown entity type: " + entity.ShortDebugString();
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

// Compares two IrP4Info protobufs and returns true if they represent the same
// information. Differences are reported in the optional string.
bool IsEquivalent(const pdpi::IrP4Info& left, const pdpi::IrP4Info& right,
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

absl::Status VerifyEntityCacheForExistence(
    const absl::flat_hash_map<pdpi::EntityKey, p4::v1::Entity>& cache,
    const EntityUpdate& entry) {
  bool exists = false;
  auto iter = cache.find(entry.entity_key);
  if (iter != cache.end()) exists = true;

  switch (entry.update_type) {
    case p4::v1::Update::INSERT: {
      if (exists) {
        LOG(WARNING) << "Could not insert duplicate entry: "
                     << entry.entry.ShortDebugString();
        return gutil::AlreadyExistsErrorBuilder()
               << GetKeyErrorMessage(entry.entry, "already exists");
      }
      break;
    }
    case p4::v1::Update::MODIFY: {
      if (!exists) {
        LOG(WARNING) << "Could not modify missing entry: "
                     << entry.entry.ShortDebugString();
        return gutil::NotFoundErrorBuilder()
               << GetKeyErrorMessage(entry.entry, "does not exist");
      }
      break;
    }
    case p4::v1::Update::DELETE: {
      if (!exists) {
        LOG(WARNING) << "Could not delete missing entry: "
                     << entry.entry.ShortDebugString();
        return gutil::NotFoundErrorBuilder()
               << GetKeyErrorMessage(entry.entry, "does not exist");
      }
      break;
    }
    default: {
      LOG(WARNING) << "Invalid update type for "
                   << entry.entry.ShortDebugString();
      return gutil::InternalErrorBuilder()
             << "Invalid Update Type: " << entry.update_type;
    }
  }
  return absl::OkStatus();
}

// Prior to updating a table entry in App DB, confirm the table entry does not
// violate constraints.
absl::Status ValidateTableEntryConstraints(
    const p4::v1::TableEntry& entry,
    const p4_constraints::ConstraintInfo& constraint_info) {
  absl::StatusOr<std::string> reason_entry_violates_constraint =
      p4_constraints::ReasonEntryViolatesConstraint(entry, constraint_info);
  if (!reason_entry_violates_constraint.ok()) {
    // A status failure implies that the TableEntry was not formatted
    // correctly, so we could not check the constraints.
    LOG(WARNING) << "Could not verify P4 constraint: "
                 << entry.ShortDebugString();
    return reason_entry_violates_constraint.status();
  }
  if (!reason_entry_violates_constraint->empty()) {
    // A non-empty result implies the constraints were not met.
    LOG(WARNING) << "Entry does not meet P4 constraint: "
                 << *reason_entry_violates_constraint
                 << entry.ShortDebugString();
    return gutil::InvalidArgumentErrorBuilder()
           << *reason_entry_violates_constraint;
  }
  return absl::OkStatus();
}

absl::StatusOr<EntityUpdate> PiUpdateToEntityUpdate(
    const pdpi::IrP4Info& p4_info, const p4::v1::Update& pi_update,
    const std::string& role_name,
    const p4_constraints::ConstraintInfo& constraint_info,
    bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    const QueueTranslator& cpu_queue_translator,
    const QueueTranslator& front_panel_queue_translator) {
  const auto pdpi_options = pdpi::TranslationOptions{
      // When deleting we only consider the key. Actions don't matter so we
      // don't waste time trying to translate that part even if the controller
      // sent it. Also, per the spec, the control plane is not required to send
      // the full entry.
      .key_only = pi_update.type() == p4::v1::Update::DELETE,
  };

  // Translating between PI and IR, and vice versa, is non-negligable. To save
  // redundant work by doing both translations here. The IR to PI translation
  // will normalize the PI value which we can then use for the entity
  // cache. Note that the entity cache isn't updated until we know that the
  // hardware has successfully programmed the entry. We do the PI to IR
  // translation here so we can efficiently handle the cache.
  auto ir_entity =
      pdpi::PiEntityToIr(p4_info, pi_update.entity(), pdpi_options);
  if (!ir_entity.ok()) {
    LOG(ERROR) << "PDPI could not translate a PI entity to IR: "
               << pi_update.entity().ShortDebugString();
    return gutil::StatusBuilder(ir_entity.status().code())
           << "[P4RT/PDPI] " << ir_entity.status().message();
  }
  auto normalized_pi_entry =
      pdpi::IrEntityToPi(p4_info, *ir_entity, pdpi_options);
  if (!ir_entity.ok()) {
    LOG(ERROR) << "PDPI could not translate an IR entity to PI: "
               << ir_entity->ShortDebugString();
    return gutil::StatusBuilder(normalized_pi_entry.status().code())
           << "[P4RT/PDPI] " << normalized_pi_entry.status().message();
  }

  if (ir_entity->entity_case() == pdpi::IrEntity::kTableEntry) {
    // Skip the constraint check for DELETE requests because existing entries
    // already satisfy constraints, and the request may also omit actions.
    if (pi_update.type() != p4::v1::Update::DELETE) {
      // If the constraints are not met then we should just report an error
      // (i.e. do not try to handle the entry in lower layers).
      RETURN_IF_ERROR(ValidateTableEntryConstraints(
          pi_update.entity().table_entry(), constraint_info));
    }

    // Verify the table entry can be written to the table.
    absl::Status role_has_access = AllowRoleAccessToTable(
        role_name, ir_entity->table_entry().table_name(), p4_info);
    if (!role_has_access.ok()) {
      LOG(WARNING) << role_has_access
                   << " IR Table Entry: " << ir_entity->ShortDebugString();
      return role_has_access;
    }
  }

  // Apply any custom translation that are needed on the switch side to
  // account for gNMI configs (e.g. port ID translation).
  RETURN_IF_ERROR(
      UpdateIrEntityForOrchAgent(*ir_entity, p4_info, 
                                 translate_port_ids, port_translation_map,
                                 cpu_queue_translator, front_panel_queue_translator));

  ASSIGN_OR_RETURN(auto entity_key,
                   pdpi::EntityKey::MakeEntityKey(*normalized_pi_entry));

  ASSIGN_OR_RETURN(
      auto app_db_update,
      sonic::CreateAppDbUpdate(pi_update.type(), *ir_entity, p4_info));

  return EntityUpdate{
      .entry = *ir_entity,
      .update_type = pi_update.type(),
      .pi_entity = *normalized_pi_entry,
      .entity_key = entity_key,
      .app_db_update = app_db_update,
  };
}

std::vector<EntityUpdate> PiEntityUpdatesToIr(
    const p4::v1::WriteRequest& request, const pdpi::IrP4Info& p4_info,
    const EntityMap& entity_cache,
    const ActionProfileCapacityMap& capacity_by_action_profile_name,
    const p4_constraints::ConstraintInfo& constraint_info,
    bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    const QueueTranslator& cpu_queue_translator,
    const QueueTranslator& front_panel_queue_translator,
    pdpi::IrWriteResponse* response) {
  absl::flat_hash_set<pdpi::EntityKey> keys_in_request;
  bool has_duplicates = false;
  std::vector<EntityUpdate> updates;
  absl::flat_hash_map<std::string, int64_t> resources_in_batch;

  response->mutable_statuses()->Reserve(request.updates().size());
  // Fail on first error.
  for (const p4::v1::Update& pi_update : request.updates()) {
    pdpi::IrUpdateStatus& entry_status = *response->add_statuses();

    // If we cannot translate it then we should just report an error (i.e. do
    // not try to handle it in lower layers).
    absl::StatusOr<EntityUpdate> update = PiUpdateToEntityUpdate(
        p4_info, pi_update, request.role(), constraint_info, translate_port_ids,
        port_translation_map, cpu_queue_translator,
        front_panel_queue_translator);
    if (!update.ok()) {
      entry_status = GetIrUpdateStatus(update.status());
      break;
    }
    if (keys_in_request.contains(update->entity_key)) {
      // We will rewrite all responses below; no need to set entry_status here.
      has_duplicates = true;
      break;
    }
    keys_in_request.insert(update->entity_key);

    // Verify the entry exists (for MODIFY/DELETE) or not exists (for DELETE)
    // against the cache.
    if (absl::Status cache_verification =
            VerifyEntityCacheForExistence(entity_cache, *update);
        !cache_verification.ok()) {
      entry_status = GetIrUpdateStatus(cache_verification);
      break;
    }

    absl::StatusOr<TableResources> resource_change =
        VerifyCapacityAndGetTableResourceChange(p4_info, *update, entity_cache,
                                                capacity_by_action_profile_name,
                                                resources_in_batch);
    if (!resource_change.ok()) {
      entry_status = GetIrUpdateStatus(resource_change.status());
      LOG(WARNING) << resource_change.status().message();
      break;
    }

    entry_status = GetIrUpdateStatus(absl::OkStatus());
    if (resource_change->action_profile.has_value()) {
      // When accounting for the total batch resources we do not assume a MODIFY
      // or DELETE will succeed. So if a request would free resources we act as
      // if it does not (i.e. max of 0).
      resources_in_batch[resource_change->action_profile->name] +=
          resource_change->action_profile->total_weight;
    }
    update->resource_utilization_change = *resource_change;
    update->status = &*response->mutable_statuses()->rbegin();
    updates.push_back(*update);
  }

  // Abandon the whole write request if any duplicate was found in the batch.
  if (has_duplicates) {
    response->clear_statuses();
    *response->add_statuses() = GetIrUpdateStatus(
        absl::StatusCode::kInvalidArgument,
        "[P4RT App] Found duplicated key in the same batch request.");
    updates.clear();
  }

  // Mark any remaining unprocessed updates as aborted.
  const pdpi::IrUpdateStatus kAborted =
      GetIrUpdateStatus(absl::StatusCode::kAborted, "Not attempted");
  for (int i = response->statuses().size(); i < request.updates().size(); ++i) {
    *response->add_statuses() = kAborted;
  }

  return updates;
}

absl::Status UpdateCacheAndUtilizationState(
    EntityMap& entity_cache,
    ActionProfileCapacityMap& capacity_by_action_profile_name,
    const std::vector<EntityUpdate>& entity_updates,
    const pdpi::IrWriteResponse& results) {
  for (const EntityUpdate& app_db_entry : entity_updates) {
    // Lower layers should rervert any state on failure so a failing request
    // should not affect our internal state.
    if (app_db_entry.status->code() != google::rpc::Code::OK) {
      continue;
    }

    switch (app_db_entry.update_type) {
      case p4::v1::Update::INSERT:
      case p4::v1::Update::MODIFY:
        entity_cache[app_db_entry.entity_key] = app_db_entry.pi_entity;
        break;
      case p4::v1::Update::DELETE: {
        ASSIGN_OR_RETURN(
            auto key, pdpi::EntityKey::MakeEntityKey(app_db_entry.pi_entity));
        entity_cache.erase(key);
        break;
      }
      default:
        return gutil::InternalErrorBuilder()
               << "Invalid Update Type: "
               << p4::v1::Update::Type_Name(app_db_entry.update_type);
    }

    if (app_db_entry.resource_utilization_change.action_profile.has_value()) {
      const std::string& profile_name =
          app_db_entry.resource_utilization_change.action_profile->name;
      auto* utilization =
          gutil::FindOrNull(capacity_by_action_profile_name, profile_name);
      if (utilization == nullptr) {
        return gutil::InternalErrorBuilder()
               << "Could not find action profile utilization for '"
               << profile_name << "' which needs to be updated.";
      }
      utilization->current_utilization +=
          app_db_entry.resource_utilization_change.action_profile->total_weight;
    }
  }
  return absl::OkStatus();
}

absl::StatusOr<absl::flat_hash_map<pdpi::EntityKey, p4::v1::Entity>>
RebuildEntityEntryCache(
    const pdpi::IrP4Info& p4_info, bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    const QueueTranslator& cpu_queue_translator,
    const QueueTranslator& front_panel_queue_translator,
    sonic::P4rtTable& p4rt_table, sonic::VrfTable& vrf_table) {
  absl::flat_hash_map<pdpi::EntityKey, p4::v1::Entity> cache;
  // Get all P4RT keys associated with IrTableEntry objects from the AppDb.
  for (const auto& app_db_key : sonic::GetAllP4TableEntryKeys(p4rt_table)) {
    // Read a single table entry out of the AppDb
    ASSIGN_OR_RETURN(pdpi::IrTableEntry ir_table_entry,
                     sonic::ReadP4TableEntry(p4rt_table, p4_info, app_db_key));
    RETURN_IF_ERROR(TranslateTableEntry(
        TranslateTableEntryOptions{
            .direction = TranslationDirection::kForController,
            .ir_p4_info = p4_info,
            .translate_port_ids = translate_port_ids,
            .port_map = port_translation_map,
            .cpu_queue_translator = cpu_queue_translator,
            .front_panel_queue_translator = front_panel_queue_translator,
        },
        ir_table_entry));

    auto p4rt_entry = pdpi::IrTableEntryToPi(p4_info, ir_table_entry);
    if (!p4rt_entry.ok()) {
      LOG(ERROR) << "PDPI could not translate IR table entry to PI: "
                 << ir_table_entry.ShortDebugString();
      return gutil::StatusBuilder(p4rt_entry.status().code())
             << "[P4RT/PDPI] " << p4rt_entry.status().message();
    }
    (*p4rt_entry).clear_counter_data();
    (*p4rt_entry).clear_meter_counter_data();
    *cache[pdpi::EntityKey(*p4rt_entry)].mutable_table_entry() = *p4rt_entry;
  }

  // Get all VRF_TABLE entries from the AppDb.
  ASSIGN_OR_RETURN(std::vector<pdpi::IrTableEntry> vrf_entries,
                   sonic::GetAllAppDbVrfTableEntries(vrf_table));
  for (const auto& ir_table_entry : vrf_entries) {
    auto vrf_entry = pdpi::IrTableEntryToPi(p4_info, ir_table_entry);
    if (!vrf_entry.ok()) {
      LOG(ERROR) << "PDPI could not translate IR table entry to PI: "
                 << ir_table_entry.ShortDebugString();
      return gutil::StatusBuilder(vrf_entry.status().code())
             << "[P4RT/PDPI] " << vrf_entry.status().message();
    }
    *cache[pdpi::EntityKey(*vrf_entry)].mutable_table_entry() = *vrf_entry;
  }

  // Get all packet replication entries from the AppDb.
  ASSIGN_OR_RETURN(std::vector<pdpi::IrPacketReplicationEngineEntry>
                       packet_replication_entries,
                   sonic::GetAllAppDbPacketReplicationTableEntries(p4rt_table));
  for (auto& ir_entry : packet_replication_entries) {
    RETURN_IF_ERROR(TranslatePacketReplicationEntry(
        TranslateTableEntryOptions{
            .direction = TranslationDirection::kForController,
            .ir_p4_info = p4_info,
            .translate_port_ids = translate_port_ids,
            .port_map = port_translation_map,
            .cpu_queue_translator = cpu_queue_translator,
            .front_panel_queue_translator = front_panel_queue_translator,
        },
        ir_entry));
    auto pi_entry = pdpi::IrPacketReplicationEngineEntryToPi(p4_info, ir_entry);
    if (!pi_entry.ok()) {
      LOG(ERROR) << "PDPI could not translate IR packet replication to PI: "
                 << ir_entry.ShortDebugString();
      return gutil::StatusBuilder(pi_entry.status().code())
             << "[P4RT/PDPI] " << pi_entry.status().message();
    }
    p4::v1::Entity pi_entity;
    *pi_entity.mutable_packet_replication_engine_entry() = *pi_entry;
    ASSIGN_OR_RETURN(auto entity_key,
                     pdpi::EntityKey::MakeEntityKey(pi_entity));
    cache[entity_key] = pi_entity;
  }

  return cache;
}

std::vector<pdpi::IrEntity> GetIrEntitiesFromCache(
    const absl::flat_hash_map<pdpi::EntityKey, p4::v1::Entity>& entity_cache,
    const pdpi::IrP4Info& ir_p4_info, bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    const QueueTranslator& cpu_queue_translator,
    const QueueTranslator& front_panel_queue_translator,
    const p4::v1::Entity::EntityCase entity_type,
    std::vector<std::string>& failures) {
  // Translate the Entity cache into IR entries for comparison.
  std::vector<pdpi::IrEntity> ir_entries;
  int failure_count = 0;
  for (const auto& [_, pi_entity] : entity_cache) {
    if (entity_type != pi_entity.entity_case()) {
      continue;
    }
    auto ir_entity = TranslatePiEntityForOrchAgent(
        pi_entity, ir_p4_info, translate_port_ids, port_translation_map,
        cpu_queue_translator, front_panel_queue_translator, 
        /*translate_key_only=*/false);
    if (!ir_entity.ok()) {
      failure_count++;
      continue;
    }
    if (sonic::GetAppDbTableType(*ir_entity) != sonic::AppDbTableType::P4RT) {
      continue;
    }
    ir_entries.push_back(*std::move(ir_entity));
  }
  if (failure_count > 0) {
    failures.push_back(absl::StrCat("Failed to translate ", failure_count,
                                    " for entity type ", entity_type,
                                    " from the entity cache."));
  }
  return ir_entries;
}

// Verify the config and generate objects required for runtime processing.
// Returns an error if the config is empty or is otherwise invalid.
absl::StatusOr<ConfigInfo>
PreprocessConfig(const p4::v1::SetForwardingPipelineConfigRequest &request) {
  if (!request.has_config()) {
    LOG(WARNING) << "ForwardingPipelineConfig is missing the config field.";
    return gutil::InvalidArgumentErrorBuilder()
           << "ForwardingPipelineConfig is missing the config field.";
  }

  absl::Status validate_p4info = ValidateP4Info(request.config().p4info());
  if (!validate_p4info.ok()) {
    // Any failure to validate indicates an invalid P4Info.
    std::string library_prefix = LibraryPrefix(validate_p4info);
    LOG(WARNING) << library_prefix << "Failed to validate P4Info. "
                 << validate_p4info;
    return gutil::InvalidArgumentErrorBuilder()
           << library_prefix << "Failed to validate P4Info. Details: "
           << validate_p4info.message();
  }

  auto constraint_info =
      p4_constraints::P4ToConstraintInfo(request.config().p4info());
  if (!constraint_info.ok()) {
    LOG(WARNING) << "Could not get constraint info from P4Info: "
                 << constraint_info.status();
    return gutil::StatusBuilder(constraint_info.status().code())
           << "[P4 Constraint] " << constraint_info.status().message();
  }

  auto ir_p4info = pdpi::CreateIrP4Info(request.config().p4info());
  if (!ir_p4info.ok()) {
    LOG(WARNING) << "Could not convert P4Info into IrP4Info: "
                 << ir_p4info.status();
    return gutil::StatusBuilder(ir_p4info.status().code())
           << "[P4RT/PDPI] " << ir_p4info.status().message();
  }
  // Remove `@unsupported` entities so their use in requests will be rejected.
  pdpi::RemoveUnsupportedEntities(*ir_p4info);
  TranslateIrP4InfoForOrchAgent(*ir_p4info);

  auto hash_packet_field_configs =
      sonic::ExtractHashPacketFieldConfigs(*ir_p4info);
  if (!hash_packet_field_configs.ok()) {
    LOG(WARNING) << "Could not process hash packet field configs: "
                 << hash_packet_field_configs.status();
    return gutil::StatusBuilder(hash_packet_field_configs.status()).SetPrepend()
           << "[P4RT/PDPI] ";
  }

  auto hash_param_configs = sonic::ExtractHashParamConfigs(*ir_p4info);
  if (!hash_param_configs.ok()) {
    LOG(WARNING) << "Could not process hash param configs: "
                 << hash_param_configs.status();
    return gutil::StatusBuilder(hash_param_configs.status()).SetPrepend()
           << "[P4RT/PDPI] ";
  }

  return ConfigInfo{
      .ir_p4info = std::move(*ir_p4info),
      .constraints = std::move(*constraint_info),
      .hash_packet_field_configs = std::move(*hash_packet_field_configs),
      .hash_param_configs = std::move(*hash_param_configs),
  };
}

}  // namespace

std::ostream& operator<<(std::ostream& os, QueueType qt) {
  switch (qt) {
    case QueueType::kCpu:
      os << "CPU";
      break;
    case QueueType::kFrontPanel:
      os << "FRONT_PANEL";
      break;
    default:
      os << "UNKNOWN";
      break;
  }
  return os;
}

P4RuntimeImpl::P4RuntimeImpl(
    sonic::P4rtTable p4rt_table, sonic::VrfTable vrf_table,
    sonic::VlanTable vlan_table, sonic::VlanMemberTable vlan_member_table,
    sonic::HashTable hash_table, sonic::SwitchTable switch_table,
    sonic::PortTable port_table, sonic::HostStatsTable host_stats_table,
    std::unique_ptr<sonic::WarmBootStateAdapter> warm_boot_state_adapter,
    std::unique_ptr<sonic::PacketIoInterface> packetio_impl,
//TODO(PINS): To add component_state, system_state and netdev_translator.
/*  swss::ComponentStateHelperInterface& component_state,
    swss::SystemStateHelperInterface& system_state,
    swss::IntfTranslator& netdev_translator,*/
    const P4RuntimeImplOptions& p4rt_options)
    : p4rt_table_(std::move(p4rt_table)),
      vrf_table_(std::move(vrf_table)),
      vlan_table_(std::move(vlan_table)),
      vlan_member_table_(std::move(vlan_member_table)),
      hash_table_(std::move(hash_table)),
      switch_table_(std::move(switch_table)),
      port_table_(std::move(port_table)),
      host_stats_table_(std::move(host_stats_table)),
      warm_boot_state_adapter_(std::move(warm_boot_state_adapter)),
      forwarding_config_full_path_(p4rt_options.forwarding_config_full_path),
      packetio_impl_(std::move(packetio_impl)),
//TODO(PINS): To add component_state, system_state and netdev_translator.
/*      component_state_(component_state),
      system_state_(system_state),
      netdev_translator_(netdev_translator), */
      translate_port_ids_(p4rt_options.translate_port_ids),
      cpu_queue_translator_(QueueTranslator::Empty()),
      front_panel_queue_translator_(QueueTranslator::Empty()),
      is_freeze_mode_(p4rt_options.is_freeze_mode) {
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

grpc::Status P4RuntimeImpl::EnterCriticalState(const std::string& message) {
  LOG(ERROR) << "Entering critical state: " << message;
  return grpc::Status(grpc::StatusCode::INTERNAL,
                      absl::StrCat("[P4RT App going CRITICAL] ", message));
}

grpc::Status P4RuntimeImpl::GrabLockAndEnterCriticalState(
    absl::string_view message) {
  absl::MutexLock l(&server_state_lock_);
  return EnterCriticalState(std::string(message));
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
    std::vector<EntityUpdate> app_db_updates = PiEntityUpdatesToIr(
        *request, *ir_p4info_, entity_cache_, capacity_by_action_profile_name_,
        *p4_constraint_info_, translate_port_ids_, port_translation_map_,
        *cpu_queue_translator_, *front_panel_queue_translator_, rpc_response);

    // Any AppDb update failures should be appended to the `rpc_response`. If
    // UpdateAppDb fails we should go critical.
    std::vector<std::pair<sonic::AppDbUpdate, pdpi::IrUpdateStatus*>>
        updates_and_results;
    updates_and_results.reserve(app_db_updates.size());
    for (const auto& update : app_db_updates) {
      updates_and_results.push_back({update.app_db_update, update.status});
    }
    auto app_db_write_status = sonic::PerformAppDbUpdates(
        p4rt_table_, vrf_table_, updates_and_results);
    if (!app_db_write_status.ok()) {
      return EnterCriticalState(
          absl::StrCat("Unexpected error calling UpdateAppDb: ",
                       app_db_write_status.ToString()));
    }

    // We do a bit of bookkeeping, before sending our final response to the
    // controller, so that we can ensure correct fail on first semantics. Each
    // layer gets a chance at a "first" failure so it is possible to have
    // multiple failures (not including the ABORTED ones) in a batch.
    //
    // Consider the following case where we get a batch of 10 entries:
    //   1. P4RT App fails to translate entry 6 and thus marks entries
    //      7-10 as ABORTED.
    //   2. SWSS then only sees entries 1-5 for which it fails on entry 3.
    //      Therefore, marking entries 4 and 5 as ABORTED.
    //
    // In the response to the controller entry 6 would have a non-ABORTED error.
    bool found_first_failure = false;
    for (auto& rpc_error :
         *rpc_status.mutable_rpc_response()->mutable_statuses()) {
      if (rpc_error.code() == google::rpc::OK) {
        continue;
      }
      if (!found_first_failure) {
        found_first_failure = true;
        continue;
      }
      LOG_IF(WARNING, rpc_error.code() != google::rpc::ABORTED)
          << "Found an error that should be marked ABORTED. This is expected "
             "if a higher layer rejects one flow in a batch and a lower layer "
             "rejects another: "
          << rpc_error.message();
      rpc_error.set_code(google::rpc::ABORTED);
    }

    auto grpc_status = pdpi::IrWriteRpcStatusToGrpcStatus(rpc_status);
    if (!grpc_status.ok()) {
      LOG(ERROR) << "PDPI failed to translate RPC status to gRPC status: "
                 << rpc_status.ShortDebugString();
      return EnterCriticalState(grpc_status.status().ToString());
    }

    absl::Status cache_and_util_status = UpdateCacheAndUtilizationState(
        entity_cache_, capacity_by_action_profile_name_, app_db_updates,
        *rpc_response);
    if (!cache_and_util_status.ok()) {
      LOG(ERROR) << "Could not update cache and utilization for write request: "
                 << cache_and_util_status;
      return EnterCriticalState(cache_and_util_status.ToString());
    }

    absl::Duration write_execution_time = absl::Now() - write_start_time;
    write_batch_requests_ += 1;
    write_total_requests_ += app_db_updates.size();
    write_execution_time_ += write_execution_time;

    // Log a warning for any batch requests that are taking "too long" so we can
    // have an accurate time of when it happened.
    if (write_execution_time > absl::Milliseconds(500)) {
      LOG(WARNING) << absl::StreamFormat(
          "Batch request (%d entries) took >500ms: %lldms ",
          app_db_updates.size(),
          absl::ToInt64Milliseconds(write_execution_time));
      LOG_IF(WARNING, !app_db_updates.empty())
          << "First entry: " << app_db_updates.at(0).entry.ShortDebugString();
      if (VLOG_IS_ON(1)) {
        int index = 0;
        for (const auto& entry : app_db_updates) {
          LOG(WARNING) << "entry " << index++ << ": "
                       << entry.entry.ShortDebugString();
        }
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
  // Default max receive message size in GRPC is 4MB, setting the batch size to
  // 2500 assuming each response message is less than ~1600 bytes max.
  constexpr int kReadResponseBatchSize = 2500;
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

    auto responses_status = ReadAllEntitiesInBatches(
        kReadResponseBatchSize, *request, *ir_p4info_, entity_cache_,
        translate_port_ids_, port_translation_map_, *cpu_queue_translator_,
        *front_panel_queue_translator_, p4rt_table_);
    if (!responses_status.ok()) {
      LOG(WARNING) << "Read failure: " << responses_status.status();
      return grpc::Status(
          grpc::StatusCode::UNKNOWN,
          absl::StrCat("Read failure: ", responses_status.status().ToString()));
    }

    for (auto& response : responses_status.value()) {
      response_writer->Write(response);
    }

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
              packetio_counters_.packet_out_errors += 1;
              LOG(WARNING) << "Could not handle PacketOut request: "
                           << packet_out_status;
              sdn_connection->SendStreamMessageResponse(
                  GenerateErrorResponse(packet_out_status, request.packet()));
            } else {
              packetio_counters_.packet_out_sent += 1;
            }
          } else {
            // Otherwise, if it's not the primary connection trying to send a
            // message so we return a PERMISSION_DENIED error.
            packetio_counters_.packet_out_errors += 1;
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
        action_status =
            gutil::AbslStatusToGrpcStatus(PreprocessConfig(*request).status());
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

    // Only record the time for a successful commit action.
    if (request->action() !=
        p4::v1::SetForwardingPipelineConfigRequest::VERIFY) {
      host_stats_table_.state_db->set(
          "CONFIG", {{"last-configuration-timestamp",
                      absl::StrCat(absl::ToUnixNanos(absl::Now()))}});
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

// Responds with one of the following actions to port translation:
// * Add the new port translation for unknown name & ID
// * Update an existing {name, id} translation to the new ID
// * No-Op if the {name, id} pairing already exists
// * Reject if the ID is already in-use or if any input is empty ("").
//
// Consider existing port mappings: {"A", "1"}, {"B", "2"}
// The result map is:
// Port | <-----  Port ID  ------> |
// Name |   "1"  |   "2"  |   "3"  |
// =====|========|========|========|
//  "A" | No-Op  | Reject | Update |
// -----|--------|--------|--------|
//  "B" | Reject | No-Op  | Update |
// -----|--------|--------|--------|
//  "C" | Reject | Reject |  Add   |
absl::Status P4RuntimeImpl::AddPortTranslation(const std::string& port_name,
                                               const std::string& port_id,
                                               bool update_dbs) {
  absl::MutexLock l(&server_state_lock_);

  // Do not allow empty strings.
  if (port_name.empty()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Cannot add port translation {'" << port_name << "', '" << port_id
           << "'} without a port name.";
  } else if (port_id.empty()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Cannot add port translation {'" << port_name << "', '" << port_id
           << "'} without a port ID.";
  }

  // TODO: Remove DB writes when sFlow listens to another table.
  // If the Port Name/ID pair already exists then update AppDB and AppStateDB to
  // ensure sFlow gets an update.
  const auto name_iter = port_translation_map_.left.find(port_name);
  if (name_iter != port_translation_map_.left.end() &&
      name_iter->second == port_id) {
    if (update_dbs) {
      port_table_.app_db->set(port_name, {{"id", port_id}});
      port_table_.app_state_db->set(port_name, {{"id", port_id}});
    }
    return absl::OkStatus();
  }

  // If the ID exists (but isn't paired to the name), reject.
  if (const auto id_iter = port_translation_map_.right.find(port_id);
      id_iter != port_translation_map_.right.end()) {
    return gutil::AlreadyExistsErrorBuilder()
           << "Cannot add port translation {'" << port_name << "', '" << port_id
           << "'}. Port ID is already in use for translation {'"
           << id_iter->second << "', '" << port_id << "'}.";
  }
  // Insert or update the port mapping.
  LOG(INFO) << "Adding translation for {'" << port_name << "', '" << port_id
            << "'}.";
  if (name_iter != port_translation_map_.left.end()) {
    port_translation_map_.left.erase(name_iter);
  }
  port_translation_map_.insert({port_name, port_id});
  if (update_dbs) {
    port_table_.app_db->set(port_name, {{"id", port_id}});
    port_table_.app_state_db->set(port_name, {{"id", port_id}});
  }
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
    LOG(INFO) << "Removing translation for {'" << port->first << "', '"
              << port->second << "'}.";
    port_translation_map_.left.erase(port);
  }

  port_table_.app_db->del(port_name);
  port_table_.app_state_db->del(port_name);
  return absl::OkStatus();
}

std::string P4RuntimeImpl::DumpPortTranslationDebugData() {
  absl::MutexLock l(&server_state_lock_);
  std::string rv;
  for (const auto& [name, id] : port_translation_map_) {
    absl::StrAppend(&rv, name, " : ", id, "\n");
  }
  return rv;
}

std::string P4RuntimeImpl::DumpEntityCache() {
  absl::MutexLock l(&server_state_lock_);
  std::string rv;
  for (const auto& [key, entity] : entity_cache_) {
    absl::StrAppend(&rv, key, " :\n", entity.ShortDebugString(), "\n\n");
  }
  return rv;
}

absl::Status P4RuntimeImpl::DumpDebugData(const std::string& path,
                                          const std::string& log_level) {
  sonic::PacketIoCounters counters = GetPacketIoCounters();
  std::string debug_str = absl::StrFormat(
      "Timestamp: %s\n"
      "PacketIoCounters \n"
      "PacketOut sent: %d, errors %d \n"
      "PacketIn received: %d, errors %d \n",
      absl::FormatTime(absl::Now()), counters.packet_out_sent,
      counters.packet_out_errors, counters.packet_in_received,
      counters.packet_in_errors);

  RETURN_IF_ERROR(gutil::WriteFile(DumpEntityCache(), path + "/entity_cache"));

  RETURN_IF_ERROR(gutil::WriteFile(DumpPortTranslationDebugData(),
                                   path + "/port_translation_map"));

  absl::MutexLock l(&server_state_lock_);
  std::string cpu_queue_str = cpu_queue_translator_
                                  ? cpu_queue_translator_->DumpDebugData()
                                  : "unassigned";
  std::string fp_queue_str =
      front_panel_queue_translator_
          ? front_panel_queue_translator_->DumpDebugData()
          : "unassigned";

  RETURN_IF_ERROR(
      gutil::WriteFile("CPU queue translation map\n" + cpu_queue_str + "\n\n" +
                           "FRONT_PANEL queue translation map\n" + fp_queue_str,
                       path + "/queue_translation_maps"));

  return gutil::WriteFile(debug_str, path + "/packet_io_counters");
}

//absl::Status P4RuntimeImpl::VerifyState(bool update_component_state)
absl::Status P4RuntimeImpl::VerifyState() {
  absl::MutexLock l(&server_state_lock_);
  std::vector<std::string> failures = {"P4RT App State Verification failures:"};

  // Verify the P4RT_TABLE entries against the cache.
  std::vector<pdpi::IrEntity> p4rt_entities = GetIrEntitiesFromCache(
      entity_cache_, *ir_p4info_, translate_port_ids_, port_translation_map_,
      *cpu_queue_translator_, *front_panel_queue_translator_,
      p4::v1::Entity::kTableEntry, failures);
  std::vector<std::string> p4rt_table_failures =
      sonic::VerifyP4rtTableWithCacheEntities(*p4rt_table_.app_db,
                                              p4rt_entities, *ir_p4info_);
  if (!p4rt_table_failures.empty()) {
    failures.insert(failures.end(), p4rt_table_failures.begin(),
                    p4rt_table_failures.end());
  }

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

  // Verify the packet replication entries.
  std::vector<pdpi::IrEntity> packet_replication_entries =
      GetIrEntitiesFromCache(entity_cache_, *ir_p4info_, translate_port_ids_,
                             port_translation_map_, *cpu_queue_translator_,
                             *front_panel_queue_translator_,
                             p4::v1::Entity::kPacketReplicationEngineEntry,
                             failures);
  std::vector<std::string> packet_replication_table_failures =
      sonic::VerifyPacketReplicationWithCacheEntities(
          p4rt_table_, packet_replication_entries);
  if (!packet_replication_table_failures.empty()) {
    failures.insert(failures.end(), packet_replication_table_failures.begin(),
                    packet_replication_table_failures.end());
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

void P4RuntimeImpl::AssignQueueTranslator(
    const QueueType queue_type, std::unique_ptr<QueueTranslator> translator) {
  absl::MutexLock l(&server_state_lock_);

  if (queue_type == QueueType::kCpu) {
    cpu_queue_translator_ = std::move(translator);
  } else if (queue_type == QueueType::kFrontPanel) {
    front_panel_queue_translator_ = std::move(translator);
  } else {
    LOG(WARNING) << "Ignoring unknown queue type '" << queue_type << "'";
  }
}

sonic::PacketIoCounters P4RuntimeImpl::GetPacketIoCounters() {
  absl::MutexLock l(&server_state_lock_);

  return packetio_counters_;
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

  // Apply the P4Info, and configure the switch.
  grpc::Status commit_status = ReconcileAndCommitPipelineConfig(request);
  if (!commit_status.ok()) {
    return commit_status;
  }

  // Rebuild the table_entry cache.
  auto entity_cache = RebuildEntityEntryCache(
      *ir_p4info_, translate_port_ids_, port_translation_map_,
      *cpu_queue_translator_, *front_panel_queue_translator_, 
      p4rt_table_, vrf_table_);
  if (!entity_cache.ok()) {
    LOG(ERROR) << "Failed to build the table cache during COMMIT: "
               << entity_cache.status();
    return EnterCriticalState(entity_cache.status().ToString());
  /*TODO(PINS): To handle component_state_ later.
    return EnterCriticalState(entity_cache.status().ToString(),
                              component_state_); */
  }
  entity_cache_ = *std::move(entity_cache);

  return grpc::Status::OK;
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
    const p4::v1::SetForwardingPipelineConfigRequest& request,
    bool commit_to_hardware) {
  auto config_info = PreprocessConfig(request);
  if (!config_info.ok()) {
    return gutil::AbslStatusToGrpcStatus(config_info.status());
  }

  std::string ir_p4info_diff;
  if (ir_p4info_.has_value() &&
      IsEquivalent(*ir_p4info_, config_info->ir_p4info, &ir_p4info_diff)) {
    forwarding_pipeline_config_ = request.config();
    LOG(INFO)
        << "Received equivalent ForwardingPipelineConfig. Saving to disk.";
    return SavePipelineConfig(*forwarding_pipeline_config_);
  }

  if (ir_p4info_.has_value()) {
    auto transition = CalculateTransition(*ir_p4info_, config_info->ir_p4info);
    if (!transition.ok()) {
      return gutil::AbslStatusToGrpcStatus(transition.status());
    }

    // We cannot reconcile ACL configs today so if we see that the new ACL
    // config is different from the current one we just return an error.
    if (!transition->acl_tables_to_add.empty() ||
        !transition->acl_tables_to_delete.empty() ||
        !transition->acl_tables_to_modify.empty()) {
      LOG(WARNING) << "Cannot modify P4Info ACL once it has been configured.";
      return grpc::Status(
          grpc::StatusCode::UNIMPLEMENTED,
          absl::StrCat(
              "Modifying a configured forwarding pipeline is not currently "
              "supported. Please reboot the device. Configuration "
              "differences:\n",
              ir_p4info_diff));
    }

    auto capacity = GetUpdatedResourceCapacities(
        config_info->ir_p4info, capacity_by_action_profile_name_);
    if (!capacity.ok()) {
      return gutil::AbslStatusToGrpcStatus(capacity.status());
    }

    if (transition->update_switch_table) {
      LOG(INFO) << "Updating hash settings for new ForwardingPipelineConfig.";
      grpc::Status hash_transition = TransitionHashConfig(
          *transition, config_info->hash_packet_field_configs,
          config_info->hash_param_configs);
      if (!hash_transition.ok()) return hash_transition;
    }

    capacity_by_action_profile_name_ = std::move(*capacity);
  } else {
    // Configure the lower layers.
    // Apply ir_p4info to DB if we are committing to DB.
    if (commit_to_hardware) {
      // Apply a config if we don't currently have one.
      absl::Status config_result = ConfigureAppDbTables(config_info->ir_p4info);
      if (!config_result.ok()) {
        return EnterCriticalState(
            absl::StrCat("Failed to apply ForwardingPipelineConfig: ",
                         config_result.ToString()));
      }
    }
    // Store resource utilization limits for any ActionProfiles.
    for (const auto& [action_profile_name, action_profile_def] :
         config_info->ir_p4info.action_profiles_by_name()) {
      capacity_by_action_profile_name_[action_profile_name] =
          GetActionProfileResourceCapacity(action_profile_def);
      LOG(INFO) << "Adding action profile limits for '" << action_profile_name
                << "': max_weights_for_all_groups="
                << action_profile_def.action_profile().size();
    }
  }

  // Update P4RuntimeImpl's state only if we succeed.
  p4_constraint_info_ = std::move(config_info->constraints);
  ir_p4info_ = std::move(config_info->ir_p4info);
  forwarding_pipeline_config_ = request.config();

  // Save the ForwardingPipelineConfig if we are committing.
  if (commit_to_hardware) {
    LOG(INFO)
        << "ForwardingPipelineConfig was successfully applied. Saving to disk.";
    return SavePipelineConfig(*forwarding_pipeline_config_);
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
      gutil::StatusBuilder(
          gutil::SaveProtoToFile(*forwarding_config_full_path_, config))
          .SetPrepend()
          .LogError()
      << "Failed to save the ForwardingPipelineConfig to disk. ");
}

absl::Status P4RuntimeImpl::ConfigureAppDbTables(
    const pdpi::IrP4Info& ir_p4info) {
  nlohmann::json ext_tables_json = {};

  // Setup definitions for each each P4 ACL table.
  for (const pdpi::IrTableDefinition& table :
       OrderTablesBySize(ir_p4info.tables_by_name())) {
    std::string table_name = table.preamble().alias();
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
              *p4rt_table_.producer, acl_key));

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
              *p4rt_table_.producer, acl_key));

      // Any issue with the forwarding config should be sent back to the
      // controller as an INVALID_ARGUMENT.
      if (status.code() != google::rpc::OK) {
        return gutil::InvalidArgumentErrorBuilder() << status.message();
      }
    }
  }
  // Program hash settings for ECMP & LAG hashing.
  ASSIGN_OR_RETURN(auto hash_fields,
                   sonic::ExtractHashPacketFieldConfigs(ir_p4info));
  ASSIGN_OR_RETURN(auto hash_values, sonic::ExtractHashParamConfigs(ir_p4info));
  RETURN_IF_ERROR(sonic::ProgramHashFieldTable(hash_table_, hash_fields));
  RETURN_IF_ERROR(
      sonic::ProgramSwitchTable(switch_table_, hash_values, hash_fields));

  return absl::OkStatus();
}

grpc::Status P4RuntimeImpl::TransitionHashConfig(
    const P4InfoReconcileTransition& transition,
    const absl::btree_set<sonic::HashPacketFieldConfig>&
        hash_packet_field_configs,
    const sonic::HashParamConfigs& hash_param_configs) {
  if (!transition.hashing_packet_field_configs_to_delete.empty()) {
    absl::Status status = sonic::RemoveFromHashFieldTable(
        hash_table_, transition.hashing_packet_field_configs_to_delete);
    if (!status.ok()) {
      return EnterCriticalState(
          absl::StrCat("Could not update hash settings. Failed to delete "
                       "packet field configs: ",
                       status.message()));
    }
  }
  if (!transition.hashing_packet_field_configs_to_set.empty()) {
    absl::Status status =
        sonic::ProgramHashFieldTable(hash_table_, hash_packet_field_configs);
    if (!status.ok()) {
      return EnterCriticalState(
          absl::StrCat("Could not update hash settings. Failed to set new "
                       "packet field configs: ",
                       status.message()));
    }
  }
  if (transition.update_switch_table) {
    absl::Status status = sonic::ProgramSwitchTable(
        switch_table_, hash_param_configs, hash_packet_field_configs);
    if (!status.ok()) {
      return EnterCriticalState(
          absl::StrCat("Could not update hash settings. Failed to program "
                       "switch table: ",
                       status.message()));
    }
  }
  return gutil::AbslStatusToGrpcStatus(absl::OkStatus());
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
      auto port_id_or =
          TranslatePort(TranslationDirection::kForController,
                        port_translation_map_, sonic_source_port_name);
      if (!port_id_or.ok()) {
        packetio_counters_.packet_in_errors += 1;
        return gutil::StatusBuilder(port_id_or.status())
               << "Could not send PacketIn request because of bad source port "
                  "name."
               << port_id_or.status().message() << "Packet(hex): "
               << absl::BytesToHexString(payload).substr(
                      0, std::min<int>(payload.size(), 100));
      }
      source_port_id = *port_id_or;
    } else {
      source_port_id = sonic_source_port_name;
    }

    std::string target_port_id = source_port_id;
    if (!sonic_target_port_name.empty()) {
      if (translate_port_ids_) {
        auto port_id_or =
            TranslatePort(TranslationDirection::kForController,
                          port_translation_map_, sonic_target_port_name);
        if (!port_id_or.ok()) {
          packetio_counters_.packet_in_errors += 1;
          return gutil::StatusBuilder(port_id_or.status())
                 << "Could not send PacketIn request because of bad target "
                    "port name."
                 << port_id_or.status().message() << "Packet(hex): "
                 << absl::BytesToHexString(payload).substr(
                        0, std::min<int>(payload.size(), 100));
        }
        target_port_id = *port_id_or;
      } else {
        target_port_id = sonic_target_port_name;
      }
    }

    // Form the PacketIn metadata fields before writing into the
    // stream.
    auto packet_in = CreatePacketInMessage(source_port_id, target_port_id);

    p4::v1::StreamMessageResponse response;
    *response.mutable_packet() = packet_in;
    *response.mutable_packet()->mutable_payload() = payload;

    // Get the primary streamchannel and write into the stream.
    absl::Status status = controller_manager_->SendPacketInToPrimary(response);
    status.ok() ? packetio_counters_.packet_in_received += 1
                : packetio_counters_.packet_in_errors += 1;

    return status;
  };

  absl::MutexLock l(&server_state_lock_);
  if (packetio_impl_ == nullptr) {
    return absl::InvalidArgumentError("PacketIoImpl is a required object");
  }

  // Spawn the receiver thread.
  return packetio_impl_->StartReceive(SendPacketInToController, use_genetlink);
}

void P4RuntimeImpl::GrabLockAndUpdateWarmBootState(
    swss::WarmStart::WarmStartState state) {
  absl::MutexLock l(&server_state_lock_);
  UpdateWarmBootState(state);
}

void P4RuntimeImpl::UpdateWarmBootState(swss::WarmStart::WarmStartState state)
    ABSL_EXCLUSIVE_LOCKS_REQUIRED(server_state_lock_) {
  warm_boot_state_adapter_->SetWarmBootState(state);
}

swss::WarmStart::WarmStartState P4RuntimeImpl::GetWarmBootState()
    ABSL_EXCLUSIVE_LOCKS_REQUIRED(server_state_lock_) {
  return warm_boot_state_adapter_->GetWarmBootState();
}

absl::Status P4RuntimeImpl::RebuildSwStateAfterWarmboot(
    const std::vector<std::pair<std::string, std::string>>& port_ids,
    const std::vector<std::pair<std::string, std::string>>& cpu_queue_ids,
    const std::vector<std::pair<std::string, std::string>>&
        front_panel_queue_ids,
    const std::optional<int>& device_id) {
  /**
   * controller_manager_, packetio_impl_, component_state_, system_state_,
   * netdev_translator_, forwarding_config_full_path_ are restored in
   * P4RuntimeImpl contructor.
   */
  {
    absl::MutexLock l(&server_state_lock_);

    // Skip P4Info reconciliation if it wasn't present before warm reboot.
    const std::vector<std::pair<std::string, std::string>> db_attributes =
        host_stats_table_.state_db->get("CONFIG");
    if (db_attributes.empty()) {
      LOG(WARNING) << "No P4Info present before warm reboot"
                   << ", skipping P4Info reconciliation";
      return absl::OkStatus();
    }

    // TODO: Check if component_state_, system_state_, netdev_translator_
    // are initialized. Check if controller_manager_ and packetio_impl_ are
    // initialized.
    if (controller_manager_ == nullptr || packetio_impl_ == nullptr) {
      return absl::FailedPreconditionError(
          "SdnControllerManager and PacketIoInterface are not initialized.");
    }
    /**
     * Load from p4info from forwarding_config_full_path_
     * */
    if (!forwarding_config_full_path_.has_value()) {
      return absl::FailedPreconditionError(
          "p4info file path is not set during warm reboot reconciliation");
    }

    p4::v1::SetForwardingPipelineConfigRequest saved_config;
    RETURN_IF_ERROR(gutil::ReadProtoFromFile(*forwarding_config_full_path_,
                                             saved_config.mutable_config()))
        .LogError();

    /**
     * Restore forwarding_pipeline_config_, p4_constraint_info_, ir_p4info_ and
     * capacity_by_action_profile_name_ by ReconcileAndCommitPipelineConfig()
     * */
    auto reconcile_status =
        ReconcileAndCommitPipelineConfig(saved_config,
                                         /*commit_to_hardware=*/false);
    if (!reconcile_status.ok()) {
      LOG(ERROR) << "Failed to rebuild pipeline config and software cache: "
                 << reconcile_status.error_message();
      return absl::InternalError(reconcile_status.error_message());
    }
  }

  /**
   * Restore port_translation_map_ , cpu_queue_translator_,
   * front_panel_queue_translator_,
   * controller_manager_->device_id_ and packetio_impl_->port_to_socket_from
   * CONFIG DB by calling AddPortTranslation(), AssignQueueTranslator(),
   * UpdateDeviceId() and AddPacketIoPort().
   */
  for (const auto& [key, port_id] : port_ids) {
    RETURN_IF_ERROR(AddPortTranslation(key, port_id, /*update_dbs=*/false))
        .LogError();
  }
  if (!cpu_queue_ids.empty()) {
    ASSIGN_OR_RETURN(auto translator, QueueTranslator::Create(cpu_queue_ids));
    AssignQueueTranslator(QueueType::kCpu, std::move(translator));
  }
  if (!front_panel_queue_ids.empty()) {
    ASSIGN_OR_RETURN(auto translator,
                     QueueTranslator::Create(front_panel_queue_ids));
    AssignQueueTranslator(QueueType::kFrontPanel, std::move(translator));
  }

  // Ignore if no valid device ID found in configDB.
  if (device_id.has_value()) {
    RETURN_IF_ERROR(UpdateDeviceId(device_id.value())).LogError();
  }

  /**
   *  Restore the entity_cache_ cache by RebuildEntityEntryCache()
   * */
  {
    absl::MutexLock l(&server_state_lock_);
    ASSIGN_OR_RETURN(
        entity_cache_,
        RebuildEntityEntryCache(*ir_p4info_, translate_port_ids_,
                                port_translation_map_, *cpu_queue_translator_,
                                *front_panel_queue_translator_, p4rt_table_,
                                vrf_table_));
  }

  return absl::OkStatus();
}

}  // namespace p4rt_app
