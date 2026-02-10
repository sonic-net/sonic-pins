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

#include "p4_infra/p4_pdpi/names.h"

#include <string>

#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/built_ins.h"
#include "p4_infra/p4_pdpi/ir.pb.h"

namespace pdpi {

// This function could be implemented by calling the second overload below.
// For now we stick to this more complicated, but faster implementation since
// it has better performance and the function is used by some performance
// sensitive code.
absl::StatusOr<std::string> EntityToTableName(const pdpi::IrP4Info& info,
                                              const p4::v1::Entity& entity) {
  switch (entity.entity_case()) {
    case p4::v1::Entity::kTableEntry: {
      ASSIGN_OR_RETURN(const IrTableDefinition table,
                       gutil::FindOrStatus(info.tables_by_id(),
                                           entity.table_entry().table_id()));
      return table.preamble().alias();
    }
    case p4::v1::Entity::kPacketReplicationEngineEntry: {
      if (entity.packet_replication_engine_entry()
              .has_multicast_group_entry()) {
        return GetMulticastGroupTableName();
      }
      if (entity.packet_replication_engine_entry().has_clone_session_entry()) {
        return GetCloneSessionTableName();
      }
      return gutil::InvalidArgumentErrorBuilder()
             << "Expected a `multicast_group_entry` or `clone_session_entry`, "
                "but got unexpected packet_replication_engine_entry: "
             << entity.packet_replication_engine_entry().DebugString();
    }
    default:
      return gutil::InvalidArgumentErrorBuilder()
             << "Expected a `table_entry` or "
                "`packet_replication_engine_entry`, but got unexpected entity:"
             << entity.DebugString();
  }
}

absl::StatusOr<std::string> EntityToTableName(const IrEntity& entity) {
  switch (entity.entity_case()) {
    case IrEntity::kTableEntry: {
      return entity.table_entry().table_name();
    }
    case IrEntity::kPacketReplicationEngineEntry: {
      switch (entity.packet_replication_engine_entry().type_case()) {
        case IrPacketReplicationEngineEntry::kMulticastGroupEntry:
          return GetMulticastGroupTableName();
        case IrPacketReplicationEngineEntry::kCloneSessionEntry:
          return GetCloneSessionTableName();
        case IrPacketReplicationEngineEntry::TYPE_NOT_SET:
          break;
      }
      break;
    }
    case IrEntity::ENTITY_NOT_SET:
      break;
  }

  return gutil::InvalidArgumentErrorBuilder()
         << "unsupported entity: " << absl::StrCat(entity);
}

}  // namespace pdpi
