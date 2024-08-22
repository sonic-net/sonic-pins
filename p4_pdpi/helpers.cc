#include "p4_pdpi/helpers.h"

#include <string>

#include "absl/status/statusor.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/built_ins.h"
#include "p4_pdpi/ir.pb.h"

namespace pdpi {

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
      if (!entity.packet_replication_engine_entry()
               .has_multicast_group_entry()) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Expected a `multicast_group_entry`, but got unexpected "
                  "packet_replication_engine_entry: "
               << entity.packet_replication_engine_entry().DebugString();
      }
      return GetMulticastGroupTableName();
    }
    default:
      return gutil::InvalidArgumentErrorBuilder()
             << "Expected a `table_entry` or "
                "`packet_replication_engine_entry`, but got unexpected entity:"
             << entity.DebugString();
  }
}

}  // namespace pdpi
