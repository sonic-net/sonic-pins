#include "p4_symbolic/test_util.h"

#include "gutil/io.h"
#include "gutil/proto.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"

namespace p4_symbolic {

absl::StatusOr<p4::v1::ForwardingPipelineConfig>
ParseToForwardingPipelineConfig(const std::string &bmv2_json_path,
                                const std::string &p4info_path) {
  // Read BMv2 json file into a string.
  ASSIGN_OR_RETURN(std::string bmv2_json, gutil::ReadFile(bmv2_json_path));

  // Parse p4info file into protobuf.
  p4::config::v1::P4Info p4info;
  RETURN_IF_ERROR(gutil::ReadProtoFromFile(p4info_path, &p4info));

  p4::v1::ForwardingPipelineConfig config;
  *config.mutable_p4_device_config() = std::move(bmv2_json);
  *config.mutable_p4info() = std::move(p4info);
  return config;
}

absl::StatusOr<std::vector<p4::v1::TableEntry>> ParseToPiTableEntries(
    const std::string &table_entries_path) {
  // Parse table entries.
  p4::v1::WriteRequest write_request;
  if (!table_entries_path.empty()) {
    RETURN_IF_ERROR(
        gutil::ReadProtoFromFile(table_entries_path, &write_request))
            .SetPrepend()
        << "While trying to parse table entry file '" << table_entries_path
        << "': ";
  }

  std::vector<p4::v1::TableEntry> table_entries;
  for (const auto &update : write_request.updates()) {
    // Make sure update is of type insert.
    if (update.type() != p4::v1::Update::INSERT) {
      return absl::InvalidArgumentError(
          absl::StrCat("Table entries file contains a non-insert update ",
                       update.DebugString()));
    }

    // Make sure the entity is a table entry.
    const p4::v1::Entity &entity = update.entity();
    if (entity.entity_case() != p4::v1::Entity::kTableEntry) {
      return absl::InvalidArgumentError(
          absl::StrCat("Table entries file contains a non-table entry entity ",
                       entity.DebugString()));
    }
    table_entries.push_back(std::move(entity.table_entry()));
  }

  return table_entries;
}

}  // namespace p4_symbolic
