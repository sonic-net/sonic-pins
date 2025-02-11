#include "p4_symbolic/test_util.h"

#include <string>
#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "gutil/io.h"
#include "gutil/proto.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"

namespace p4_symbolic {

namespace {

absl::StatusOr<std::vector<p4::v1::Entity>> ParseWriteRequestToPiEntities(
    const p4::v1::WriteRequest &write_request) {
  std::vector<p4::v1::Entity> entities;
  entities.reserve(write_request.updates_size());

  for (const auto &update : write_request.updates()) {
    // Make sure update is of type insert.
    if (update.type() != p4::v1::Update::INSERT) {
      return absl::InvalidArgumentError(
          absl::StrCat("Table entries file contains a non-insert update ",
                       update.DebugString()));
    }

    entities.push_back(update.entity());
  }

  return entities;
}

}  // namespace

absl::StatusOr<p4::v1::ForwardingPipelineConfig>
ParseToForwardingPipelineConfig(absl::string_view bmv2_json_path,
                                absl::string_view p4info_path) {
  // Read BMv2 json file into a string.
  ASSIGN_OR_RETURN(std::string bmv2_json,
                   gutil::ReadFile(std::string(bmv2_json_path)));

  // Parse p4info file into protobuf.
  p4::config::v1::P4Info p4info;
  RETURN_IF_ERROR(gutil::ReadProtoFromFile(p4info_path, &p4info));

  p4::v1::ForwardingPipelineConfig config;
  *config.mutable_p4_device_config() = std::move(bmv2_json);
  *config.mutable_p4info() = std::move(p4info);
  return config;
}

absl::StatusOr<std::vector<p4::v1::Entity>>
GetPiEntitiesFromPiUpdatesProtoTextFile(absl::string_view table_entries_path) {
  p4::v1::WriteRequest write_request;
  if (!table_entries_path.empty()) {
    RETURN_IF_ERROR(
        gutil::ReadProtoFromFile(table_entries_path, &write_request))
            .SetPrepend()
        << "While trying to parse table entry file '" << table_entries_path
        << "': ";
  }
  return ParseWriteRequestToPiEntities(write_request);
}

}  // namespace p4_symbolic
