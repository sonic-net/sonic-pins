#include "sai_p4/instantiations/google/sai_pd_util.h"

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/strip.h"
#include "absl/types/optional.h"

namespace sai_pd {

absl::optional<std::string> TableEntryName(const sai::TableEntry& entry) {
  const google::protobuf::OneofDescriptor* oneof =
      entry.GetDescriptor()->FindOneofByName("entry");
  const google::protobuf::FieldDescriptor* field =
      entry.GetReflection()->GetOneofFieldDescriptor(entry, oneof);
  if (field == nullptr) return absl::nullopt;
  return std::string(field->name());
}

absl::optional<std::string> TableName(const sai::TableEntry& entry) {
  auto table_entry_name = TableEntryName(entry);
  if (!table_entry_name.has_value()) {
    return absl::nullopt;
  }
  return std::string(absl::StripSuffix(table_entry_name.value(), "_entry"));
}

std::string UpdateStatusToString(const sai::UpdateStatus& status) {
  return absl::StrCat(
      absl::StatusCodeToString(static_cast<absl::StatusCode>(status.code())),
      status.message().empty() ? "" : absl::StrCat(": ", status.message()));
}

}  // namespace sai_pd
