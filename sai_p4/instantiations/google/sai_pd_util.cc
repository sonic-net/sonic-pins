#include "sai_p4/instantiations/google/sai_pd_util.h"

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/types/optional.h"

namespace sai_pd {

absl::optional<std::string> TableEntryName(const sai::TableEntry& entry) {
  const google::protobuf::OneofDescriptor* oneof =
      entry.GetDescriptor()->FindOneofByName("entry");
  const google::protobuf::FieldDescriptor* field =
      entry.GetReflection()->GetOneofFieldDescriptor(entry, oneof);
  if (field == nullptr) return absl::nullopt;
  return field->name();
}

std::string UpdateStatusToString(const sai::UpdateStatus& status) {
  return absl::StrCat(
      absl::StatusCodeToString(static_cast<absl::StatusCode>(status.code())),
      status.message().empty() ? "" : absl::StrCat(": ", status.message()));
}

}  // namespace sai_pd
