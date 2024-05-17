// Helper functions for working with the SAI PD protobuf representation.

#ifndef PINS_SAI_P4_INSTANTIATIONS_GOOGLE_SAI_PD_UTIL_H_
#define PINS_SAI_P4_INSTANTIATIONS_GOOGLE_SAI_PD_UTIL_H_

#include "absl/types/optional.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

namespace sai_pd {

// Returns a name for the entry such as "ipv4_table_entry", provided the entry
// is initialized, or `absl::nullopt` otherwise.
absl::optional<std::string> TableEntryName(const sai::TableEntry& entry);

// Returns human-readable string representation of the given update status.
std::string UpdateStatusToString(const sai::UpdateStatus& status);

}  // namespace sai_pd

#endif  // PINS_SAI_P4_INSTANTIATIONS_GOOGLE_SAI_PD_UTIL_H_
