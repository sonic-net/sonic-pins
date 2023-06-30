#ifndef PINS_P4_SYMBOLIC_TEST_UTIL_H_
#define PINS_P4_SYMBOLIC_TEST_UTIL_H_

#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "p4/v1/p4runtime.pb.h"

namespace p4_symbolic {

absl::StatusOr<p4::v1::ForwardingPipelineConfig>
ParseToForwardingPipelineConfig(absl::string_view bmv2_json_path,
                                absl::string_view p4info_path);

absl::StatusOr<std::vector<p4::v1::TableEntry>>
GetPiTableEntriesFromPiUpdatesProtoTextFile(
    absl::string_view table_entries_path);

}  // namespace p4_symbolic

#endif  // PINS_P4_SYMBOLIC_TEST_UTIL_H_
