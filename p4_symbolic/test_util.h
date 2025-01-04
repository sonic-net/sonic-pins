#ifndef PINS_P4_SYMBOLIC_TEST_UTIL_H_
#define PINS_P4_SYMBOLIC_TEST_UTIL_H_

#include <string>
#include <vector>

#include "absl/status/statusor.h"
#include "p4/v1/p4runtime.pb.h"

namespace p4_symbolic {

absl::StatusOr<p4::v1::ForwardingPipelineConfig>
ParseToForwardingPipelineConfig(const std::string &bmv2_json_path,
                                const std::string &p4info_path);

absl::StatusOr<std::vector<p4::v1::TableEntry>> ParseToPiTableEntries(
    const std::string &table_entries_path);

}  // namespace p4_symbolic

#endif  // PINS_P4_SYMBOLIC_TEST_UTIL_H_
