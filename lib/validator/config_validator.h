#ifndef PINS_LIB_VALIDATOR_CONFIG_VALIDATOR_H_
#define PINS_LIB_VALIDATOR_CONFIG_VALIDATOR_H_

#include <string>

#include "absl/base/nullability.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "include/nlohmann/json.hpp"
#include "thinkit/switch.h"
#include "thinkit/test_environment.h"

namespace pins_test {

// Flattens the JSON object to a map of paths to values.
absl::StatusOr<absl::flat_hash_map<std::string, std::string>>
FlattenOpenconfigJsonToMap(const nlohmann::json& source);

// Checks if the switch state has converged to the expected config, ignoring
// `paths_to_skip`. Optional test environment will be used to dump any diffs.
absl::Status ConfigConverged(
    thinkit::Switch& thinkit_switch, absl::string_view expected_config,
    const absl::flat_hash_set<std::string>& paths_to_skip = {},
    thinkit::TestEnvironment*  test_environment = nullptr,
    absl::Duration timeout = absl::Seconds(60));

}  // namespace pins_test

#endif  // PINS_LIB_VALIDATOR_CONFIG_VALIDATOR_H_
