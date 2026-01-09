#include "lib/validator/config_validator.h"

#include <map>
#include <string>
#include <utility>
#include <vector>

#include "absl/algorithm/container.h"
#include "absl/base/nullability.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "gutil/status.h"
#include "include/nlohmann/json.hpp"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/utils/json_utils.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "thinkit/switch.h"
#include "thinkit/test_environment.h"

namespace pins_test {
namespace {

// Flattens the JSON object to a map of paths to values. Helper recursive
// function.
absl::Status FlattenOpenconfigJson(
    absl::string_view path, const nlohmann::json& source,
    absl::flat_hash_map<std::string, std::string>& flattened_map) {
  switch (source.type()) {
    case nlohmann::json::value_t::object: {
      // Traverse recursively through all the members of the object type after
      // adding the path element to the path.
      for (const auto& [name, value] : source.items()) {
        const std::string member_path = absl::StrCat(path, "/", name);
        RETURN_IF_ERROR(
            FlattenOpenconfigJson(member_path, value, flattened_map));
      }
      break;
    }
    case nlohmann::json::value_t::array: {
      // Find the value of the key leaf for each element in the array to
      // construct the path element.
      for (const auto& element : source) {
        std::string member_path = std::string(path);
        std::map<std::string, std::string> key_value_map;
        for (const auto& [key_name, key_value] : element.items()) {
          // Keys will be all of the primitive values in this object.
          if (!key_value.is_primitive()) {
            continue;
          }
          key_value_map[key_name] =
              json_yang::GetSimpleJsonValueAsString(key_value);
        }
        for (const auto& [key_name, key_value] : key_value_map) {
          absl::StrAppend(&member_path, "[", key_name, "='", key_value, "']");
        }

        // Traverse each array element recursively after adding the path element
        // to the path.
        RETURN_IF_ERROR(
            FlattenOpenconfigJson(member_path, element, flattened_map));
      }
      break;
    }
    case nlohmann::json::value_t::number_integer:
    case nlohmann::json::value_t::number_unsigned:
    case nlohmann::json::value_t::number_float:
    case nlohmann::json::value_t::string:
    case nlohmann::json::value_t::boolean:
      flattened_map[path] = json_yang::GetSimpleJsonValueAsString(source);
      break;
    case nlohmann::json::value_t::null:
      // No yang path.
      break;
    default:
      return absl::InvalidArgumentError(
          absl::StrCat("Invalid json type '", source.type_name(),
                       "' for path: [", path, "]."));
  }
  return absl::OkStatus();
}

// Returns a JSON object with only the `member` specified.
nlohmann::json SingleOutMember(const nlohmann::json& json_to_isolate,
                               absl::string_view member) {
  nlohmann::json single_member;
  std::string member_key(member);
  single_member[member_key] = json_to_isolate[member_key];
  return single_member;
}

// TODO: Do this in a single gNMI call instead.
// Gets the state value for the given `oc_path` and compares it with the
// expected state value in the `config`. Dumps debug data if `test_environment`
// is provided.
absl::Status CompareConfigAndStateValues(
    absl::string_view chassis_id, gnmi::gNMI::StubInterface& gnmi_stub,
    const nlohmann::json& config, const std::string& oc_path,
    thinkit::TestEnvironment*  test_environment,
    absl::Duration timeout) {
  std::pair<std::string, std::string> state_path = absl::StrSplit(oc_path, ':');
  ASSIGN_OR_RETURN(std::string state_path_info,
                   pins_test::GetGnmiStatePathInfo(
                       &gnmi_stub, /*state_path=*/state_path.second,
                       /*resp_parse_str=*/"", timeout));
  ASSIGN_OR_RETURN(nlohmann::json state_json,
                   json_yang::ParseJson(state_path_info));

  // Compare config and state path info and ensure config is a subset of state.
  LOG(INFO) << absl::StrCat(chassis_id, " verifying path: ", oc_path);
  std::vector<std::string> error_messages;
  nlohmann::json expected_state = SingleOutMember(
      json_yang::ReplaceNamesinJsonObject(config, {{"config", "state"}}),
      oc_path);
  ASSIGN_OR_RETURN(auto flat_expected_state,
                   FlattenOpenconfigJsonToMap(expected_state));
  ASSIGN_OR_RETURN(auto flat_actual_state,
                   FlattenOpenconfigJsonToMap(state_json));
  if (json_yang::IsJsonSubset(flat_expected_state, flat_actual_state,
                              error_messages)) {
    return absl::OkStatus();
  }

  // Otherwise, there was a mismatch. Dump debug data if `test_environment` is
  // provided.
  if (test_environment != nullptr) {
    const auto current_time = absl::FormatTime(absl::Now());
    std::string config_artifact_prefix =
        absl::StrCat(chassis_id, "_", state_path.second, "_", current_time);
    RETURN_IF_ERROR(test_environment->StoreTestArtifact(
        absl::StrCat(config_artifact_prefix, "_config.json"),
        json_yang::DumpJson(config[oc_path])));
    RETURN_IF_ERROR(test_environment->StoreTestArtifact(
        absl::StrCat(config_artifact_prefix, "_state.json"),
        json_yang::DumpJson(state_json[oc_path])));
    RETURN_IF_ERROR(test_environment->StoreTestArtifact(
        absl::StrCat(config_artifact_prefix, "_error.txt"),
        absl::StrJoin(error_messages, "\n")));
  }
  return absl::InternalError(
      absl::StrCat("Config and state values are different for ", oc_path));
}

}  // namespace

absl::StatusOr<absl::flat_hash_map<std::string, std::string>>
FlattenOpenconfigJsonToMap(const nlohmann::json& source) {
  absl::flat_hash_map<std::string, std::string> flattened_map;
  RETURN_IF_ERROR(FlattenOpenconfigJson(/*path=*/"", source, flattened_map));
  return flattened_map;
}

absl::Status ConfigConverged(
    thinkit::Switch& thinkit_switch, absl::string_view expected_config,
    const absl::flat_hash_set<std::string>& paths_to_skip,
    thinkit::TestEnvironment*  test_environment,
    absl::Duration timeout) {
  ASSIGN_OR_RETURN(auto gnmi_stub, thinkit_switch.CreateGnmiStub());
  ASSIGN_OR_RETURN(nlohmann::json config,
                   json_yang::ParseJson(expected_config));

  std::vector<std::string> mismatched_paths;
  for (const auto& [config_path, _] : config.items()) {
    if (config_path.empty()) {
      continue;
    }
    auto does_config_path_contain = [&config_path](absl::string_view path) {
      return absl::StrContains(config_path, path);
    };
    if (auto skipped_path =
            absl::c_find_if(paths_to_skip, does_config_path_contain);
        skipped_path != paths_to_skip.end()) {
      LOG(INFO) << "Skipping Validation for path " << *skipped_path;
      continue;
    }

    // TODO: Do this in a single gNMI call instead.
    // Fetch state DB and compare.
    absl::Status config_state_diff_status = CompareConfigAndStateValues(
        thinkit_switch.ChassisName(), *gnmi_stub, config, config_path,
        test_environment, timeout);
    // If a mismatch is found, add it to the list of mismatched paths to log.
    if (absl::StrContains(config_state_diff_status.message(),
                          "Config and state values are different")) {
      mismatched_paths.push_back(config_path);
      continue;
    }
    // Fail for any other status error.
    RETURN_IF_ERROR(config_state_diff_status);
  }

  if (!mismatched_paths.empty()) {
    std::string error_msg = absl::StrCat("Config verification failed for: ",
                                         absl::StrJoin(mismatched_paths, "\n"));
    LOG(INFO) << error_msg;
    return absl::InternalError(error_msg);
  }
  return absl::OkStatus();
}

}  // namespace pins_test
