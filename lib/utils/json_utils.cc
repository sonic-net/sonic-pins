// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "lib/utils/json_utils.h"

#include <string>
#include <vector>

#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "gutil/status.h"
#include "include/nlohmann/json.hpp"

namespace json_yang {

namespace {

using StringSetMap =
    absl::flat_hash_map<std::string, absl::btree_set<std::string>>;
using StringMap = absl::flat_hash_map<std::string, std::string>;

// Helper function to perform flattening recursively.
//
// A list data node in YANG is represented as an array in JSON. The YANG model
// is required to define one or more leaf data nodes as keys that uniquely
// identify the elements in the list. (see rfc7950#section-7.8.2).
//
//  - path contains the currently traversed JSON value and includes the
//    key/value pairs for array elements. This is used in the output map.
//    e. g. /outer_element/array_container/array_element[key='value']/leaf
//  - path_without_keys contains the currently traversed JSON value without
//    key/value pairs for array elements. This is used to look up key leaves.
//    e. g. /outer_element/array_container/array_element/leaf
//  - yang_path_key_name_map contains a map of yang list paths to the name of
//    the leaf that's defined as the key for that list (multiple keys are
//    supported).
//  - unknown_key_paths: If the key for a list is absent in
//  'yang_path_key_name_map', then such paths are recorded in
//  'unknown_key_paths'
absl::Status FlattenJson(const absl::string_view path,
                         const absl::string_view path_without_keys,
                         const nlohmann::json& source,
                         const StringSetMap& yang_path_key_name_map,
                         StringMap& flattened_map,
                         absl::btree_set<std::string>& unknown_key_paths) {
  switch (source.type()) {
    case nlohmann::json::value_t::object: {
      // Traverse recursively through all the members of the object type after
      // adding the path element to the path.
      for (const auto& [name, value] : source.items()) {
        const std::string member_path = absl::StrCat(path, "/", name);
        const std::string member_path_without_keys =
            absl::StrCat(path_without_keys, "/", name);
        RETURN_IF_ERROR(FlattenJson(member_path, member_path_without_keys,
                                    value, yang_path_key_name_map,
                                    flattened_map, unknown_key_paths));
      }
      break;
    }
    case nlohmann::json::value_t::array: {
      // Find the name of the leaf that is considered the key for the elements
      // in the array.
      auto key_name_iter = yang_path_key_name_map.find(path_without_keys);
      if (key_name_iter == yang_path_key_name_map.end()) {
        unknown_key_paths.insert(std::string(path_without_keys));
        return absl::OkStatus();
      }
      const absl::btree_set<std::string>& key_names = key_name_iter->second;

      // Find the value of the key leaf for each element in the array to
      // construct the path element.
      for (int i = 0; i < source.size(); ++i) {
        std::string member_path = std::string(path);
        std::string key_value;
        if (key_names.empty()) {
          switch (source[i].type()) {
            case nlohmann::json::value_t::number_integer:
            case nlohmann::json::value_t::number_unsigned:
            case nlohmann::json::value_t::number_float:
            case nlohmann::json::value_t::string:
            case nlohmann::json::value_t::boolean:
              key_value = GetSimpleJsonValueAsString(source[i]);
              break;
            default:
              return absl::InvalidArgumentError(absl::StrCat(
                  "Invalid type '", source[i].type_name(),
                  "' for array element (leaf list) ", i, " under path [", path,
                  "]. Expected: integer, unsigned, float, string, bool."));
              break;
          }
          member_path = absl::StrCat(path, "['", key_value, "']");
        }
        for (const auto& key_name : key_names) {
          if (!source[i].contains(key_name)) {
            return absl::InvalidArgumentError(absl::StrCat(
                "No key leaf '", key_name, "' found for array element ", i,
                " under path: [", path, "]."));
          }

          switch (source[i][key_name].type()) {
            case nlohmann::json::value_t::number_integer:
            case nlohmann::json::value_t::number_unsigned:
            case nlohmann::json::value_t::number_float:
            case nlohmann::json::value_t::string:
            case nlohmann::json::value_t::boolean:
              key_value = GetSimpleJsonValueAsString(source[i][key_name]);
              break;
            default:
              // This is an error case. The key leaf must be a simple value.
              return absl::InvalidArgumentError(absl::StrCat(
                  "Invalid type '", source[i][key_name].type_name(),
                  "' for key leaf '", key_name, "' for array element ", i,
                  " under path [", path,
                  "]. Expected: integer, unsigned, float, string, bool."));
              break;
          }
          absl::StrAppend(&member_path, "[", key_name, "='", key_value, "']");
        }

        // Traverse each array element recursively after adding the path element
        // to the path.
        RETURN_IF_ERROR(FlattenJson(member_path, path_without_keys, source[i],
                                    yang_path_key_name_map, flattened_map,
                                    unknown_key_paths));
      }
      break;
    }
    case nlohmann::json::value_t::number_integer:
    case nlohmann::json::value_t::number_unsigned:
    case nlohmann::json::value_t::number_float:
    case nlohmann::json::value_t::string:
    case nlohmann::json::value_t::boolean:
      flattened_map[path] = GetSimpleJsonValueAsString(source);
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

}  // namespace

absl::StatusOr<nlohmann::json> ParseJson(absl::string_view json_str) {
  // Return a null json if the input is an empty string.
  if (json_str.empty()) return nlohmann::json(nullptr);

  // TODO: Enable exception after we find out why test crashes instead of
  // catching the error.
  nlohmann::json json =
      nlohmann::json::parse(std::string(json_str), /*cb =*/nullptr,
                            /*allow_exceptions =*/false);
  if (json.is_discarded()) {
    return absl::InvalidArgumentError(
        absl::StrCat("json parse error. Json value is:\n", json_str));
  }
  return json;
}

std::string DumpJson(const nlohmann::json& value) {
  // Return an empty string if the input value is null.
  if (value.is_null()) return "";

  return value.dump(
      /*indent =*/2, /*indent_char =*/' ', /*ensure_ascii =*/false,
      /*error_handler =*/nlohmann::json::error_handler_t::replace);
}

std::string FormatJsonBestEffort(absl::string_view raw_json) {
  using Json = nlohmann::json;
  Json json = Json::parse(raw_json, /*cb=*/nullptr, /*allow_exceptions=*/false);
  return json.is_discarded() ? std::string(raw_json) : DumpJson(json);
}

nlohmann::json ReplaceNamesinJsonObject(
    const nlohmann::json& source, const StringMap& old_name_to_new_name_map) {
  switch (source.type()) {
    case nlohmann::json::value_t::object: {
      nlohmann::json target(nlohmann::json::value_t::object);
      for (const auto& [name, value] : source.items()) {
        // Replace the path element if necessary.
        auto name_iter = old_name_to_new_name_map.find(name);
        const std::string new_name = name_iter == old_name_to_new_name_map.end()
                                         ? name
                                         : name_iter->second;
        // Traverse through all the members recursively.
        target[new_name] =
            ReplaceNamesinJsonObject(value, old_name_to_new_name_map);
      }
      return target;
    }
    case nlohmann::json::value_t::array: {
      nlohmann::json target(nlohmann::json::value_t::array);
      for (int i = 0; i < source.size(); ++i) {
        // Traverse through all array elements recursively.
        target.push_back(
            ReplaceNamesinJsonObject(source[i], old_name_to_new_name_map));
      }
      return target;
    }
    default:
      // Leaf value or null. Nothing to replace.
      return source;
  }
}

void ReplaceNamesinJsonObject(const StringMap& old_name_to_new_name_map,
                              nlohmann::json& root) {
  switch (root.type()) {
    case nlohmann::json::value_t::object: {
      for (const auto& [old_name, new_name] : old_name_to_new_name_map) {
        if (!root.contains(old_name)) continue;

        // Create an empty JSON with the new name (erases any existing value).
        root[new_name] = nlohmann::json(nlohmann::json::value_t::null);
        // Swap with JSON values between the old and new names.
        root[old_name].swap(root[new_name]);
        // Erase the old name.
        root.erase(old_name);
      }
      for (auto& [_, value] : root.items()) {
        // Traverse through all the members recursively.
        ReplaceNamesinJsonObject(old_name_to_new_name_map, value);
      }
      break;
    }
    case nlohmann::json::value_t::array: {
      nlohmann::json target(nlohmann::json::value_t::array);
      for (int i = 0; i < root.size(); ++i) {
        // Traverse through all array elements recursively.
        ReplaceNamesinJsonObject(old_name_to_new_name_map, root[i]);
      }
      break;
    }
    default:
      // Primitive value or null. Nothing to replace.
      break;
  }
}

absl::StatusOr<StringMap> FlattenJsonToMap(
    const nlohmann::json& root, const StringSetMap& yang_path_key_name_map,
    bool ignore_unknown_key_paths) {
  StringMap flattened_json;
  absl::btree_set<std::string> unknown_key_paths;
  RETURN_IF_ERROR(FlattenJson("", "", root, yang_path_key_name_map,
                              flattened_json, unknown_key_paths));
  if (!unknown_key_paths.empty() && !ignore_unknown_key_paths) {
    return absl::InvalidArgumentError(
        absl::StrCat("No key found in the map for the paths: \n",
                     absl::StrJoin(unknown_key_paths, "\n")));
  }
  return flattened_json;
}

bool IsJsonSubset(const StringMap& source_map, const StringMap& target_map,
                  std::vector<std::string>& differences) {
  // Iterate over all the paths in source and compare to the paths in target.
  bool is_subset = true;
  for (const auto& [source_path, source_value] : source_map) {
    auto target_iter = target_map.find(source_path);
    if (target_iter == target_map.end()) {
      differences.push_back(absl::StrCat("Missing: [", source_path,
                                         "] with value '", source_value, "'."));
      is_subset = false;
    } else if (source_value != target_iter->second) {
      differences.push_back(absl::StrCat("Mismatch: [", source_path, "]: '",
                                         source_value, "' != '",
                                         target_iter->second, "'"));
      is_subset = false;
    }
  }
  return is_subset;
}

absl::StatusOr<bool> IsJsonSubset(const nlohmann::json& source,
                                  const nlohmann::json& target,
                                  const StringSetMap& yang_path_key_name_map,
                                  std::vector<std::string>& differences) {
  ASSIGN_OR_RETURN(auto flat_source,
                   FlattenJsonToMap(source, yang_path_key_name_map,
                                    /*ignore_unknown_key_paths=*/false));
  ASSIGN_OR_RETURN(auto flat_target,
                   FlattenJsonToMap(target, yang_path_key_name_map,
                                    /*ignore_unknown_key_paths=*/false));
  return IsJsonSubset(flat_source, flat_target, differences);
}

absl::StatusOr<bool> AreJsonEqual(const nlohmann::json& lhs,
                                  const nlohmann::json& rhs,
                                  const StringSetMap& yang_path_key_name_map,
                                  std::vector<std::string>& differences) {
  // Create a flattened map of the lhs.
  ASSIGN_OR_RETURN(const StringMap& flat_lhs,
                   FlattenJsonToMap(lhs, yang_path_key_name_map,
                                    /*ignore_unknown_key_paths=*/false));

  // Create a flattened map of the rhs.
  ASSIGN_OR_RETURN(const StringMap& flat_rhs,
                   FlattenJsonToMap(rhs, yang_path_key_name_map,
                                    /*ignore_unknown_key_paths=*/false));

  // Create a union of the paths from both lhs and rhs.
  absl::flat_hash_set<std::string> all_paths;
  for (const auto& [path, _] : flat_lhs) all_paths.insert(path);
  for (const auto& [path, _] : flat_rhs) all_paths.insert(path);

  // Iterate over all the paths and compare to the paths in lhs and rhs.
  bool are_equal = true;
  for (const auto& path : all_paths) {
    auto lhs_iter = flat_lhs.find(path);
    auto rhs_iter = flat_rhs.find(path);

    if (lhs_iter != flat_lhs.end() && rhs_iter != flat_rhs.end()) {
      // The path exists in both. Compare the values.
      if (lhs_iter->second != rhs_iter->second) {
        differences.push_back(absl::StrCat("Mismatch: [", path, "]: '",
                                           lhs_iter->second, "' != '",
                                           rhs_iter->second, "'"));
        are_equal = false;
      }
    } else if (rhs_iter == flat_rhs.end()) {
      // Exists in lhs but not rhs.
      differences.push_back(absl::StrCat(
          "Missing rhs: [", path, "] with value '", lhs_iter->second, "'."));
      are_equal = false;
    } else {
      // Exists in rhs but not lhs.
      differences.push_back(absl::StrCat(
          "Missing lhs: [", path, "] with value '", rhs_iter->second, "'."));
      are_equal = false;
    }
  }
  return are_equal;
}

std::string GetSimpleJsonValueAsString(const nlohmann::json& source) {
  switch (source.type()) {
    case nlohmann::json::value_t::number_integer:
      return absl::StrCat(source.get<int>());
    case nlohmann::json::value_t::number_unsigned:
      return absl::StrCat(source.get<uint>());
    case nlohmann::json::value_t::number_float:
      return absl::StrCat(source.get<float>());
    case nlohmann::json::value_t::string:
      return source.get<std::string>();
    case nlohmann::json::value_t::boolean:
      return source.get<bool>() ? "true" : "false";
    default:
      return "";
  }
}

}  // namespace json_yang

namespace pins_test {

namespace {

using ::Json::arrayValue;
using ::Json::objectValue;
using ::Json::Value;

}  // namespace

bool JsonDiff(const Value& source, const Value& target, Value& diff) {
  // If values are the same, return empty diff.
  if (source == target) {
    return false;
  }

  if (source.type() != target.type()) {
    // Different types: replace value.
    diff = source;
    return true;
  } else {
    // Do a deep comparison of array/object members.
    switch (source.type()) {
      case arrayValue: {
        bool diff_detected = false;
        uint traverse_size =
            source.size() < target.size() ? source.size() : target.size();
        // First pass: traverse common elements.
        for (uint i = 0; i < traverse_size; ++i) {
          Value diff_at_index;
          // Recursive call to compare array values at index i.
          if (JsonDiff(source[i], target[i], diff_at_index)) {
            if (!diff_at_index.isNull()) {
              diff[diff.size()] = diff_at_index;
              diff_detected = true;
            }
          }
        }
        // Index i now reached the end of second array, in a second pass,
        // traverse the remaining elements in the first array and add
        // remaining elements to diff.
        for (uint i = traverse_size; i < source.size(); ++i) {
          // Add operations in reverse order to avoid invalid
          // indices.
          diff[diff.size()] = source[i];
          diff_detected = true;
        }
        return diff_detected;
      }

      case objectValue: {
        bool diff_detected = false;
        // Traverse this object's elements.
        for (const auto& name : source.getMemberNames()) {
          // Recursive call to compare object values with key 'name'.
          Value diff_at_key;
          if (JsonDiff(source[name], target[name], diff_at_key)) {
            if (!diff_at_key.isNull()) {
              diff[name] = diff_at_key;
              diff_detected = true;
            }
          }
        }
        return diff_detected;
      }

      default:
        diff = source;
        return true;
    }
  }
}

void JsonReplaceKey(Value& source, const absl::string_view old_key,
                    const absl::string_view new_key) {
  if (old_key == new_key) {
    return;
  }

  switch (source.type()) {
    case arrayValue: {
      for (auto& s : source) {
        // recursive call to replace key
        JsonReplaceKey(s, old_key, new_key);
      }
      break;
    }

    case objectValue: {
      if (source.isMember(std::string(old_key))) {
        source[std::string(new_key).c_str()] =
            source[std::string(old_key).c_str()];
        source.removeMember(std::string(old_key).c_str());
      }
      for (const auto& name : source.getMemberNames()) {
        // recursive call to replace keys in members
        JsonReplaceKey(source[name], old_key, new_key);
      }
      break;
    }

    default:
      break;
  }
}

bool JsonIsSubset(const Value& source, const Value& target,
                  std::vector<std::string>& error_messages) {
  if (source.type() != target.type()) {
    return false;
  }
  if (source == target) {
    return true;
  }
  switch (source.type()) {
    case objectValue: {
      for (const auto& key : source.getMemberNames()) {
        if (!target.isMember(key)) {
          std::string error_string = absl::Substitute(
              "$0 is not member of target $1", key, target.toStyledString());
          error_messages.push_back(error_string);
          return false;
        }
        if (!JsonIsSubset(source[key], target[key], error_messages)) {
          return false;
        }
      }
      return true;
    }
    case arrayValue: {
      if (source.size() > target.size()) {
        std::string error_string = absl::Substitute(
            "Source has more elements than target, "
            "Source size: $0, Target size: $1, "
            "Source: $2, Target: $3",
            source.size(), target.size(), source.toStyledString(),
            target.toStyledString());
        error_messages.push_back(error_string);
        return false;
      }
      for (int i = 0; i < source.size(); ++i) {
        bool match_found = false;
        for (int j = 0; j < target.size(); ++j) {
          if (JsonIsSubset(source[i], target[j], error_messages)) {
            match_found = true;
            break;
          }
        }
        if (match_found == false) {
          std::string error_string = absl::Substitute(
              "source[$0]: $1 is not a subset of target: $2", i,
              source[i].toStyledString(), target.toStyledString());
          error_messages.push_back(error_string);
          return false;
        }
      }
      return true;
    }
    default: {
      std::string error_string =
          absl::Substitute("source: $0 is not a subset of target: $1",
                           source.toStyledString(), target.toStyledString());
      error_messages.push_back(error_string);
      return false;
    }
  }
  return false;
}

bool JsonValueIsEqual(const Value& value1, const Value& value2) {
  // First check whether the type is the same.
  if (value1.type() != value2.type()) {
    // Special case: since JSON treat int and uint different, it's possible when
    // parsing, the integer is parsed to different type than expected which
    // cause the comparison failed.
    if (value1.isIntegral() && value2.isIntegral()) {
      return value1.asInt64() == value2.asInt64();
    }
    // Otherwise, return false since type is not same.
    return false;
  }
  // Check the JSON value size. For object and array, the size will be the
  // member size, all other basic type size will be 0.
  if (value1.size() != value2.size()) {
    return false;
  }

  switch (value1.type()) {
    case arrayValue: {
      // Recurse on array. Array comparison has to be O(N*N) since JSON array
      // didn't have key and cannot be sorted. Therefore we have to compare each
      // of them to verify there is no difference.
      absl::flat_hash_set<int64_t> identical_index;
      for (int i = 0; i != value1.size(); ++i) {
        for (int j = 0; j != value2.size(); ++j) {
          if (!identical_index.contains(j)) {
            if (JsonValueIsEqual(value1[i], value2[j])) {
              identical_index.insert(j);
              break;
            }
          }
        }
        // didn't find a matching index in array2 for array1[i].
        if (identical_index.size() != (i + 1)) return false;
      }
      return true;
    }
    case objectValue: {
      for (const auto& member : value1.getMemberNames()) {
        if (!JsonValueIsEqual(value1[member], value2[member])) {
          return false;
        }
      }
      return true;
    }
    default: {
      return value1 == value2;
    }
  }
  return false;
}

}  // namespace pins_test
