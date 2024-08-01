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

#ifndef PINS_LIB_UTILS_JSON_UTILS_H_
#define PINS_LIB_UTILS_JSON_UTILS_H_

#include <string>
#include <vector>

#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_map.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "include/json/value.h"
#include "include/nlohmann/json.hpp"

namespace pins_test {

// The API returns the difference between the 2 Json::Value objects passed as
// parameters. The API returns the set of elements in the first parameter which
// are not present in the second parameter. So the semantics is source-target.
//
// Note: This API will be used by experimental to get the applied config STATE by taking
// the diff of the STATE and the OPERATIONAL STATE. Underlying assumption is
// that the order of array elements is the same in STATE and OPERATIONAL data.
//
// For example if there are 3 interfaces on the switch. STATE would have the
// CONFIG and OPERATIONAL STATE for all 3 interfaces and the OPERATIONAL state
// will just have the OPERATIONAL STATE for the 3 interfaces but the order of
// 3 interfaces in both the STATE and OPERATIONAL state will be the same.
bool JsonDiff(const Json::Value& source, const Json::Value& target,
              Json::Value& diff);

// Iterates recursively over the members of the Json::Value object passed as a
// parameter and replaces member name old_key with new_key. Note: If member
// with name new_key already exists in the object it will be over-written.
void JsonReplaceKey(Json::Value& source, absl::string_view old_key,
                    absl::string_view new_key);

// If source and target are of type Json::objectValue then iterate over members
// of the source and check if the member is also a member of target and has the
// same value.
//
// If source and target are of type Json::arrayValue then iterate over elements
// of source and check if the element is present at any index (not necessarily
// matching index) on the target.
//
// If the source and target are of any scalar type, then check if they match.
// This would correspond to the leaves.
bool JsonIsSubset(const Json::Value& source, const Json::Value& target,
                  std::vector<std::string>& error_messages);

// Compare the equilvalence of two JSON values, allowes for the array/object
// field to be in the different order. For example:
// {'a':'value1', 'b': {'c':['value2','value3'], 'd':['value4']}, 'e':'value5'}
// is the same with {'b': {'d':['value4'], 'c':['value3','value2']},
// 'e':'value5', 'a':'value1'}. Naive JSON comparison must be in strict order.
bool JsonValueIsEqual(const Json::Value& value1, const Json::Value& value2);

}  // namespace pins_test

namespace json_yang {
// Helper functions to manipulate JSON that encode data modeled with YANG.
// See http://datatracker.ietf.org/doc/html/rfc7159 for JSON.
// See http://datatracker.ietf.org/doc/html/rfc7950 for YANG modeling language.
// See http://datatracker.ietf.org/doc/html/rfc7951 for JSON encoding of YANG.

// Returns a JSON value from the input JSON string that contains data modeled
// with YANG.
// - Returns a null JSON value if the input is an empty string.
// - Returns an invalid argument error if the input could not be parsed.
absl::StatusOr<nlohmann::json> ParseJson(absl::string_view json_str);

// Returns a pretty-printed JSON string from the JSON value.
// - Returns an empty string if the JSON value is null.
// - Replaces invalid UTF-8 sequences with U+FFFD.
std::string DumpJson(const nlohmann::json& value);

// Returns a neatly formatted version of the input JSON string, best effort.
// If the input string cannot be parsed as JSON, returns the original string.
std::string FormatJsonBestEffort(absl::string_view raw_json);

// Returns a JSON value by recursively replacing the names of name/value pairs
// in JSON objects using the mapping specified in the old to new names map.
//   - If source already contains the new name then it may be overwritten.
//   - The behavior is undefined if the map of name replacements maps several
//     old names to the same new name.
nlohmann::json ReplaceNamesinJsonObject(
    const nlohmann::json& source,
    const absl::flat_hash_map<std::string, std::string>&
        old_name_to_new_name_map);

// Modifies the JSON value in place by recursively replacing the names of
// name/value pairs in JSON objects using the mapping specified in the old to
// new names map.
//   - If root already contains the new name then it may be overwritten.
//   - The behavior is undefined if the map of name replacements maps several
//     old names to the same new name.
void ReplaceNamesinJsonObject(
    const absl::flat_hash_map<std::string, std::string>&
        old_name_to_new_name_map,
    nlohmann::json& root);

// Returns a map of flattened paths to leaves in the JSON encoded YANG modeled
// data to string values from the input JSON value using the map of yang paths
// (representing array-link containers) to the leaf that is defined as the key
// for the elements in the array in the yang model.
//
// A list data node in YANG is represented as an array in JSON. The YANG model
// is required to define one or more leaf data nodes as keys that uniquely
// identify the elements in the list. (see rfc7950#section-7.8.2).
//
//  - yang_path_key_name_map contains a map of yang list paths to the name of
//    the leaf that's defined as the key for that list. There can exist multiple
//    keys.
//  - If ignore_unknown_key_paths is true and the key is not found in the map,
//    then the entire array will not be included in the output.
absl::StatusOr<absl::flat_hash_map<std::string, std::string>> FlattenJsonToMap(
    const nlohmann::json& root,
    const absl::flat_hash_map<std::string, absl::btree_set<std::string>>&
        yang_path_key_name_map,
    bool ignore_unknown_key_paths);

// Returns true if all yang leaf nodes in 'source' are present in 'target' with
// the same values or false otherwise.
// - Returns an error if the source/target cannot be parsed into JSON values.
// - Populates the yang paths missing or have mismatched values wtih 'target' in
//   'differences'.
// - Object/Array members can be in any order.
// - Flattens the JSON values using the map of yang list paths to the name of
//   the leaf that's defined as the key.
absl::StatusOr<bool> IsJsonSubset(
    const nlohmann::json& source, const nlohmann::json& target,
    const absl::flat_hash_map<std::string, absl::btree_set<std::string>>&
        yang_path_key_name_map,
    std::vector<std::string>& differences);

// Returns true only if lhs and rhs have the same sets of paths with the same
// values and false with the differences populated if not. Object/Array members
// can be in any order. Uses the yang key leaf map to identify array
// elements.
absl::StatusOr<bool> AreJsonEqual(
    const nlohmann::json& lhs, const nlohmann::json& rhs,
    const absl::flat_hash_map<std::string, absl::btree_set<std::string>>&
        yang_path_key_name_map,
    std::vector<std::string>& differences);

// Helper function to return the simple JSON value (number, boolean, string).
// - returns an empty string if not a simple JSON value (object, array, null).
std::string GetSimpleJsonValueAsString(const nlohmann::json& source);

}  // namespace json_yang

#endif  // PLATFORMS_NETWORKING_PINS_CONFIG_UTILS_JSON_UTILS_H_
