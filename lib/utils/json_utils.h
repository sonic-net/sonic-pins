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

#include "absl/strings/string_view.h"
#include "include/json/value.h"

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
bool JsonIsSubset(const Json::Value& source, const Json::Value& target);

// Compare the equilvalence of two JSON values, allowes for the array/object
// field to be in the different order. For example:
// {'a':'value1', 'b': {'c':['value2','value3'], 'd':['value4']}, 'e':'value5'}
// is the same with {'b': {'d':['value4'], 'c':['value3','value2']},
// 'e':'value5', 'a':'value1'}. Naive JSON comparison must be in strict order.
bool JsonValueIsEqual(const Json::Value& value1, const Json::Value& value2);

}  // namespace pins_test

#endif  // PINS_LIB_UTILS_JSON_UTILS_H_
