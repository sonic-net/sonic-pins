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

#include "absl/container/flat_hash_set.h"
#include "glog/logging.h"

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

bool JsonIsSubset(const Value& source, const Value& target) {
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
          return false;
        }
        if (!JsonIsSubset(source[key], target[key])) {
          return false;
        }
      }
      return true;
    }
    case arrayValue: {
      if (source.size() > target.size()) {
        return false;
      }
      for (int i = 0; i < source.size(); ++i) {
        bool match_found = false;
        for (int j = 0; j < target.size(); ++j) {
          if (JsonIsSubset(source[i], target[j])) {
            match_found = true;
            break;
          }
        }
        if (match_found == false) {
          return false;
        }
      }
      return true;
    }

    default:
      return false;
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
