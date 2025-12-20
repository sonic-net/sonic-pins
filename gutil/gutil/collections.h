// Copyright 2020 Google LLC
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

#ifndef PINS_GUTIL_GUTIL_COLLECTIONS_H_
#define PINS_GUTIL_GUTIL_COLLECTIONS_H_

#include <string>
#include <type_traits>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/log/check.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "google/protobuf/map.h"
#include "gutil/gutil/status.h"

namespace gutil {

// Returns a vector of the keys in a map collection.
template <typename M>
std::vector<typename M::key_type> Keys(const M& m) {
  std::vector<typename M::key_type> keys;
  for (const auto& [key, val] : m) keys.push_back(key);
  return keys;
}

// Returns a const copy of the value associated with a given key if it exists,
// or a status failure if it does not.
//
// WARNING: prefer FindOrNull if the value can be large to avoid the copy.
template <typename M, typename KeyType = typename M::key_type>
absl::StatusOr<const typename M::mapped_type> FindOrStatus(const M& m,
                                                           const KeyType& k) {
  auto it = m.find(k);
  if (it != m.end()) return it->second;
  if constexpr (std::is_same_v<KeyType, std::string>) {
    return absl::NotFoundError(absl::StrCat("Key not found: '", k, "'"));
  } else {
    return absl::NotFoundError("Key not found");
  }
}

// Returns a const, non-null pointer of the value associated with a given key
// if it exists, or a status failure if it does not.
template <typename M, typename KeyType = typename M::key_type>
absl::StatusOr<const typename M::mapped_type*> FindPtrOrStatus(
    const M& m, const KeyType& k) {
  auto it = m.find(k);
  if (it != m.end()) return &it->second;
  if constexpr (std::is_same_v<typename M::key_type, std::string>) {
    return absl::NotFoundError(absl::StrCat("Key not found: '", k, "'"));
  } else {
    return absl::NotFoundError("Key not found");
  }
}

// Returns a mutable, non-null pointer of the value associated with a given key
// if it exists, or a status failure if it does not.
template <typename M, typename KeyType = typename M::key_type>
absl::StatusOr<typename M::mapped_type*> FindMutablePtrOrStatus(
    M& m, const KeyType& k) {
  auto it = m.find(k);
  if (it != m.end()) return &it->second;
  if constexpr (std::is_same_v<typename M::key_type, std::string>) {
    return absl::NotFoundError(absl::StrCat("Key not found: '", k, "'"));
  } else {
    return absl::NotFoundError("Key not found");
  }
}

// Returns a const pointer of the value associated with a given key if it
// exists, or a nullptr if it does not.
template <typename M, typename KeyType = typename M::key_type>
const typename M::mapped_type* FindOrNull(const M& m, const KeyType& k) {
  const auto it = m.find(k);
  if (it != m.end()) return &(it->second);
  return nullptr;
}

// Returns a non-const pointer of the value associated with a given key if it
// exists, or a nullptr if it does not.
template <typename M, typename KeyType = typename M::key_type>
typename M::mapped_type* FindOrNull(M& m, const KeyType& k) {
  auto it = m.find(k);
  if (it != m.end()) return &(it->second);
  return nullptr;
}

// Returns a reference of the value associated with a given key if it exists,
// crashes if it does not.
template <typename M, typename KeyType = typename M::key_type>
typename M::mapped_type& FindOrDie(M& map, const KeyType& key) {
  auto iter = map.find(key);
  CHECK(iter != map.end()) << "Could not find key";  // Crash OK
  return iter->second;
}

// Returns a const reference of the value associated with a given key if it
// exists, crashes if it does not.
template <typename M, typename KeyType = typename M::key_type>
const typename M::mapped_type& FindOrDie(const M& map, const KeyType& key) {
  auto iter = map.find(key);
  CHECK(iter != map.end()) << "Could not find key";  // Crash OK

  return iter->second;
}

// Returns a copy of the value associated with the given key if it exists, or
// returns the given default value otherwise.
// NOTE: May be inefficient for large datatypes that are expensive to copy.
template <typename M, typename KeyType = typename M::key_type>
typename M::mapped_type FindOrDefault(const M& map, const KeyType& key,
                                      typename M::mapped_type default_value) {
  auto it = map.find(key);
  return (it != map.end()) ? it->second : default_value;
}

// Checks if the id is unique in set.
template <typename M>
absl::Status InsertIfUnique(absl::flat_hash_set<M>& set, const M& id,
                            const std::string& error_message) {
  const auto it = set.insert(id);
  if (!it.second) {
    return absl::Status(absl::StatusCode::kInvalidArgument, error_message);
  }

  return absl::OkStatus();
}

template <typename K, typename V>
absl::Status InsertIfUnique(absl::flat_hash_map<K, V>& map, K key, const V& val,
                            const std::string& error_message) {
  auto it = map.insert({key, val});
  if (!it.second) {
    return absl::Status(absl::StatusCode::kInvalidArgument, error_message);
  }

  return absl::OkStatus();
}

template <typename K, typename V>
absl::Status InsertIfUnique(google::protobuf::Map<K, V>* map, K key,
                            const V& val, const std::string& error_message) {
  auto it = map->insert({key, val});
  if (!it.second) {
    return absl::Status(absl::StatusCode::kInvalidArgument, error_message);
  }

  return absl::OkStatus();
}

}  // namespace gutil

#endif  // PINS_GUTIL_GUTIL_COLLECTIONS_H_
