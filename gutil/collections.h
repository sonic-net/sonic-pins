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

#ifndef GUTIL_COLLECTIONS_H
#define GUTIL_COLLECTIONS_H

#include <string>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "glog/logging.h"
#include "google/protobuf/map.h"
#include "gutil/status.h"

namespace gutil {

// Returns a const copy of the value associated with a given key if it exists,
// or a status failure if it does not.
//
// WARNING: prefer FindOrNull if the value can be large to avoid the copy.
template <typename M>
absl::StatusOr<const typename M::mapped_type> FindOrStatus(
    const M &m, const typename M::key_type &k) {
  auto it = m.find(k);
  if (it != m.end()) return it->second;
  return absl::NotFoundError("Key not found");
}

// Returns a non-null pointer of the value associated with a given key
// if it exists, or a status failure if it does not.
template <typename M>
absl::StatusOr<const typename M::mapped_type *> FindPtrOrStatus(
    M &m, const typename M::key_type &k) {
  auto it = m.find(k);
  if (it != m.end()) return &it->second;
  return absl::NotFoundError("Key not found");
}

// Returns a const pointer of the value associated with a given key if it
// exists, or a nullptr if it does not.
template <typename M>
const typename M::mapped_type *FindOrNull(const M &m,
                                          const typename M::key_type &k) {
  const auto it = m.find(k);
  if (it != m.end()) return &(it->second);
  return nullptr;
}

// Returns a non-const pointer of the value associated with a given key if it
// exists, or a nullptr if it does not.
template <typename M>
typename M::mapped_type *FindOrNull(M &m, const typename M::key_type &k) {
  auto it = m.find(k);
  if (it != m.end()) return &(it->second);
  return nullptr;
}

// Returns a reference of the value associated with a given key if it exists,
// crashes if it does not.
template <typename M>
typename M::mapped_type &FindOrDie(M &map, const typename M::key_type &key) {
  auto iter = map.find(key);
  CHECK(iter != map.end()) << "Could not find key";
  return iter->second;
}

// Returns a const reference of the value associated with a given key if it
// exists, crashes if it does not.
template <typename M>
const typename M::mapped_type &FindOrDie(const M &map,
                                         const typename M::key_type &key) {
  auto iter = map.find(key);
  CHECK(iter != map.end()) << "Could not find key";

  return iter->second;
}

// Returns a copy of the value associated with the given key if it exists, or
// returns the given default value otherwise.
// NOTE: May be inefficient for large datatypes that are expensive to copy.
template <typename Map>
typename Map::mapped_type FindOrDefault(
    const Map &map, const typename Map::key_type &key,
    typename Map::mapped_type default_value) {
  auto it = map.find(key);
  return (it != map.end()) ? it->second : default_value;
}

// Checks if the id is unique in set.
template <typename M>
absl::Status InsertIfUnique(absl::flat_hash_set<M> &set, const M &id,
                            const std::string &error_message) {
  const auto it = set.insert(id);
  if (!it.second) {
    return absl::Status(absl::StatusCode::kInvalidArgument, error_message);
  }

  return absl::OkStatus();
}

template <typename K, typename V>
absl::Status InsertIfUnique(absl::flat_hash_map<K, V> &map, K key, const V &val,
                            const std::string &error_message) {
  auto it = map.insert({key, val});
  if (!it.second) {
    return absl::Status(absl::StatusCode::kInvalidArgument, error_message);
  }

  return absl::OkStatus();
}

template <typename K, typename V>
absl::Status InsertIfUnique(google::protobuf::Map<K, V> *map, K key,
                            const V &val, const std::string &error_message) {
  auto it = map->insert({key, val});
  if (!it.second) {
    return absl::Status(absl::StatusCode::kInvalidArgument, error_message);
  }

  return absl::OkStatus();
}

}  // namespace gutil

#endif  // GUTIL_COLLECTIONS_H
