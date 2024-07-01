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
#ifndef PINS_P4RT_APP_UTILS_LRU_CACHE_H_
#define PINS_P4RT_APP_UTILS_LRU_CACHE_H_

#include <list>

#include "absl/container/flat_hash_map.h"

namespace p4rt_app {

// General purpose LRU cache.
// This is a map with fixed capacity to prevent unbounded memory growth.
template <class T, class U>
class LruCache {
 public:
  explicit LruCache(uint32_t capacity) : capacity_(capacity) {}
  ~LruCache() = default;

  U& operator[](const T& key) {
    auto it = cache_.find(key);
    if (it == cache_.end()) {
      if (cache_.size() >= capacity_) {
        T last = queue_.back();
        queue_.pop_back();
        cache_.erase(last);
      }
    } else {
      queue_.erase(it->second.ptr);
    }

    queue_.push_front(key);
    auto& c = cache_[key];
    c.ptr = queue_.begin();
    return c.data;
  }

  const U& at(const T& k) const { return cache_.at(k).data; }
  bool contains(const T& k) const { return cache_.count(k) != 0; }
  std::size_t size() const { return cache_.size(); }
  uint32_t capacity() const { return capacity_; }

 private:
  struct Entry {
    typename std::list<T>::iterator ptr;
    U data;
  };

  // Capacity of the cache.
  uint32_t capacity_;

  // A queue to keep track of the entry usage.
  // The most recent accessed entry is in front of the queue.
  std::list<T> queue_;

  // A map to store the contents of the cache.
  absl::flat_hash_map<T, Entry> cache_;
};

}  // namespace p4rt_app

#endif  // PINS_P4RT_APP_UTILS_LRU_CACHE_H_
