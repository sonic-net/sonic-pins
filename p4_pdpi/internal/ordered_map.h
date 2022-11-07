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

#ifndef GOOGLE_P4_PDPI_INTERNAL_ORDERED_MAP_H_
#define GOOGLE_P4_PDPI_INTERNAL_ORDERED_MAP_H_

#include "absl/container/btree_map.h"

// Ordered view of an unordered Map. Useful for iterating over the map
// in deterministic fashion. Note that the original map and its contents must
// remain live (i.e. allocated) or else this will cause dangling references.
template <typename M>
absl::btree_map<typename M::key_type, const typename M::mapped_type&> Ordered(
    const M& map) {
  return absl::btree_map<typename M::key_type, const typename M::mapped_type&>(
      map.begin(), map.end());
}

#endif  // GOOGLE_P4_PDPI_INTERNAL_ORDERED_MAP_H_
