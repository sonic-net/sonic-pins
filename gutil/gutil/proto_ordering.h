// Functions for sorting, ordering, and deduplicating Protobuf messages.

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

#ifndef PINS_GUTIL_GUTIL_PROTO_ORDERING_H_
#define PINS_GUTIL_GUTIL_PROTO_ORDERING_H_

#include <iterator>
#include <utility>

#include "absl/algorithm/container.h"
#include "absl/types/span.h"
#include "google/protobuf/message.h"
#include "google/protobuf/repeated_ptr_field.h"
#include "gutil/gutil/proto.h"

namespace gutil {

// A strict total order (`<`) on proto messages. The order is not semantically
// meaningful, but can be useful for operations such as sorting.
//
// CAUTION: This function is very inefficient and must only be used in
// performance-insensitive settings.
bool InefficientProtoLessThan(const google::protobuf::Message& message1,
                              const google::protobuf::Message& message2);

// Sorts the given sequence of `messages` with respect to an arbitrary, but
// deterministic order.
//
// CAUTION: This function is very inefficient and must only be used in
// performance-insensitive settings.
template <typename ProtoSequence>
void InefficientProtoSort(ProtoSequence& messages);

// Sorts the given sequence of `messages` with respect to an arbitrary, but
// deterministic order, and removes all duplicate messages.
//
// CAUTION: This function is very inefficient and must only be used in
// performance-insensitive settings.
template <class ProtoSequence>
void InefficientProtoSortAndDedup(ProtoSequence& messages);

// == END OF PUBLIC INTERFACE ==================================================

template <typename ProtoSequence>
void InefficientProtoSort(ProtoSequence& messages) {
  absl::c_stable_sort(messages, InefficientProtoLessThan);
}

// Helper to obtain back inserter of a given `Container`. Essentially a drop-in
// replacement for `std::back_inserter` that also works for repeated protobuf
// fields.
template <class Container>
auto BackInserter(Container& c) {
  return std::back_inserter(c);
}
template <class T>
auto BackInserter(google::protobuf::RepeatedPtrField<T>& c) {
  return google::protobuf::RepeatedPtrFieldBackInserter(&c);
}

template <class ProtoSequence>
void InefficientProtoSortAndDedup(ProtoSequence& messages) {
  InefficientProtoSort(messages);
  ProtoSequence tmp;
  std::swap(messages, tmp);
  absl::c_unique_copy(tmp, BackInserter(messages),
                      google::protobuf::util::MessageDifferencer::Equals);
}

}  // namespace gutil

#endif  // PINS_GUTIL_GUTIL_PROTO_ORDERING_H_
