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

#ifndef PINS_GUTIL_TESTING_H
#define PINS_GUTIL_TESTING_H

#include "absl/log/check.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"

namespace gutil {

// Parses a protobuf from a string, and crashes if parsing failed. Only use in
// tests.
template <typename T>
T ParseProtoOrDie(absl::string_view proto_string) {
  T message;
  CHECK_OK(ReadProtoFromString(proto_string, &message));  // Crash OK
  return message;
}

// Parses a protobuf from a file, and crashes if parsing failed. Only use in
// tests.
template <typename T>
T ParseProtoFileOrDie(absl::string_view proto_file) {
  T message;
  CHECK_OK(ReadProtoFromFile(proto_file, &message));  // Crash OK
  return message;
}

// Takes a snake_case string and returns a CamelCase string. If `lower_first` is
// set, the first character will be lowercase (if a letter) and otherwise it
// will be uppercase.
// Used to e.g. convert snake case strings to GTEST compatible test names.
std::string SnakeCaseToCamelCase(absl::string_view input,
                                 bool lower_first = false);

}  // namespace gutil

#endif  // PINS_GUTIL_TESTING_H
