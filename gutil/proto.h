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

#ifndef GUTIL_PROTO_H
#define GUTIL_PROTO_H

#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "google/protobuf/message.h"
#include "gutil/status.h"

namespace gutil {

// Read the contents of the file into a protobuf.
absl::Status ReadProtoFromFile(absl::string_view filename,
                               google::protobuf::Message *message);

// Read the contents of the string into a protobuf.
absl::Status ReadProtoFromString(absl::string_view proto_string,
                                 google::protobuf::Message *message);

// Read the contents of the given string into a protobuf and returns it.
template <class T>
absl::StatusOr<T> ParseTextProto(absl::string_view proto_string) {
  T message;
  if (auto status = ReadProtoFromString(proto_string, &message); status.ok()) {
    return message;
  } else {
    return status;
  }
}

// Get the name of the oneof enum that is set.
// Eg:
// message IrValue {
//   oneof format {
//     string hex_str = 1;
//     string ipv4 = 2;
//     string ipv6 = 3;
//     string mac = 4;
//     string str = 5;
//   }
// }
// IrValue value;
// value.set_hex_str("0xf00d");
// std::string name = GetOneOfFieldName(value, std::string("format"));
// EXPECT_EQ(name, "hex_str");
absl::StatusOr<std::string> GetOneOfFieldName(
    const google::protobuf::Message &message, const std::string &oneof_name);
}  // namespace gutil
#endif  // GUTIL_PROTO_H
