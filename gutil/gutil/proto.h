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

#ifndef PINS_GUTIL_GUTIL_PROTO_H_
#define PINS_GUTIL_GUTIL_PROTO_H_

#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "google/protobuf/message.h"
#include "google/protobuf/util/json_util.h"
#include "google/protobuf/util/message_differencer.h"
#include "gutil/gutil/status.h"

namespace gutil {

// Returns `true` if the given `message` has no fields set, `false` otherwise.
bool IsEmptyProto(const google::protobuf::Message& message);

// Read the contents of the file into a protobuf.
absl::Status ReadProtoFromFile(absl::string_view filename,
                               google::protobuf::Message* message);

// Read the contents of the string into a protobuf.
absl::Status ReadProtoFromString(absl::string_view proto_string,
                                 google::protobuf::Message* message);

// Saves the content of a protobuf into a file.
absl::Status SaveProtoToFile(absl::string_view filename,
                             const google::protobuf::Message& message);

// Read the contents of the given string into a protobuf and returns it.
template <class T>
absl::StatusOr<T> ParseTextProto(absl::string_view proto_string) {
  T message;
  RETURN_IF_ERROR(ReadProtoFromString(proto_string, &message));
  return message;
}

// Returns diff of the given protobuf messages, provided they have the same
// `Descriptor` (message1.GetDescriptor() == message2.GetDescriptor()), or
// returns `InvalidArgumentError` otherwise.
// Optionally, a `differ` can be provided for fine-grained control over how to
// compute the diff.
absl::StatusOr<std::string> ProtoDiff(
    const google::protobuf::Message& message1,
    const google::protobuf::Message& message2,
    google::protobuf::util::MessageDifferencer differ =
        google::protobuf::util::MessageDifferencer());

// Similar to `ProtoDiff`, execpt returns boolean result of equality comparison.
bool ProtoEqual(const google::protobuf::Message& message1,
                const google::protobuf::Message& message2,
                google::protobuf::util::MessageDifferencer& differ);

bool ProtoEqual(const google::protobuf::Message& message1,
                const google::protobuf::Message& message2);

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
    const google::protobuf::Message& message, const std::string& oneof_name);

// Print proto in TextFormat.
std::string PrintTextProto(const google::protobuf::Message& message);

// Print proto in TextFormat in a single line.
std::string PrintShortTextProto(const google::protobuf::Message& message);

// Parses the given JSON string into a proto of type `T`.
template <class T>
absl::StatusOr<T> ParseJsonAsProto(absl::string_view raw_json_string,
                                   bool ignore_unknown_fields = false);

// Serializes the given proto message as a JSON string.
absl::StatusOr<std::string> SerializeProtoAsJson(
    const google::protobuf::Message& proto);

// -- END OF PUBLIC INTERFACE - Implementation details follow ------------------

template <class T>
absl::StatusOr<T> ParseJsonAsProto(absl::string_view raw_json_string,
                                   bool ignore_unknown_fields) {
  google::protobuf::util::JsonParseOptions options;
  options.ignore_unknown_fields = ignore_unknown_fields;
  T proto;
  // OS protobuf uses its own `Status`-like and `string_view`-like classes, so
  // some gymnastics are required here:
  // - ToAbslStatus converts any `Status`-like type to an absl::Status.
  // - We pass in `{raw_json_string.data(), raw_json_string.size()}` instead of
  // `raw_json_string`, constructing a new object of the appropriate
  // `string_view`-like type implicitly.
  RETURN_IF_ERROR(
      gutil::ToAbslStatus(google::protobuf::util::JsonStringToMessage(
          {raw_json_string.data(), raw_json_string.size()}, &proto, options)));
  return proto;
}

}  // namespace gutil

#endif  // PINS_GUTIL_GUTIL_PROTO_H_
