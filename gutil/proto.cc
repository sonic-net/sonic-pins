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

#include "gutil/proto.h"

#include <fcntl.h>

#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "google/protobuf/descriptor.h"
#include "google/protobuf/io/zero_copy_stream_impl.h"
#include "google/protobuf/message.h"
#include "google/protobuf/text_format.h"
#include "gutil/status.h"

namespace gutil {

absl::Status ReadProtoFromFile(absl::string_view filename,
                               google::protobuf::Message *message) {
  // Verifies that the version of the library that we linked against is
  // compatible with the version of the headers we compiled against.
  GOOGLE_PROTOBUF_VERIFY_VERSION;

  int fd = open(std::string(filename).c_str(), O_RDONLY);
  if (fd < 0) {
    return InvalidArgumentErrorBuilder()
           << "Error opening the file " << filename;
  }

  google::protobuf::io::FileInputStream file_stream(fd);
  file_stream.SetCloseOnDelete(true);

  if (!google::protobuf::TextFormat::Parse(&file_stream, message)) {
    return InvalidArgumentErrorBuilder() << "Failed to parse file " << filename;
  }

  return absl::OkStatus();
}

absl::Status ReadProtoFromString(absl::string_view proto_string,
                                 google::protobuf::Message *message) {
  // Verifies that the version of the library that we linked against is
  // compatible with the version of the headers we compiled against.
  GOOGLE_PROTOBUF_VERIFY_VERSION;

  if (!google::protobuf::TextFormat::ParseFromString(std::string(proto_string),
                                                     message)) {
    return InvalidArgumentErrorBuilder()
           << "Failed to parse string " << proto_string;
  }

  return absl::OkStatus();
}

absl::StatusOr<std::string> GetOneOfFieldName(
    const google::protobuf::Message &message, const std::string &oneof_name) {
  const auto *oneof_descriptor =
      message.GetDescriptor()->FindOneofByName(oneof_name);
  const auto *field = message.GetReflection()->GetOneofFieldDescriptor(
      message, oneof_descriptor);
  if (!field) {
    return gutil::NotFoundErrorBuilder()
           << "Oneof field \"" << oneof_name << "\" is not set";
  }
  return field->name();
}
}  // namespace gutil
