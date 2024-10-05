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
#include "gutil/proto_string_error_collector.h"
#include "gutil/status.h"

namespace gutil {

bool IsEmptyProto(const google::protobuf::Message &message) {
  return message.ByteSizeLong() == 0;
}

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

  google::protobuf::TextFormat::Parser parser;
  std::string all_errors;
  StringErrorCollector collector(&all_errors);
  parser.RecordErrorsTo(&collector);

  if (!parser.ParseFromString(std::string(proto_string), message)) {
    return InvalidArgumentErrorBuilder()
           << "string <" << proto_string << "> did not parse as a"
           << message->GetTypeName() << ":\n"
           << all_errors;
  }

  return absl::OkStatus();
}

absl::Status SaveProtoToFile(absl::string_view filename,
                             const google::protobuf::Message &message) {
  // Verifies that the version of the library that we linked against is
  // compatible with the version of the headers we compiled against.
  GOOGLE_PROTOBUF_VERIFY_VERSION;
  int fd = open(std::string(filename).c_str(), O_WRONLY | O_CREAT, 0644);
  if (fd < 0) {
    return InvalidArgumentErrorBuilder()
           << "Error opening the file " << filename;
  }

  google::protobuf::io::FileOutputStream file_stream(fd);
  file_stream.SetCloseOnDelete(true);

  if (!google::protobuf::TextFormat::Print(message, &file_stream)) {
    return InvalidArgumentErrorBuilder()
           << "Failed to print proto to file " << filename;
  }

  file_stream.Flush();
  return absl::OkStatus();
}

absl::StatusOr<std::string> ProtoDiff(
    const google::protobuf::Message &message1,
    const google::protobuf::Message &message2,
    google::protobuf::util::MessageDifferencer differ) {
  if (message1.GetDescriptor() != message2.GetDescriptor()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "cannot compute diff for messages of incompatible descriptors `"
           << message1.GetDescriptor()->full_name() << "' vs '"
           << message2.GetDescriptor()->full_name() << "'";
  }

  std::string diff;
  differ.ReportDifferencesToString(&diff);
  differ.Compare(message1, message2);
  return diff;
}

bool ProtoEqual(const google::protobuf::Message &message1,
                const google::protobuf::Message &message2,
                google::protobuf::util::MessageDifferencer &differ) {
  if (message1.GetDescriptor() != message2.GetDescriptor()) {
    return false;
  }
  return differ.Compare(message1, message2);
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

std::string PrintTextProto(const google::protobuf::Message &message) {
  std::string message_text;

  google::protobuf::TextFormat::Printer printer;
  printer.SetExpandAny(true);

  printer.PrintToString(message, &message_text);

  return message_text;
}

// Print proto in TextFormat with single line mode enabled.
std::string PrintShortTextProto(const google::protobuf::Message &message) {
  std::string message_short_text;

  google::protobuf::TextFormat::Printer printer;
  printer.SetSingleLineMode(true);
  printer.SetExpandAny(true);

  printer.PrintToString(message, &message_short_text);
  // Single line mode currently might have an extra space at the end.
  if (!message_short_text.empty() && message_short_text.back() == ' ') {
    message_short_text.pop_back();
  }

  return message_short_text;
}

absl::StatusOr<std::string> SerializeProtoAsJson(
    const google::protobuf::Message &proto) {
  std::string json;
  RETURN_IF_ERROR(gutil::ToAbslStatus(
      google::protobuf::util::MessageToJsonString(proto, &json)));
  return json;
}

}  // namespace gutil
