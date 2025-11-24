// Copyright 2021 Google LLC
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
#include "gutil/gutil/status.h"

#include <string>

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "grpcpp/grpcpp.h"

namespace gutil {

std::string StableStatusToString(const absl::Status& status) {
  return absl::StrCat(absl::StatusCodeToString(status.code()), ": ",
                      status.message(), "\n");
}

absl::Status gutil::StatusBuilder::GetStatusAndLog() const {
  std::string message = source_;
  switch (join_style_) {
    case MessageJoinStyle::kPrepend:
      absl::StrAppend(&message, stream_.str(), status_.message());
      break;
    case MessageJoinStyle::kAppend:
      absl::StrAppend(&message, status_.message(), stream_.str());
      break;
    case MessageJoinStyle::kAnnotate:
    default: {
      if (!status_.message().empty() && !stream_.str().empty()) {
        absl::StrAppend(&message, status_.message(), "; ", stream_.str());
      } else if (status_.message().empty()) {
        absl::StrAppend(&message, stream_.str());
      } else {
        absl::StrAppend(&message, status_.message());
      }
      break;
    }
  }
  if (log_error_ && status_.code() != absl::StatusCode::kOk) {
    std::cout << message << std::endl;
  }
  absl::Status new_status(status_.code(), message);
  status_.ForEachPayload(
      [&new_status](absl::string_view url, const absl::Cord& cord) {
        new_status.SetPayload(url, cord);
      });
  return new_status;
}

grpc::Status AbslStatusToGrpcStatus(const absl::Status& status) {
  return grpc::Status(static_cast<grpc::StatusCode>(status.code()),
                      std::string(status.message()));
}

absl::Status GrpcStatusToAbslStatus(const grpc::Status& status) {
  return absl::Status(static_cast<absl::StatusCode>(status.error_code()),
                      status.error_message());
}

}  // namespace gutil
