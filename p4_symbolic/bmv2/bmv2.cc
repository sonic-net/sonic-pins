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

#include "p4_symbolic/bmv2/bmv2.h"

#include <string>

#include "google/protobuf/util/json_util.h"
#include "gutil/status.h"
#include "p4_symbolic/util/io.h"

namespace p4_symbolic {
namespace bmv2 {

absl::StatusOr<P4Program> ParseBmv2JsonFile(const std::string &json_path) {
  ASSIGN_OR_RETURN(std::string file_content, util::ReadFile(json_path));

  P4Program output;
  google::protobuf::util::JsonParseOptions options;
  options.ignore_unknown_fields = true;

  RETURN_IF_ERROR(
      gutil::ToAbslStatus(google::protobuf::util::JsonStringToMessage(
          file_content, &output, options)));

  return output;
}

}  // namespace bmv2
}  // namespace p4_symbolic
