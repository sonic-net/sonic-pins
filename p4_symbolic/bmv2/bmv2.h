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

#ifndef P4_SYMBOLIC_BMV2_BMV2_H_
#define P4_SYMBOLIC_BMV2_BMV2_H_

#include <string>

#include "gutil/status.h"
#include "p4_symbolic/bmv2/bmv2.pb.h"

namespace p4_symbolic {
namespace bmv2 {

// Reads and parses the bmv2 JSON content (typically the output of p4c) from
// the given file.
// Returns the resulting P4Program instance if successful, or an appropriate
// failure status in case of a badly formatted input file, or if the file
// does not exist.
absl::StatusOr<P4Program> ParseBmv2JsonFile(const std::string &json_path);

// Like `ParseBmv2JsonFile`, but parsing from the given string instead of a
// file.
absl::StatusOr<P4Program> ParseBmv2JsonString(const std::string &json_string);

}  // namespace bmv2
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_BMV2_BMV2_H_
