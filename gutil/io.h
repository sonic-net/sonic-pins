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

#ifndef P4_SYMBOLIC_UTIL_IO_H_
#define P4_SYMBOLIC_UTIL_IO_H_

#include <string>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "gutil/status.h"

namespace gutil {

// Reads the entire content of the file and returns it (or an error status).
absl::StatusOr<std::string> ReadFile(const std::string &path);

// Reads the entire content of the file and returns as a vector of individual
// lines (or an error status).
absl::StatusOr<std::vector<std::string>> ReadFileLines(const std::string &path);

// Writes the content of the string to the file.
absl::Status WriteFile(const std::string &content, const std::string &path);

} // namespace gutil

#endif // P4_SYMBOLIC_UTIL_IO_H_
