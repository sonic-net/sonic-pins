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

#include "gutil/io.h"

#include <cerrno>
#include <fstream>
#include <streambuf>
#include <string>

#include "absl/strings/str_format.h"
#include "gutil/status.h"

namespace gutil {

namespace {

absl::Status ErrorNoToAbsl(const char *operation, const std::string &path) {
  switch (errno) {
    case EACCES:
    case ENOENT:
      return absl::NotFoundError(
          absl::StrFormat("%s: %s", strerror(errno), path));
    default:
      return absl::UnknownError(absl::StrFormat("Cannot %s file %s, errno = %d",
                                                operation, path, errno));
  }
}

}  // namespace

absl::StatusOr<std::string> ReadFile(const std::string &path) {
  std::ifstream f;
  f.open(path.c_str());
  if (f.fail()) {
    return ErrorNoToAbsl("open", path);
  }
  f >> std::noskipws;  // Read whitespaces.
  std::string result(std::istreambuf_iterator<char>(f),
                     (std::istreambuf_iterator<char>()));
  if (f.bad()) {
    return ErrorNoToAbsl("read", path);
  }
  f.close();
  return result;
}

absl::StatusOr<std::vector<std::string>> ReadFileLines(
    const std::string &path) {
  std::ifstream f;
  f.open(path.c_str());
  if (f.fail()) {
    return ErrorNoToAbsl("open", path);
  }
  std::vector<std::string> results;
  std::string line;
  while (std::getline(f, line)) {
    results.push_back(line);
  }
  if (f.bad()) {
    return ErrorNoToAbsl("read", path);
  }
  f.close();
  return results;
}

absl::Status WriteFile(const std::string &content, const std::string &path) {
  std::ofstream f;
  f.open(path.c_str());
  if (f.fail()) {
    return ErrorNoToAbsl("open", path);
  }
  f << content;
  f.close();
  if (f.bad()) {
    return ErrorNoToAbsl("write", path);
  }
  return absl::OkStatus();
}

}  // namespace gutil
