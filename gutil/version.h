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

#ifndef GOOGLE_GUTIL_VERSION_H_
#define GOOGLE_GUTIL_VERSION_H_

#include <ostream>

#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"

namespace gutil {

// Semantic version number (see https://semver.org/), consisting of:
// - `major_version` - incremented when making breaking API changes.
// - `minor_version` - incremented when adding functionality in
//                     backward-compatible manner.
// - `patch_version` - incremented when making backward-compatible bug fixes.
//
// We don't support extensions such as pre-release and build metadata labels at
// this time.
struct Version {
  int major_version = 0;
  int minor_version = 0;
  int patch_version = 0;
};

// Parses semantic version string of the form `MAJOR.MINOR.PATCH`, where each
// of `MAJOR`, `MINOR`, and `PATCH` is an unsigned decimal string.
absl::StatusOr<Version> ParseVersion(absl::string_view version_string);

// Returns semantic version string of the form `MAJOR.MINOR.PATCH`.
std::string VersionToString(const Version& v);

// Pretty printer.
std::ostream& operator<<(std::ostream& os, const Version& v);

// Absl pretty printer (https://abseil.io/blog/20221115-stringify).
template <class Sink>
void AbslStringify(Sink& sink, const Version& v);

// Comparison operators.
bool operator==(const Version& x, const Version& y);
bool operator!=(const Version& x, const Version& y);
bool operator<=(const Version& x, const Version& y);
bool operator<(const Version& x, const Version& y);
bool operator>=(const Version& x, const Version& y);
bool operator>(const Version& x, const Version& y);

// -- END OF PUBLIC INTERFACE -- implementation details follow -----------------

template <class Sink>
void AbslStringify(Sink& sink, const Version& v) {
  absl::Format(&sink, "%d.%d.%d", v.major_version, v.minor_version,
               v.patch_version);
}

}  // namespace gutil

#endif  // GOOGLE_GUTIL_VERSION_H_
