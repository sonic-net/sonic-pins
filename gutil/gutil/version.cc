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

#include "gutil/gutil/version.h"

#include <ostream>
#include <string>
#include <tuple>

#include "absl/log/log.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "gutil/gutil/status.h"
#include "re2/re2.h"

namespace gutil {

namespace {

// Returns the given version as a tuple.
inline constexpr std::tuple<int, int, int> Tupled(Version v) {
  return std::make_tuple(v.major_version, v.minor_version, v.patch_version);
}

}  // namespace

bool operator==(const Version& x, const Version& y) {
  return Tupled(x) == Tupled(y);
}
bool operator!=(const Version& x, const Version& y) {
  return Tupled(x) != Tupled(y);
}
bool operator<=(const Version& x, const Version& y) {
  return Tupled(x) <= Tupled(y);
}
bool operator<(const Version& x, const Version& y) {
  return Tupled(x) < Tupled(y);
}
bool operator>=(const Version& x, const Version& y) {
  return Tupled(x) >= Tupled(y);
}
bool operator>(const Version& x, const Version& y) {
  return Tupled(x) > Tupled(y);
}

absl::StatusOr<Version> ParseVersion(absl::string_view version_string) {
  static const LazyRE2 kSemanticVersionRegex = {R"((\d+).(\d+).(\d+))"};
  Version version;
  if (!RE2::FullMatch(version_string, *kSemanticVersionRegex,
                      &version.major_version, &version.minor_version,
                      &version.patch_version)) {
    return gutil::InvalidArgumentErrorBuilder()
           << "unable to parse '" << version_string
           << "' as a semantic version string; expected string of the form "
              "`MAJOR.MINOR.PATCH`, where each sub-string is a decimal string";
  }
  return version;
}

Version ParseVersionOrDie(absl::string_view version_string) {
  absl::StatusOr<Version> version = ParseVersion(version_string);
  if (!version.ok()) {
    LOG(FATAL) << version.status();  // Crash OK since that's the point of the
                                     // function.
  }
  return std::move(*version);
}

std::string VersionToString(const Version& v) { return absl::StrCat(v); }

std::ostream& operator<<(std::ostream& os, const Version& v) {
  return os << absl::StrCat(v);
}

}  // namespace gutil
