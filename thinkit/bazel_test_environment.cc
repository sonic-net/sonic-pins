// Copyright (c) 2024, Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "thinkit/bazel_test_environment.h"

#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <ios>
#include <ostream>
#include <system_error>  // NOLINT

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "thinkit/test_environment.h"

namespace thinkit {

namespace {

absl::StatusOr<std::string> ArtifactDirectory() {
  // Pick appropriate artifact directory using Bazel environment variables, see
  // https://docs.bazel.build/versions/master/test-encyclopedia.html#initial-conditions
  char* base_dir = std::getenv("TEST_UNDECLARED_OUTPUTS_DIR");
  if (base_dir == nullptr) {
    base_dir = std::getenv("TEST_TMPDIR");
  }
  if (base_dir == nullptr) {
    return gutil::InternalErrorBuilder()
           << "Environment variables TEST_UNDECLARED_OUTPUTS_DIR and "
              "TEST_TMPDIR undefined; is this a Bazel test run?";
  }
  std::string dir = base_dir;
  if (auto* test_info = testing::UnitTest::GetInstance()->current_test_info();
      test_info != nullptr) {
    absl::StrAppend(&dir, "/", test_info->test_case_name(), "/",
                    test_info->name());
  }

  // Ensure the directory exists.
  std::error_code error;
  std::filesystem::create_directories(dir, error);
  if (error) {
    return gutil::InternalErrorBuilder()
           << "failed to create test artifact directory '" << dir
           << "': " << error;
  }
  return dir;
}

absl::Status WriteToTestArtifact(absl::string_view filename,
                                 absl::string_view contents,
                                 std::ios_base::openmode mode) {
  ASSIGN_OR_RETURN(std::string directory, ArtifactDirectory());
  std::string filepath = absl::StrCat(directory, "/", filename);
  std::ofstream file;
  file.open(filepath, mode);
  if (!file.is_open()) {
    return gutil::InternalErrorBuilder()
           << "unable to open test artifact file: '" << filepath << "'";
  }
  file << contents;
  file.close();
  if (file.good()) return absl::OkStatus();
  return gutil::InternalErrorBuilder()
         << "failed to store test artifact: '" << filepath << "'";
}

}  // namespace

absl::Status BazelTestEnvironment::StoreTestArtifact(
    absl::string_view filename, absl::string_view contents) {
  return WriteToTestArtifact(filename, contents, std::ios_base::trunc);
}

absl::Status BazelTestEnvironment::AppendToTestArtifact(
    absl::string_view filename, absl::string_view contents) {
  return WriteToTestArtifact(filename, contents, std::ios_base::app);
}

}  // namespace thinkit
