/* Copyright 2024 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

#include "gutil/test_artifact_writer.h"

#include <cstdlib>
#include <filesystem>  // NOLINT: open source code
#include <fstream>
#include <ios>
#include <string>
#include <system_error>  // NOLINT: open source code

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/synchronization/mutex.h"
#include "google/protobuf/message.h"
#include "gtest/gtest.h"
#include "gutil/proto.h"
#include "gutil/status.h"

namespace gutil {
namespace {

// Gets a Bazel artifact directory based on the currently running test.
absl::StatusOr<std::string> ArtifactDirectory() {
  // Pick appropriate artifact directory using Bazel environment variables, see
  // https://docs.bazel.build/versions/main/test-encyclopedia.html#initial-conditions
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

// Writes an artifact with `contents` to `filename` under an artifact directory
// determined by the currently running test. The mode to write the contents
// under is determined by `mode` supporting e.g. `std::ios_base::trunc` or
// `std::ios_base::app`.
// `open_file_by_filepath` is used to continue to use the same file descriptor,
// instead of creating a new one, when appending.
absl::Status WriteToTestArtifact(
    absl::string_view filename, absl::string_view contents,
    std::ios_base::openmode mode,
    absl::flat_hash_map<std::string, std::ofstream>& open_file_by_filepath) {
  ASSIGN_OR_RETURN(std::string directory, ArtifactDirectory());
  std::string filepath = absl::StrCat(directory, "/", filename);
  // Note that pointer-stability of values is not a concern here because the
  // reference is local and nothing is added to the map while the reference is
  // live.
  std::ofstream& file = open_file_by_filepath[filepath];
  if (file.is_open() && mode == std::ios_base::trunc) {
    // If we have an open file descriptor and we want to truncate the file, then
    // we close it and reopen it in truncation mode.
    file.close();
  }
  // If the file is not open, then we just want to open it in the given mode.
  if (!file.is_open()) {
    file.open(filepath, mode);
    // If the file is still not open, we have a problem.
    if (!file.is_open()) {
      return gutil::InternalErrorBuilder()
             << "unable to open test artifact file: '" << filepath << "'";
    }
  }
  file << contents;

  // We flush the contents to persist them, but leave the file open so that we
  // can continue to append to it.
  file.flush();
  if (file.good()) return absl::OkStatus();
  return gutil::InternalErrorBuilder()
         << "failed to store test artifact: '" << filepath << "'";
}

}  // namespace

// -- TestArtifactWriter -------------------------------------------------------

absl::Status TestArtifactWriter::StoreTestArtifact(
    absl::string_view filename, const google::protobuf::Message& proto) {
  return StoreTestArtifact(filename, PrintTextProto(proto));
}
absl::Status TestArtifactWriter::AppendToTestArtifact(
    absl::string_view filename, const google::protobuf::Message& proto) {
  return AppendToTestArtifact(filename,
                              absl::StrCat(PrintTextProto(proto), "\n"));
}

// -- BazelTestArtifactWriter --------------------------------------------------

absl::Status BazelTestArtifactWriter::StoreTestArtifact(
    absl::string_view filename, absl::string_view contents) {
  absl::MutexLock lock(&this->write_mutex_);
  return WriteToTestArtifact(filename, contents, std::ios_base::trunc,
                             open_file_by_filepath_);
}
absl::Status BazelTestArtifactWriter::AppendToTestArtifact(
    absl::string_view filename, absl::string_view contents) {
  absl::MutexLock lock(&this->write_mutex_);
  return WriteToTestArtifact(filename, contents, std::ios_base::app,
                             open_file_by_filepath_);
}

}  // namespace gutil
