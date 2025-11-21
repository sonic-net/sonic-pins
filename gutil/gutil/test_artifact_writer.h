// Exposes functions to write test artifacts understood by Bazel.

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

#ifndef PINS_GUTIL_TEST_WRITER_H_
#define PINS_GUTIL_TEST_WRITER_H_

#include <fstream>
#include <ios>
#include <string>

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "absl/synchronization/mutex.h"
#include "google/protobuf/message.h"

namespace gutil {

// Abstract base class for storing test artifacts.
class TestArtifactWriter {
 public:
  virtual ~TestArtifactWriter() = default;

  // Stores a test artifact with the specified filename and contents. Overwrites
  // existing files.
  virtual absl::Status StoreTestArtifact(absl::string_view filename,
                                         absl::string_view contents) = 0;
  absl::Status StoreTestArtifact(absl::string_view filename,
                                 const google::protobuf::Message& proto);

  // Appends contents to an existing test artifact with the specified filename.
  // Creates a new file if it doesn't exist.
  virtual absl::Status AppendToTestArtifact(absl::string_view filename,
                                            absl::string_view contents) = 0;
  absl::Status AppendToTestArtifact(absl::string_view filename,
                                    const google::protobuf::Message& proto);
};

// A thread-safe class for storing test artifacts.
//
// Calls to {Store,AppendTo}TestArtifact within a BazelTestArtifactWriter
// object are guaranteed to be thread-safe due to writes being sequential.
//
// NOTE: This class assumes a Bazel test environment! See
// https://docs.bazel.build/versions/main/test-encyclopedia.html#initial-conditions
class BazelTestArtifactWriter : public TestArtifactWriter {
 public:
  // Stores a test artifact with the specified filename and contents. Overwrites
  // existing files.
  absl::Status StoreTestArtifact(absl::string_view filename,
                                 absl::string_view contents)
      ABSL_LOCKS_EXCLUDED(write_mutex_) override;
  using TestArtifactWriter::StoreTestArtifact;  // Inherit second overload.

  // Appends contents to an existing test artifact with the specified filename.
  // Creates a new file if it doesn't exist.
  absl::Status AppendToTestArtifact(absl::string_view filename,
                                    absl::string_view contents)
      ABSL_LOCKS_EXCLUDED(write_mutex_) override;
  using TestArtifactWriter::AppendToTestArtifact;  // Inherit second overload.

 private:
  // Open files are cached to avoid closing them after every append. On certain
  // file systems (e.g. b/111316875) closing files is abnormally slow and this
  // avoids it. However, this approach should also generally be faster.
  absl::flat_hash_map<std::string, std::ofstream> open_file_by_filepath_;
  // The mutex is used to ensure that writes to disk are sequential.
  absl::Mutex write_mutex_;
};

}  // namespace gutil

#endif  // PINS_GUTIL_TEST_WRITER_H_
