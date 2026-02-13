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

#include <ios>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "absl/synchronization/mutex.h"
#include "gutil/test_artifact_writer.h"

namespace thinkit {

absl::Status BazelTestEnvironment::StoreTestArtifact(
    absl::string_view filename, absl::string_view contents) {
  return artifact_writer_.StoreTestArtifact(filename, contents);
}
absl::Status BazelTestEnvironment::StoreTestArtifact(
    absl::string_view filename, const google::protobuf::Message& proto) {
  return artifact_writer_.StoreTestArtifact(filename, proto);
}

absl::Status BazelTestEnvironment::AppendToTestArtifact(
    absl::string_view filename, absl::string_view contents) {
  return artifact_writer_.AppendToTestArtifact(filename, contents);
}
absl::Status BazelTestEnvironment::AppendToTestArtifact(
    absl::string_view filename, const google::protobuf::Message& proto) {
  return artifact_writer_.AppendToTestArtifact(filename, proto);
}

}  // namespace thinkit
