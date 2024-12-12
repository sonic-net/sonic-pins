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

#ifndef PINS_THINKIT_BAZEL_TEST_ENVIRONMENT_H_
#define PINS_THINKIT_BAZEL_TEST_ENVIRONMENT_H_

#include <fstream>
#include <functional>
#include <ios>
#include <string>
#include <utility>
#include <vector>

#include "absl/base/thread_annotations.h"
#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "absl/synchronization/mutex.h"
#include "gutil/test_artifact_writer.h"
#include "thinkit/test_environment.h"

namespace thinkit {

// Simple `thinkit::TestEnvironment` that works well with the Bazel build
// system.
// Calls to {Store,AppendTo}TestArtifact within a BazelTestEnvironment
// object are guaranteed to be thread-safe due to writes being sequential.
class BazelTestEnvironment : public TestEnvironment {
public:
  BazelTestEnvironment() = delete;
  explicit BazelTestEnvironment(
      bool mask_known_failures,
      std::function<void(const std::vector<std::string> &)> set_test_case_ids =
          [](auto) {})
      : mask_known_failures_{mask_known_failures},
        set_test_case_ids_(std::move(set_test_case_ids)) {}

  absl::Status StoreTestArtifact(absl::string_view filename,
                                 absl::string_view contents) override;
  absl::Status StoreTestArtifact(absl::string_view filename,
                                 const google::protobuf::Message &proto);

  absl::Status AppendToTestArtifact(absl::string_view filename,
                                    absl::string_view contents) override;
  absl::Status AppendToTestArtifact(absl::string_view filename,
                                    const google::protobuf::Message &proto);

  bool MaskKnownFailures() { return mask_known_failures_; };

  void SetTestCaseIDs(const std::vector<std::string> &test_case_ids) override {
    set_test_case_ids_(test_case_ids);
  }

private:
  bool mask_known_failures_;
  std::function<void(const std::vector<std::string> &)> set_test_case_ids_;
  gutil::BazelTestArtifactWriter artifact_writer_;
};

} // namespace thinkit

#endif // PINS_THINKIT_BAZEL_TEST_ENVIRONMENT_H_
