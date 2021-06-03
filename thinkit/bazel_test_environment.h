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

#ifndef GOOGLE_THINKIT_BAZEL_TEST_ENVIRONMENT_H_
#define GOOGLE_THINKIT_BAZEL_TEST_ENVIRONMENT_H_

#include <ios>

#include "absl/strings/string_view.h"
#include "absl/synchronization/mutex.h"
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
      std::function<void(absl::string_view)> set_test_case_id = [](auto) {})
      : mask_known_failures_{mask_known_failures},
        set_test_case_id_(std::move(set_test_case_id)) {}

  absl::Status StoreTestArtifact(absl::string_view filename,
                                 absl::string_view contents)
      ABSL_LOCKS_EXCLUDED(write_mutex_) override;
  using TestEnvironment::StoreTestArtifact;  // Inherit protobuf overload which
                                             // calls string_view version.

  absl::Status AppendToTestArtifact(absl::string_view filename,
                                    absl::string_view contents)
      ABSL_LOCKS_EXCLUDED(write_mutex_) override;
  using TestEnvironment::AppendToTestArtifact;  // Inherit protobuf overload
                                                // which calls string_view
                                                // version.

  bool MaskKnownFailures() { return mask_known_failures_; };

  void SetTestCaseID(absl::string_view test_case_id) override {
    set_test_case_id_(test_case_id);
  }

 private:
  bool mask_known_failures_;
  std::function<void(absl::string_view)> set_test_case_id_;
  // The mutex is used to ensure that writes to disk are sequential.
  absl::Mutex write_mutex_;
};

}  // namespace thinkit

#endif  // GOOGLE_THINKIT_BAZEL_TEST_ENVIRONMENT_H_
