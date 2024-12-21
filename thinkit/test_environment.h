// Copyright (c) 2020, Google Inc.
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

#ifndef THINKIT_TEST_ENVIRONMENT_H_
#define THINKIT_TEST_ENVIRONMENT_H_

#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "google/protobuf/message.h"
#include "thinkit/proto/metrics.pb.h"

namespace thinkit {

// The TestEnvironment interface represents the underlying test infrastructure
// to which a test might want to pass additional debug information to.
class TestEnvironment {
public:
  virtual ~TestEnvironment() {}

  // Stores a test artifact with the specified filename and contents. Overwrites
  // existing files.
  virtual absl::Status StoreTestArtifact(absl::string_view filename,
                                         absl::string_view contents) = 0;
  absl::Status StoreTestArtifact(absl::string_view filename,
                                 const google::protobuf::Message &proto) {
    return StoreTestArtifact(filename, proto.DebugString());
  }

  // Appends contents to an existing test artifact with the specified filename.
  // Creates a new file if it doesn't exist.
  virtual absl::Status AppendToTestArtifact(absl::string_view filename,
                                            absl::string_view contents) = 0;
  absl::Status AppendToTestArtifact(absl::string_view filename,
                                    const google::protobuf::Message &proto) {
    return AppendToTestArtifact(filename,
                                absl::StrCat(proto.DebugString(), "\n"));
  }

  // Should known failures be masked, or should the test fail instead?
  virtual bool MaskKnownFailures() = 0;

  // Set the `test_case_id` for use by tracking tools.
  virtual void SetTestCaseID(absl::string_view test_case_id) {
    SetTestCaseIDs({std::string(test_case_id)});
  }

  // Set the `test_case_ids` for use by tracking tools.
  virtual void SetTestCaseIDs(const std::vector<std::string> &test_case_ids) {}

  // Record a group of metrics for use by tracking tools.
  virtual void RecordMetrics(const MetricGroup &metric_group) {}
};

} // namespace thinkit

#endif // THINKIT_TEST_ENVIRONMENT_H_
