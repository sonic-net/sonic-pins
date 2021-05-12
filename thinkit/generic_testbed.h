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

#ifndef GOOGLE_THINKIT_GENERIC_TESTBED_H_
#define GOOGLE_THINKIT_GENERIC_TESTBED_H_

#include <string>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "thinkit/switch.h"
#include "thinkit/test_environment.h"

namespace thinkit {

// HttpResponse represents an HTTP response from an Ixia device.
struct HttpResponse {
  int response_code;
  std::string response;
};

enum class RequestType {
  kGet,
  kPost,
  kPut,
  kDelete,
};

// The GenericTestbed interface represents a testbed with control interface and
// Ixia interface.
class GenericTestbed {
 public:
  virtual ~GenericTestbed() {}

  // Returns the switch (aka system) under test.
  virtual Switch& Sut() = 0;

  // Returns the test environment in which the test is run.
  virtual TestEnvironment& Environment() = 0;

  // Sends a REST request to the Ixia and returns the response.
  virtual absl::StatusOr<HttpResponse> SendRestRequestToIxia(
      RequestType type, absl::string_view url, absl::string_view payload) = 0;
};

}  // namespace thinkit
#endif  // GOOGLE_THINKIT_GENERIC_TESTBED_H_
