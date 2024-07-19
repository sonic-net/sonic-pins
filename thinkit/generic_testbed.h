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

#include "absl/container/flat_hash_map.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "thinkit/control_interface.h"
#include "thinkit/proto/generic_testbed.pb.h"
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

// InterfaceInfo represents the mode of an interface and the name of the peer
// interface.
struct InterfaceInfo {
  third_party::pins_infra::thinkit::InterfaceMode interface_mode;
  std::string peer_interface_name;  // Empty if not applicable.
};

// The GenericTestbed interface represents a testbed with control interface and
// Ixia interface.
class GenericTestbed {
 public:
  virtual ~GenericTestbed() {}

  // Returns the switch (aka system) under test.
  virtual Switch& Sut() = 0;

  // Returns the control interface responsible for packet injection and various
  // management operations.
  virtual ControlInterface& Interface() = 0;

  // Returns the test environment in which the test is run.
  virtual TestEnvironment& Environment() = 0;

  // Returns the information for all SUT interfaces.
  virtual absl::flat_hash_map<std::string, InterfaceInfo>
  GetSutInterfaceInfo() = 0;

  // Sends a REST request to the Ixia and returns the response.
  virtual absl::StatusOr<HttpResponse> SendRestRequestToIxia(
      RequestType type, absl::string_view url, absl::string_view payload) = 0;
};

}  // namespace thinkit
#endif  // GOOGLE_THINKIT_GENERIC_TESTBED_H_
