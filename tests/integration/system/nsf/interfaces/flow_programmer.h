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

#ifndef PINS_TESTS_INTEGRATION_SYSTEM_NSF_INTERFACES_FLOW_PROGRAMMER_H_
#define PINS_TESTS_INTEGRATION_SYSTEM_NSF_INTERFACES_FLOW_PROGRAMMER_H_

#include <optional>
#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "p4/config/v1/p4info.pb.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "thinkit/ssh_client.h"

namespace pins_test {

// Interface to program or clear flows on the SUT of the given `testbed` during
// NSF integration tests.
//
// Note: The caller is responsible for ensuring that exact same testbed is
// passed throughout the test.
class FlowProgrammer {
 public:
  virtual ~FlowProgrammer() = default;

  // Programs predefined flows on the SUT. Optionally returns an updated gNMI
  // config.
  virtual absl::StatusOr<std::optional<std::string>>
  ProgramFlows(const p4::config::v1::P4Info &p4_info, Testbed &testbed,
               thinkit::SSHClient &ssh_client) = 0;

  // Clears all flows on the SUT.
  virtual absl::Status ClearFlows(Testbed& testbed) = 0;
};

}  // namespace pins_test

#endif  // PINS_TESTS_INTEGRATION_SYSTEM_NSF_INTERFACES_FLOW_PROGRAMMER_H_
