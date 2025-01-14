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

#include "absl/status/status.h"
#include "thinkit/generic_testbed.h"

namespace pins_test {

enum class IpVersion { kIpv4, kIpv6 };
enum class Protocol { kTcp, kUdp };

// Interface to program or clear flows on the SUT of the given `testbed` during
// NSF integration tests.
class FlowProgrammer {
 public:
  virtual ~FlowProgrammer() = default;

  // Programs a predefined flow on the SUT based on the given IP version and
  // protocol.
  virtual absl::Status ProgramFlows(IpVersion ip_version, Protocol protocol,
                                    thinkit::GenericTestbed& testbed) = 0;

  // Clears all flows on the SUT.
  virtual absl::Status ClearFlows(thinkit::GenericTestbed& testbed) = 0;
};

}  // namespace pins_test

#endif  // PINS_TESTS_INTEGRATION_SYSTEM_NSF_INTERFACES_FLOW_PROGRAMMER_H_
