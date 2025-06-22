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

#ifndef PINS_TESTS_INTEGRATION_SYSTEM_NSF_FLOW_PROGRAMMERS_FUZZER_REPLAY_PROGRAMMER_H_
#define PINS_TESTS_INTEGRATION_SYSTEM_NSF_FLOW_PROGRAMMERS_FUZZER_REPLAY_PROGRAMMER_H_

#include "absl/status/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "tests/integration/system/nsf/interfaces/flow_programmer.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "thinkit/ssh_client.h"

namespace pins_test {

class FuzzerReplayProgrammer : public FlowProgrammer {
 public:
   absl::Status ProgramFlows(const p4::config::v1::P4Info &p4_info,
                             Testbed &testbed,
                             thinkit::SSHClient &ssh_client) override {
     return absl::OkStatus();
   };
  absl::Status ClearFlows(Testbed& testbed) override {
    return absl::OkStatus();
  };
};

}  // namespace pins_test

#endif  // PINS_TESTS_INTEGRATION_SYSTEM_NSF_FLOW_PROGRAMMERS_FUZZER_REPLAY_PROGRAMMER_H_
