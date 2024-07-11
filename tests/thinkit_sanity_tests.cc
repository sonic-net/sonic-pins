// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "tests/thinkit_sanity_tests.h"

#include <stdint.h>

#include <memory>
#include <utility>

#include "absl/status/statusor.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/switch.h"

namespace pins_test {

void TestP4Sessions(thinkit::MirrorTestbed& testbed) {
  // TODO: Remove kDeviceId once device ID is set through gNMI in
  // P4RT app.
  static constexpr uint64_t kDeviceId = 183807201;
  ASSERT_OK_AND_ASSIGN(auto sut_p4runtime_stub,
                       testbed.Sut().CreateP4RuntimeStub());
  EXPECT_OK(
      pdpi::P4RuntimeSession::Create(std::move(sut_p4runtime_stub), kDeviceId));
  ASSERT_OK_AND_ASSIGN(auto control_switch_p4runtime_stub,
                       testbed.ControlSwitch().CreateP4RuntimeStub());
  EXPECT_OK(pdpi::P4RuntimeSession::Create(
      std::move(control_switch_p4runtime_stub), kDeviceId));
}

}  // namespace pins_test
