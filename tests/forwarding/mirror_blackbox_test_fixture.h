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

#ifndef PINS_TESTS_FORWARDING_MIRROR_BLACKBOX_TEST_FIXTURE_H_
#define PINS_TESTS_FORWARDING_MIRROR_BLACKBOX_TEST_FIXTURE_H_

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "p4_infra/p4_runtime/p4_runtime_session.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/mirror_testbed_fixture.h"

namespace pins_test {

// Fixture for mirror blackbox testing. It performs test specific setup and
// teardown: Creates and initializes a P4RT channel, clears the switch of all
// table entries, and pushes a GNMI config before every test. This gets the
// switch ready to accept programming operations.
class MirrorBlackboxTestFixture : public thinkit::MirrorTestbedFixture {
 public:
  void SetUp() override;

  void TearDown() override;

  p4_runtime::P4RuntimeSession& GetSutP4RuntimeSession() const {
    return *sut_p4rt_session_;
  }

  p4_runtime::P4RuntimeSession& GetControlP4RuntimeSession() const {
    return *control_switch_p4rt_session_;
  }

 private:
  // This test runs on a mirror testbed setup so we open a P4RT connection to
  // both switches.
  std::unique_ptr<p4_runtime::P4RuntimeSession> sut_p4rt_session_;
  std::unique_ptr<p4_runtime::P4RuntimeSession> control_switch_p4rt_session_;
};

}  // namespace pins_test

#endif  // PINS_TESTS_FORWARDING_MIRROR_BLACKBOX_TEST_FIXTURE_H_
