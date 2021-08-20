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

#ifndef PINS_TESTS_FORWARDING_WATCH_PORT_TEST_H_
#define PINS_TESTS_FORWARDING_WATCH_PORT_TEST_H_

#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <thread>  // NOLINT: Need threads (instead of fiber) for upstream code.
#include <vector>

#include "absl/status/status.h"
#include "gtest/gtest.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "tests/forwarding/group_programming_util.h"
#include "tests/forwarding/packet_test_util.h"
#include "thinkit/mirror_testbed_fixture.h"
#include "thinkit/switch.h"

namespace pins {

// Holds the common params needed for watch port test.
struct WatchPortTestParams {
  thinkit::MirrorTestbedInterface* testbed;
  std::string gnmi_config;
  // TODO: Remove port ids from here and derive from gNMI config.
  std::vector<int> port_ids;
};

// WatchPortTestFixture for testing watch port action.
class WatchPortTestFixture
    : public testing::TestWithParam<WatchPortTestParams> {
 protected:
  void SetUp() override;

  void TearDown() override;

  // Returns the P4Info used by the test, for now just Middleblock.
  const p4::config::v1::P4Info& GetP4Info();
  const pdpi::IrP4Info& GetIrP4Info();

  TestData test_data_;
  std::unique_ptr<pdpi::P4RuntimeSession> sut_p4_session_;
  std::unique_ptr<pdpi::P4RuntimeSession> control_p4_session_;
  std::unique_ptr<gnmi::gNMI::StubInterface> control_gnmi_stub_;
  // Stores the receive thread that is created in SetUp() and joined in
  // TearDown(). Accesses control_p4_session_->StreamChannelRead to read
  // packets, which must not be used by other threads.
  std::thread receive_packet_thread_;
};

}  // namespace pins

#endif  // PINS_TESTS_FORWARDING_WATCH_PORT_TEST_H_
