// Copyright 2025 Google LLC
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

#ifndef PINS_TESTS_PACKET_CAPTURE_PACKET_CAPTURE_TEST_H_
#define PINS_TESTS_PACKET_CAPTURE_PACKET_CAPTURE_TEST_H_

#include <cstdint>
#include <memory>
#include <optional>
#include <vector>

#include "dvaas/dataplane_validation.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"
#include "p4_infra/packetlib/packetlib.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/mirror_testbed_fixture.h"

namespace pins_test {

// Parameters used by tests that don't require an Ixia.
struct PacketCaptureTestWithoutIxiaParams {
  // Using a shared_ptr because parameterized tests require objects to be
  // copyable.
  std::shared_ptr<thinkit::MirrorTestbedInterface> testbed_interface;
  packetlib::Packet test_packet;
};

// These tests must be run on a mirror testbed.
class PacketCaptureTestWithoutIxia
    : public testing::TestWithParam<PacketCaptureTestWithoutIxiaParams> {
 protected:
  void SetUp() override { GetParam().testbed_interface->SetUp(); }

  thinkit::MirrorTestbed& Testbed() {
    return GetParam().testbed_interface->GetMirrorTestbed();
  }

  void TearDown() override { GetParam().testbed_interface->TearDown(); }
};

// The type of packet to send to the SUT for Packet Capture Tests
enum class PacketCaptureTestPacketType {
  kIcmpv4,
  kIcmpv6,
  kArpRequest,
  kArpResponse,
  kBgp
};

inline std::string PacketCaptureTestPacketTypeToString(
    PacketCaptureTestPacketType packet_type) {
  switch (packet_type) {
    case PacketCaptureTestPacketType::kIcmpv4:
      return "ICMPv4";
    case PacketCaptureTestPacketType::kIcmpv6:
      return "ICMPv6";
    case PacketCaptureTestPacketType::kArpRequest:
      return "ARP_REQUEST";
    case PacketCaptureTestPacketType::kArpResponse:
      return "ARP_RESPONSE";
    case PacketCaptureTestPacketType::kBgp:
      return "BGP";
  }
  return "none";
}

struct ControllerPacketCaptureTestWithoutIxiaParams {
  // Using a shared_ptr because parameterized tests require objects to be
  // copyable.
  std::shared_ptr<thinkit::MirrorTestbedInterface> testbed_interface;
  std::vector<int> vlans_to_be_tested;  // Ingress Packet VLAN IDs to be tested.
  uint32_t cpu_port_id;
  // If provided, installs the P4Info on the SUT. Otherwise, uses the P4Info
  // already on the SUT.
  std::optional<p4::config::v1::P4Info> sut_p4info;
  sai::Instantiation sut_instantiation;
  PacketCaptureTestPacketType packet_type;
  std::string test_name;
  std::shared_ptr<dvaas::DataplaneValidator> validator;
  dvaas::DataplaneValidationParams validation_params;
};

// These tests must be run on a testbed where the SUT is connected
// to a "control device" that can send and received packets.
class ControllerPacketCaptureTestWithoutIxia
    : public testing::TestWithParam<
          ControllerPacketCaptureTestWithoutIxiaParams> {
 protected:
  void SetUp() override { GetParam().testbed_interface->SetUp(); }

  thinkit::MirrorTestbed &Testbed() {
    return GetParam().testbed_interface->GetMirrorTestbed();
  }

  void TearDown() override { GetParam().testbed_interface->TearDown(); }
};

} // namespace pins_test

#endif // PINS_TESTS_PACKET_CAPTURE_PACKET_CAPTURE_TEST_H_
