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

#ifndef PINS_TESTS_FORWARDING_PACKET_TEST_UTIL_H_
#define PINS_TESTS_FORWARDING_PACKET_TEST_UTIL_H_

#include <net/ethernet.h>
#include <netinet/in.h>

#include <string>
#include <vector>

#include "absl/base/thread_annotations.h"
#include "absl/container/flat_hash_map.h"
#include "absl/status/statusor.h"
#include "absl/synchronization/mutex.h"
#include "dvaas/test_vector.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/netaddr/mac_address.h"
#include "p4_pdpi/packetlib/packetlib.h"

// Helper library to hold a collection of functions to define a test
// configuration, define a packet, generate a packet etc.
namespace pins {

enum class PacketField {
  kEthernetSrc,
  kEthernetDst,
  kIpSrc,
  kIpDst,
  kHopLimit,
  kDscp,
  kFlowLabelLower16,
  kFlowLabelUpper4,
  kInnerIpSrc,
  kInnerIpDst,
  kInnerHopLimit,
  kInnerDscp,
  kInnerFlowLabelLower16,
  kInnerFlowLabelUpper4,
  kL4SrcPort,
  kL4DstPort,
  kInputPort,
};

// Description of a single test (sequence of packets) that specifies what kind
// of packets we want to send (IPv4 vs IPv6, etc) and which field in the packet
// header has to be varied.
struct TestConfiguration {
  // The field to be modified.
  PacketField field = PacketField::kEthernetSrc;
  // (outer) IPv4 or IPv6?
  bool ipv4 = true;
  // Is this packet encapped?
  bool encapped = false;
  // Inner/encapped header is IPv4 or IPv6?
  bool inner_ipv4 = false;
  // Will this packet be decapped?
  bool decap = false;
};

// The config used for the test and the vector of packets received.
struct TestInputOutput {
  TestConfiguration config;
  // The list of packets received
  std::vector<dvaas::Packet> output;
};

// Holds a map of the input packet raw data to its TestInputOutput.
struct TestData {
  absl::Mutex mutex;
  int total_packets_sent = 0;
  int total_packets_received = 0;
  int total_invalid_packets_received = 0;
  absl::flat_hash_map<std::string, TestInputOutput>
      input_output_per_packet ABSL_GUARDED_BY(mutex);
  // Clears the received packets in the output vector and the send/receive
  // counters.
  void ClearReceivedPackets() ABSL_LOCKS_EXCLUDED(mutex);
};

// Checks wehether this a valid test configuration. Not all configurations are
// valid, e.g. you can't modify the flow label in an IPv4 packet (because there
// is no flow label there).
bool IsValidTestConfiguration(const TestConfiguration &config);

// Returns the ith destination MAC that is used when varying that field.
netaddr::MacAddress GetIthDstMac(int i);

// Returns a human-readable description of a test config.
std::string DescribeTestConfig(const TestConfiguration &config);

// Returns the first 64 characters of test config, padded with '.' if needed.
std::string TestConfigurationToPayload(const TestConfiguration &config);

// Returns the i-th packet for the given test configuration.  The packets all
// follow the requirements of the config (e.g., is this a IPv4 or IPv6 packet),
// and vary in exactly one field (the one specified in the config).
absl::StatusOr<packetlib::Packet>
GenerateIthPacket(const TestConfiguration &config, int index);

} // namespace pins

#endif // PINS_TESTS_FORWARDING_PACKET_UTIL_H_
