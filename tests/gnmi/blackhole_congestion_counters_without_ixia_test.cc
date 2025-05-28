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

#include "tests/gnmi/blackhole_congestion_counters_without_ixia_test.h"

#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/optional.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "include/nlohmann/json.hpp"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/utils/generic_testbed_utils.h"
#include "lib/utils/json_utils.h"
#include "p4_infra/netaddr/ipv4_address.h"
#include "p4_infra/netaddr/ipv6_address.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.pb.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "thinkit/control_device.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/generic_testbed_fixture.h"
#include "thinkit/proto/generic_testbed.pb.h"
#include "thinkit/switch.h"

namespace pins_test {
namespace {

using ::nlohmann::json;

const sai::Ipv4Lpm kIpv4Lpm = {.dst_ip = netaddr::Ipv4Address(10, 10, 20, 0),
                               .prefix_len = 24};
const sai::Ipv6Lpm kIpv6Lpm = {.dst_ip = netaddr::Ipv6Address(0xF105, 0x102),
                               .prefix_len = 64};
const sai::IpForwardingParams kIpForwardingParams = {.ipv4_lpm = kIpv4Lpm,
                                                     .ipv6_lpm = kIpv6Lpm};
constexpr absl::string_view kIpv4DstIpForL3Hit = "10.10.20.10";
constexpr absl::string_view kIpv4DstIpForL3Miss = "10.10.30.10";
constexpr absl::string_view kIpv6DstIpForL3Hit = "F105:0102::2356";
constexpr absl::string_view kIpv6DstIpForL3Miss = "F205:102::9845";

constexpr int kDecimalToMilliPercent = 1e5;
constexpr int kLpmMissesThresh = 10;
constexpr double kInDiscardsRateThresh = 0.05;
constexpr double kOutDiscardsRateThresh = 0.05;
constexpr uint64_t kInDiscardsRateThreshMilliPercent =
    kInDiscardsRateThresh * kDecimalToMilliPercent;
constexpr uint64_t kOutDiscardsRateThreshMilliPercent =
    kOutDiscardsRateThresh * kDecimalToMilliPercent;
constexpr int kMinInPacketsThresh = 100;
constexpr int kMinOutPacketsThresh = 100;
constexpr int kEccSingleBitErrorsThresh = 0;
constexpr int kRecoveredParityErrorsThresh = 0;

const char kOpenConfigSystemParseKey[] = "openconfig-system:system";
const char kPinsDiagParseKey[] = "diag:diag";

// Takes a `gnmi_config` from the config generator and returns a modified
// version that sets up blackhole and congestion related configs and thresholds
// for the testbed. If the testbed does not support blackhole and congestion
// monitoring, returns an error status.
absl::StatusOr<std::string> SetUpBlackholeCongestionConfig(
    absl::string_view gnmi_config) {
  ASSIGN_OR_RETURN(json gnmi_config_json, json_yang::ParseJson(gnmi_config));

  // Gets the switch-level and port-level configs.
  json& switch_config =
      gnmi_config_json[kOpenConfigSystemParseKey][kPinsDiagParseKey]["config"];
  json& port_profiles =
      gnmi_config_json[kOpenConfigSystemParseKey][kPinsDiagParseKey]
                      ["port-profiles"]["port-profile"];

  if (switch_config.empty() || port_profiles.empty()) {
    return absl::NotFoundError(
        "Blackhole and congestion monitoring not supported on testbed: Failed "
        "to get switch-level or port-level configs.");
  }

  // Updates switch-level configs.
  switch_config["blackhole-monitoring-enable"] = true;
  switch_config["congestion-monitoring-enable"] = true;
  switch_config["ecc-single-bit-errors-threshold"] = kEccSingleBitErrorsThresh;
  switch_config["recovered-parity-errors-threshold"] =
      kRecoveredParityErrorsThresh;
  switch_config["lpm-misses-threshold"] = kLpmMissesThresh;

  // Updates port-level configs.
  for (json& port_profile : port_profiles) {
    port_profile["config"]["in-discards-rate-threshold"] =
        kInDiscardsRateThreshMilliPercent;
    port_profile["config"]["out-discards-rate-threshold"] =
        kOutDiscardsRateThreshMilliPercent;
    port_profile["config"]["min-incoming-pkt-threshold"] = kMinInPacketsThresh;
    port_profile["config"]["min-outgoing-pkt-threshold"] = kMinOutPacketsThresh;
  }

  return json_yang::DumpJson(gnmi_config_json);
}

// Packet proto messages sent from control switch to SUT.
constexpr absl::string_view kIpv4TestPacket = R"pb(
  headers {
    ethernet_header {
      ethernet_destination: "00:1A:11:17:5F:80"
      ethernet_source: "00:01:02:03:04:05"
      ethertype: "0x0800"
    }
  }
  headers {
    ipv4_header {
      version: "0x4"
      ihl: "0x5"
      dscp: "0x03"
      ecn: "0x0"
      identification: "0x0000"
      flags: "0x0"
      fragment_offset: "0x0000"
      ttl: "0x20"
      protocol: "0x11"
      ipv4_source: "1.2.3.4"
      ipv4_destination: "$0"
    }
  }
  headers { udp_header { source_port: "0x0000" destination_port: "0x0000" } }
  payload: "Basic IPv4 test packet")pb";

constexpr absl::string_view kIpv6TestPacket = R"pb(
  headers {
    ethernet_header {
      ethernet_destination: "00:1A:11:17:5F:80"
      ethernet_source: "00:01:02:03:04:05"
      ethertype: "0x86dd"
    }
  }
  headers {
    ipv6_header {
      dscp: "0x03"
      ecn: "0x0"
      flow_label: "0x00000"
      next_header: "0xfd"  # Reserved for experimentation.
      hop_limit: "0x40"
      ipv6_source: "2001:db8:0:12::1"
      ipv6_destination: "$0"
    }
  }
  payload: "Basic IPv6 test packet")pb";

absl::StatusOr<std::string> MakeTestPacket(sai::IpVersion ip_version,
                                           absl::string_view dst_ip) {
  packetlib::Packet test_packet;
  if (ip_version == sai::IpVersion::kIpv4) {
    test_packet = gutil::ParseProtoOrDie<packetlib::Packet>(
        absl::Substitute(kIpv4TestPacket, dst_ip));
  } else {
    test_packet = gutil::ParseProtoOrDie<packetlib::Packet>(
        absl::Substitute(kIpv6TestPacket, dst_ip));
  }
  LOG(INFO) << "Test packet to send: " << test_packet.DebugString();
  return packetlib::SerializePacket(test_packet);
}

// Send packets from control switch to SUT.
absl::Status SendPackets(thinkit::ControlDevice& control_device,
                         absl::string_view control_port,
                         sai::IpVersion ip_version, absl::string_view dst_ip,
                         uint32_t packets_count) {
  // Make test packet.
  ASSIGN_OR_RETURN(std::string test_packet, MakeTestPacket(ip_version, dst_ip));

  // Send packet to SUT.
  for (uint32_t i = 0; i < packets_count; ++i) {
    RETURN_IF_ERROR(control_device.SendPacket(control_port, test_packet))
        << "failed to inject the packet.";
  }
  LOG(INFO) << "Successfully sent " << packets_count << " packets.";
  return absl::OkStatus();
}

TEST_P(BlackholeCongestionCountersWithoutIxiaTestFixture,
       TestIpv4LpmMissesAboveThreshIncrementBlackholeLpmMissCounters) {
  constexpr uint32_t kLpmMissesCount = kLpmMissesThresh + 5;

  ASSERT_OK_AND_ASSIGN(LpmMissCounters lpm_miss_counters,
                       TriggerLpmMisses(sai::IpVersion::kIpv4, kLpmMissesCount,
                                        /*lpm_hit_packets_count=*/0));

  // Check the changes are as expected.
  EXPECT_EQ(lpm_miss_counters.port_in_packets, kLpmMissesCount);
  EXPECT_GE(lpm_miss_counters.switch_blackhole_lpm_miss_events, 1);
  EXPECT_GE(lpm_miss_counters.switch_blackhole_events, 1);
}

TEST_P(BlackholeCongestionCountersWithoutIxiaTestFixture,
       TestIpv6LpmMissesAboveThreshIncrementBlackholeLpmMissCounters) {
  constexpr uint32_t kLpmMissesCount = kLpmMissesThresh + 5;

  ASSERT_OK_AND_ASSIGN(LpmMissCounters lpm_miss_counters,
                       TriggerLpmMisses(sai::IpVersion::kIpv6, kLpmMissesCount,
                                        /*lpm_hit_packets_count=*/0));

  // Check the changes are as expected.
  EXPECT_EQ(lpm_miss_counters.port_in_packets, kLpmMissesCount);
  EXPECT_GE(lpm_miss_counters.switch_blackhole_lpm_miss_events, 1);
  EXPECT_GE(lpm_miss_counters.switch_blackhole_events, 1);
}

TEST_P(BlackholeCongestionCountersWithoutIxiaTestFixture,
       TestIpv4LpmMissesBelowThreshNotIncrementBlackholeLpmMissCounters) {
  constexpr uint32_t kLpmMissesCount = kLpmMissesThresh - 5;

  ASSERT_OK_AND_ASSIGN(LpmMissCounters lpm_miss_counters,
                       TriggerLpmMisses(sai::IpVersion::kIpv4, kLpmMissesCount,
                                        /*lpm_hit_packets_count=*/0));

  // Check the changes are as expected.
  EXPECT_EQ(lpm_miss_counters.port_in_packets, kLpmMissesCount);
  EXPECT_EQ(lpm_miss_counters.switch_blackhole_lpm_miss_events, 0);
  EXPECT_EQ(lpm_miss_counters.switch_blackhole_events, 0);
}

TEST_P(BlackholeCongestionCountersWithoutIxiaTestFixture,
       TestIpv6LpmMissesBelowThreshNotIncrementBlackholeLpmMissCounters) {
  constexpr uint32_t kLpmMissesCount = kLpmMissesThresh - 5;

  ASSERT_OK_AND_ASSIGN(LpmMissCounters lpm_miss_counters,
                       TriggerLpmMisses(sai::IpVersion::kIpv6, kLpmMissesCount,
                                        /*lpm_hit_packets_count=*/0));

  // Check the changes are as expected.
  EXPECT_EQ(lpm_miss_counters.port_in_packets, kLpmMissesCount);
  EXPECT_EQ(lpm_miss_counters.switch_blackhole_lpm_miss_events, 0);
  EXPECT_EQ(lpm_miss_counters.switch_blackhole_events, 0);
}

TEST_P(BlackholeCongestionCountersWithoutIxiaTestFixture,
       TestInDiscardsAboveThreshIncrementBlackholeInDiscardCounters) {
  constexpr double kInDiscardsRate = kInDiscardsRateThresh + 0.03;
  constexpr uint32_t kInPacketsCount = kMinInPacketsThresh + 50;
  constexpr uint32_t kLpmMissesCount = kInPacketsCount * kInDiscardsRate;
  constexpr uint32_t kLpmHitsCount = kInPacketsCount - kLpmMissesCount;

  // Use LPM misses to trigger in-discard events.
  ASSERT_OK_AND_ASSIGN(
      LpmMissCounters lpm_miss_counters,
      TriggerLpmMisses(sai::IpVersion::kIpv4, kLpmMissesCount, kLpmHitsCount));

  // Check the changes are as expected.
  EXPECT_EQ(lpm_miss_counters.port_in_packets, kLpmMissesCount + kLpmHitsCount);
  EXPECT_EQ(lpm_miss_counters.port_in_discards, kLpmMissesCount);
  EXPECT_GE(lpm_miss_counters.switch_blackhole_in_discard_events, 1);
  EXPECT_GE(lpm_miss_counters.switch_blackhole_events, 1);
}

TEST_P(BlackholeCongestionCountersWithoutIxiaTestFixture,
       TestInDiscardsBelowThreshNotIncrementBlackholeInDiscardCounters) {
  constexpr double kInDiscardsRate = kInDiscardsRateThresh - 0.03;
  constexpr uint32_t kInPacketsCount = kMinInPacketsThresh + 50;
  constexpr uint32_t kLpmMissesCount = kInPacketsCount * kInDiscardsRate;
  constexpr uint32_t kLpmHitsCount = kInPacketsCount - kLpmMissesCount;

  // Use LPM misses to trigger in-discard events.
  ASSERT_OK_AND_ASSIGN(
      LpmMissCounters lpm_miss_counters,
      TriggerLpmMisses(sai::IpVersion::kIpv4, kLpmMissesCount, kLpmHitsCount));

  // Check the changes are as expected.
  EXPECT_EQ(lpm_miss_counters.port_in_packets, kLpmMissesCount + kLpmHitsCount);
  EXPECT_EQ(lpm_miss_counters.port_in_discards, kLpmMissesCount);
  EXPECT_EQ(lpm_miss_counters.switch_blackhole_in_discard_events, 0);
  EXPECT_EQ(lpm_miss_counters.switch_blackhole_events, 0);
}

TEST_P(BlackholeCongestionCountersWithoutIxiaTestFixture,
       TestPacketCountBelowThreshNotIncrementBlackholeInDiscardCounters) {
  constexpr double kInDiscardsRate = kInDiscardsRateThresh + 0.03;
  constexpr uint32_t kInPacketsCount = kMinInPacketsThresh - 50;
  constexpr uint32_t kLpmMissesCount = kInPacketsCount * kInDiscardsRate;
  constexpr uint32_t kLpmHitsCount = kInPacketsCount - kLpmMissesCount;

  // Use LPM misses to trigger in-discard events.
  ASSERT_OK_AND_ASSIGN(
      LpmMissCounters lpm_miss_counters,
      TriggerLpmMisses(sai::IpVersion::kIpv4, kLpmMissesCount, kLpmHitsCount));

  // Check the changes are as expected.
  EXPECT_EQ(lpm_miss_counters.port_in_packets, kLpmMissesCount + kLpmHitsCount);
  EXPECT_EQ(lpm_miss_counters.port_in_discards, kLpmMissesCount);
  EXPECT_EQ(lpm_miss_counters.switch_blackhole_in_discard_events, 0);
  EXPECT_EQ(lpm_miss_counters.switch_blackhole_events, 0);
}

TEST_P(BlackholeCongestionCountersWithoutIxiaTestFixture,
       TestAclDropAboveThreshIncrementBlackholeOutDiscardsCounters) {
  constexpr double kOutDiscardsRate = kOutDiscardsRateThresh + 0.03;
  constexpr uint32_t kOutPacketsCount = kMinOutPacketsThresh + 50;
  constexpr uint32_t kOutDiscardsCount = kOutPacketsCount * kOutDiscardsRate;

  ASSERT_OK_AND_ASSIGN(OutDiscardCounters out_discard_counters,
                       TriggerOutDiscards(kOutDiscardsCount, kOutPacketsCount));

  // Check the changes are as expected.
  EXPECT_GE(out_discard_counters.port_blackhole_out_discard_events, 1);
  EXPECT_GE(out_discard_counters.switch_blackhole_out_discard_events, 1);
  EXPECT_GE(out_discard_counters.switch_blackhole_events, 1);
}

TEST_P(BlackholeCongestionCountersWithoutIxiaTestFixture,
       TestAclDropBelowThreshNotIncrementOutDiscardsCounters) {
  constexpr double kOutDiscardsRate = kOutDiscardsRateThresh - 0.03;
  constexpr uint32_t kOutPacketsCount = kMinOutPacketsThresh + 50;
  constexpr uint32_t kOutDiscardsCount = kOutPacketsCount * kOutDiscardsRate;

  ASSERT_OK_AND_ASSIGN(OutDiscardCounters out_discard_counters,
                       TriggerOutDiscards(kOutDiscardsCount, kOutPacketsCount));

  // Check the changes are as expected.
  EXPECT_EQ(out_discard_counters.port_blackhole_out_discard_events, 0);
  EXPECT_EQ(out_discard_counters.switch_blackhole_out_discard_events, 0);
  EXPECT_EQ(out_discard_counters.switch_blackhole_events, 0);
}

TEST_P(BlackholeCongestionCountersWithoutIxiaTestFixture,
       TestAclDropWithLowTrafficNotIncrementOutDiscardsCounters) {
  constexpr uint32_t kOutPacketsCount = kMinOutPacketsThresh - 50;
  constexpr uint32_t kOutDiscardsCount = kOutPacketsCount;

  ASSERT_OK_AND_ASSIGN(OutDiscardCounters out_discard_counters,
                       TriggerOutDiscards(kOutDiscardsCount, kOutPacketsCount));

  // Check the changes are as expected.
  EXPECT_EQ(out_discard_counters.port_blackhole_out_discard_events, 0);
  EXPECT_EQ(out_discard_counters.switch_blackhole_out_discard_events, 0);
  EXPECT_EQ(out_discard_counters.switch_blackhole_events, 0);
}

}  // namespace

void BlackholeCongestionCountersWithoutIxiaTestFixture::SetUp() {
  thinkit::GenericTestbedFixture<
      BlackholeCongestionCountersWithoutIxiaTestFixtureParams>::SetUp();
  thinkit::TestRequirements requirements =
      gutil::ParseProtoOrDie<thinkit::TestRequirements>(
          R"pb(interface_requirements {
                 count: 1
                 interface_mode: CONTROL_INTERFACE
               })pb");

  ASSERT_OK_AND_ASSIGN(generic_testbed_,
                       GetTestbedWithRequirements(requirements));

  ASSERT_OK_AND_ASSIGN(std::string blackhole_congestion_config,
                       SetUpBlackholeCongestionConfig(GetParam().gnmi_config));
  ASSERT_OK(generic_testbed_->Environment().StoreTestArtifact(
      "gnmi_config.txt", GetParam().gnmi_config));
  ASSERT_OK(generic_testbed_->Environment().StoreTestArtifact(
      "blackhole_congestion_config.txt", blackhole_congestion_config));

  // Hook up to gNMI.
  ASSERT_OK_AND_ASSIGN(gnmi_stub_, generic_testbed_->Sut().CreateGnmiStub());

  // Set up P4 Runtime session.
  ASSERT_OK_AND_ASSIGN(sut_p4_session_,
                       ConfigureSwitchAndReturnP4RuntimeSession(
                           generic_testbed_->Sut(), blackhole_congestion_config,
                           GetParam().p4_info));

  ASSERT_OK_AND_ASSIGN(control_links_,
                       GetUpLinks(GetAllControlLinks, *generic_testbed_));
  ASSERT_FALSE(control_links_.empty())
      << "Need at least 1 SUT interface to test";
}

void BlackholeCongestionCountersWithoutIxiaTestFixture::TearDown() {
  // Restores the gNMI config and clears table entries.
  ASSERT_OK(PushGnmiConfig(generic_testbed_->Sut(), GetParam().gnmi_config));
  ASSERT_OK(pdpi::ClearEntities(*sut_p4_session_));
  ASSERT_OK(sut_p4_session_->Finish());
  thinkit::GenericTestbedFixture<
      BlackholeCongestionCountersWithoutIxiaTestFixtureParams>::TearDown();
}

absl::StatusOr<LpmMissCounters>
BlackholeCongestionCountersWithoutIxiaTestFixture::TriggerLpmMisses(
    sai::IpVersion ip_version, uint32_t lpm_miss_packets_count,
    uint32_t lpm_hit_packets_count) {
  const std::string control_interface = control_links_[0].peer_interface;
  const std::string sut_interface = control_links_[0].sut_interface;

  absl::flat_hash_map<std::string, std::string> port_id_by_interface;
  ASSIGN_OR_RETURN(port_id_by_interface,
                   GetAllInterfaceNameToPortId(*gnmi_stub_));
  ASSIGN_OR_RETURN(const std::string sut_port_id,
                   gutil::FindOrStatus(port_id_by_interface, sut_interface));

  thinkit::ControlDevice& control_device = generic_testbed_->ControlDevice();

  RETURN_IF_ERROR(pdpi::ClearEntities(*sut_p4_session_));
  RETURN_IF_ERROR(sai::EntryBuilder()
                      .AddEntriesForwardingIpPacketsToGivenPort(
                          sut_port_id, kIpForwardingParams)
                      .LogPdEntries()
                      .InstallDedupedEntities(*sut_p4_session_));

  // Read some initial counters via gNMI from the SUT.
  ASSIGN_OR_RETURN(
      const uint64_t initial_port_in_pkts,
      GetInterfaceCounter("in-pkts", sut_interface, gnmi_stub_.get()));
  ASSIGN_OR_RETURN(
      const uint64_t initial_port_in_discards,
      GetInterfaceCounter("in-discards", sut_interface, gnmi_stub_.get()));
  ASSIGN_OR_RETURN(
      const BlackholeSwitchCounters initial_blackhole_switch_counters,
      GetBlackholeSwitchCounters(*gnmi_stub_));

  LOG(INFO) << "Sending test packets on port: " << control_interface;
  if (ip_version == sai::IpVersion::kIpv4) {
    RETURN_IF_ERROR(SendPackets(control_device, control_interface, ip_version,
                                kIpv4DstIpForL3Miss, lpm_miss_packets_count));
    RETURN_IF_ERROR(SendPackets(control_device, control_interface, ip_version,
                                kIpv4DstIpForL3Hit, lpm_hit_packets_count));
  } else {
    RETURN_IF_ERROR(SendPackets(control_device, control_interface, ip_version,
                                kIpv6DstIpForL3Miss, lpm_miss_packets_count));
    RETURN_IF_ERROR(SendPackets(control_device, control_interface, ip_version,
                                kIpv6DstIpForL3Hit, lpm_hit_packets_count));
  }

  // Wait some time before capturing the port stats.
  absl::SleepFor(absl::Seconds(15));

  // Re-read the same counters via GNMI from the SUT.
  ASSIGN_OR_RETURN(
      const uint64_t final_port_in_pkts,
      GetInterfaceCounter("in-pkts", sut_interface, gnmi_stub_.get()));
  ASSIGN_OR_RETURN(
      const uint64_t final_port_in_discards,
      GetInterfaceCounter("in-discards", sut_interface, gnmi_stub_.get()));
  ASSIGN_OR_RETURN(
      const BlackholeSwitchCounters final_blackhole_switch_counters,
      GetBlackholeSwitchCounters(*gnmi_stub_));

  // Compute the change for each counter.
  const uint64_t port_in_pkts_delta = final_port_in_pkts - initial_port_in_pkts;
  const uint64_t port_in_discards_delta =
      final_port_in_discards - initial_port_in_discards;
  const BlackholeSwitchCounters blackhole_switch_delta =
      final_blackhole_switch_counters - initial_blackhole_switch_counters;

  return LpmMissCounters{
      .port_in_packets = port_in_pkts_delta,
      .port_in_discards = port_in_discards_delta,
      .switch_blackhole_lpm_miss_events =
          blackhole_switch_delta.lpm_miss_events,
      .switch_blackhole_in_discard_events =
          blackhole_switch_delta.in_discard_events,
      // Sometimes fec_not_correctable_events occur which the test can't
      // control, so subtract those from the switch blackhole counter.
      .switch_blackhole_events =
          blackhole_switch_delta.blackhole_events -
          blackhole_switch_delta.fec_not_correctable_events,
  };
}

absl::StatusOr<OutDiscardCounters>
BlackholeCongestionCountersWithoutIxiaTestFixture::TriggerOutDiscards(
    uint32_t out_discards_count, uint32_t out_packets_count) {
  const std::string control_interface = control_links_[0].peer_interface;
  const std::string sut_interface = control_links_[0].sut_interface;

  LOG(INFO) << "sut_interface: " << sut_interface;

  absl::flat_hash_map<std::string, std::string> port_id_by_interface;
  ASSIGN_OR_RETURN(port_id_by_interface,
                   GetAllInterfaceNameToPortId(*gnmi_stub_));
  ASSIGN_OR_RETURN(const std::string sut_port_id,
                   gutil::FindOrStatus(port_id_by_interface, sut_interface));

  thinkit::ControlDevice& control_device = generic_testbed_->ControlDevice();

  // Clear entries and set up a route to forward all packets to the SUT port.
  // Set up egress ACL to drop all IPv6 packets for testing out-discard
  // counters.
  RETURN_IF_ERROR(pdpi::ClearEntities(*sut_p4_session_));
  RETURN_IF_ERROR(sai::EntryBuilder()
                      .AddEntriesForwardingIpPacketsToGivenPort(sut_port_id)
                      .AddEgressAclDroppingIpPackets(sai::IpVersion::kIpv6)
                      .LogPdEntries()
                      .InstallDedupedEntities(*sut_p4_session_));

  // Read some initial counters via GNMI from the SUT.
  ASSIGN_OR_RETURN(
      const uint64_t initial_port_out_pkts,
      GetInterfaceCounter("out-pkts", sut_interface, gnmi_stub_.get()));
  ASSIGN_OR_RETURN(
      const uint64_t initial_port_out_discards,
      GetInterfaceCounter("out-discards", sut_interface, gnmi_stub_.get()));
  ASSIGN_OR_RETURN(BlackholeSwitchCounters initial_blackhole_switch_counters,
                   GetBlackholeSwitchCounters(*gnmi_stub_));
  ASSIGN_OR_RETURN(BlackholePortCounters initial_blackhole_port_counters,
                   GetBlackholePortCounters(sut_interface, *gnmi_stub_));

  LOG(INFO) << "Sending test packets on port: " << control_interface;
  // All IPv6 packets will be dropped by the egress ACL.
  RETURN_IF_ERROR(SendPackets(control_device, control_interface,
                              sai::IpVersion::kIpv6, kIpv6DstIpForL3Hit,
                              out_discards_count));
  // All IPv4 packets will be forwarded to the SUT port.
  RETURN_IF_ERROR(SendPackets(control_device, control_interface,
                              sai::IpVersion::kIpv4, kIpv4DstIpForL3Hit,
                              out_packets_count));

  // Wait some time before capturing the port stats.
  absl::SleepFor(absl::Seconds(15));

  // Re-read the same counters via GNMI from the SUT.
  ASSIGN_OR_RETURN(
      const uint64_t final_port_out_pkts,
      GetInterfaceCounter("out-pkts", sut_interface, gnmi_stub_.get()));
  ASSIGN_OR_RETURN(
      const uint64_t final_port_out_discards,
      GetInterfaceCounter("out-discards", sut_interface, gnmi_stub_.get()));
  ASSIGN_OR_RETURN(BlackholeSwitchCounters final_blackhole_switch_counters,
                   GetBlackholeSwitchCounters(*gnmi_stub_));
  ASSIGN_OR_RETURN(BlackholePortCounters final_blackhole_port_counters,
                   GetBlackholePortCounters(sut_interface, *gnmi_stub_));

  // Compute the change for each counter.
  const uint64_t port_out_pkts_delta =
      final_port_out_pkts - initial_port_out_pkts;
  const uint64_t port_out_discards_delta =
      final_port_out_discards - initial_port_out_discards;
  BlackholeSwitchCounters blackhole_switch_delta =
      final_blackhole_switch_counters - initial_blackhole_switch_counters;
  BlackholePortCounters blackhole_port_delta =
      final_blackhole_port_counters - initial_blackhole_port_counters;

  return OutDiscardCounters{
      .port_out_packets = port_out_pkts_delta,
      .port_out_discard_packets = port_out_discards_delta,
      .port_blackhole_out_discard_events =
          blackhole_port_delta.out_discard_events,
      .switch_blackhole_out_discard_events =
          blackhole_switch_delta.out_discard_events,
      // Sometimes fec_not_correctable_events occur which the test can't
      // control, so subtract those from the switch blackhole counter.
      .switch_blackhole_events =
          blackhole_switch_delta.blackhole_events -
          blackhole_switch_delta.fec_not_correctable_events,
  };
}

}  // namespace pins_test
