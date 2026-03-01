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

#include "tests/integration/system/alpm_miss_counter_tests.h"

#include <algorithm>
#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/log/log.h"
#include "absl/random/random.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/validator/validator_lib.h"
#include "p4_infra/netaddr/mac_address.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/p4_pdpi/p4_runtime_session_extras.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.pb.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "thinkit/control_device.h"
#include "thinkit/switch.h"

namespace pins_test {

constexpr char kIpv4DstIpForL3Route[] = "10.10.20.0";
constexpr int kIpv4DstIpPrefixLenForL3Route = 24;
constexpr char kIpv4DstIpForL3Hit[] = "10.10.20.10";
constexpr char kIpv4DstIpForL3Miss[] = "10.10.30.10";

constexpr char kIpv6DstIpForL3Route[] = "F105:0102::";
constexpr int kIpv6DstIpPrefixLenForL3Route = 64;
constexpr char kIpv6DstIpForL3Hit[] = "F105:0102::2356";
constexpr char kIpv6DstIpForL3Miss[] = "F205:0102::9845";

constexpr uint32_t kPacketsToSend = 1000;
constexpr uint32_t kNumberOfPacketsMargin = 50;

enum class IpVersion {
  kIpv4,
  kIpv6,
  kIpv4And6,
};

void CreateAlpmRouteParams(struct AlpmRouteParams& route_params,
                           const std::string& p4rt_egress_port_id) {
  route_params.neighbor_id =
      netaddr::MacAddress(1, 3, 5, 7, 9, 9).ToLinkLocalIpv6Address().ToString();
  route_params.vrf = absl::StrCat("vrf-", p4rt_egress_port_id);
  route_params.rif = absl::StrCat("rif-", p4rt_egress_port_id);
  route_params.nexthop = absl::StrCat("nexthop-", p4rt_egress_port_id);
  route_params.p4_port_id = p4rt_egress_port_id;
}

absl::StatusOr<sai::TableEntries> ConstructTestEntries(
    struct AlpmRouteParams& route_params, IpVersion ip_version) {
  sai::TableEntries test_entries;
  ASSIGN_OR_RETURN(
      test_entries,
      gutil::ParseTextProto<sai::TableEntries>(absl::Substitute(
          R"pb(
            entries {
              vrf_table_entry {
                match { vrf_id: "$0" }
                action { no_action {} }
              }
            }
            entries {
              acl_pre_ingress_table_entry {
                match { is_ip { value: "0x1" } }
                action { set_vrf { vrf_id: "$0" } }
                priority: 1
              }
            }
            entries {
              router_interface_table_entry {
                match { router_interface_id: "$2" }
                action {
                  set_port_and_src_mac {
                    port: "$4"
                    src_mac: "09:08:07:08:09:09"
                  }
                }
              }
            }
            entries {
              neighbor_table_entry {
                match { router_interface_id: "$2" neighbor_id: "$1" }
                action { set_dst_mac { dst_mac: "01:03:05:07:09:09" } }
              }
            }
            entries {
              nexthop_table_entry {
                match { nexthop_id: "$3" }
                action {
                  set_ip_nexthop { router_interface_id: "$2" neighbor_id: "$1" }
                }
              }
            }
          )pb",
          route_params.vrf, route_params.neighbor_id, route_params.rif,
          route_params.nexthop, route_params.p4_port_id)));

  if (ip_version == IpVersion::kIpv4 || ip_version == IpVersion::kIpv4And6) {
    *test_entries.add_entries() =
        gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
            R"pb(
              ipv4_table_entry {
                match {
                  vrf_id: "$0"
                  ipv4_dst: { value: "$2" prefix_length: $3 }
                }
                action { set_nexthop_id { nexthop_id: "$1" } }
              }
            )pb",
            route_params.vrf, route_params.nexthop, kIpv4DstIpForL3Route,
            kIpv4DstIpPrefixLenForL3Route));
  }

  if (ip_version == IpVersion::kIpv6 || ip_version == IpVersion::kIpv4And6) {
    *test_entries.add_entries() = gutil::ParseProtoOrDie<sai::TableEntry>(
        absl::Substitute(R"pb(
                           ipv6_table_entry {
                             match {
                               vrf_id: "$0"
                               ipv6_dst: { value: "$2" prefix_length: $3 }
                             }
                             action { set_nexthop_id { nexthop_id: "$1" } }
                           }
                         )pb",
                         route_params.vrf, route_params.nexthop,
                         kIpv6DstIpForL3Route, kIpv6DstIpPrefixLenForL3Route));
  }

  // L3 admit entry.
  *test_entries.add_entries() = gutil::ParseProtoOrDie<sai::TableEntry>(R"pb(
    l3_admit_table_entry {
      match {}  # Wildcard.
      action { admit_to_l3 {} }
      priority: 1
    }
  )pb");

  return test_entries;
}

absl::StatusOr<std::string> GetPortId(gnmi::gNMI::StubInterface& gnmi_stub,
                                      absl::string_view interface) {
  absl::flat_hash_map<std::string, std::string> interface_to_port_id;
  ASSIGN_OR_RETURN(interface_to_port_id,
                   pins_test::GetAllInterfaceNameToPortId(gnmi_stub));
  return gutil::FindOrStatus(interface_to_port_id, interface);
}

// Test packet proto message sent from control switch to SUT.
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

absl::StatusOr<uint64_t> GetGnmiStats(gnmi::gNMI::StubInterface& gnmi_stub,
                                      absl::string_view state_path,
                                      absl::string_view resp_parse_str) {
  ASSIGN_OR_RETURN(
      std::string stat_response,
      GetGnmiStatePathInfo(&gnmi_stub, state_path, resp_parse_str));

  uint64_t stat;
  if (!absl::SimpleAtoi(StripQuotes(stat_response), &stat)) {
    return absl::InternalError(
        absl::StrCat("Unable to parse counter from ", stat_response));
  }
  return stat;
}

absl::StatusOr<uint64_t> GetGnmiInterfaceStat(
    absl::string_view stat_name, absl::string_view interface,
    gnmi::gNMI::StubInterface& gnmi_stub) {
  std::string state_path = absl::StrCat("interfaces/interface[name=", interface,
                                        "]/state/counters/", stat_name);
  std::string resp_parse_str =
      absl::StrCat("openconfig-interfaces:", stat_name);
  return GetGnmiStats(gnmi_stub, state_path, resp_parse_str);
}

absl::StatusOr<uint64_t> GetAlpmMissStat(gnmi::gNMI::StubInterface& gnmi_stub) {
  std::string state_path =
      "components/component[name=integrated_circuit0]/integrated-circuit/"
      "pipeline-counters/drop/lookup-block/state/no-route";
  std::string resp_parse_str = "openconfig-platform-pipeline-counters:no-route";

  return GetGnmiStats(gnmi_stub, state_path, resp_parse_str);
}

absl::StatusOr<bool> DoesPlatformSupportAlpm(
    gnmi::gNMI::StubInterface& gnmi_stub) {
  std::string state_path =
      "components/component[name=chassis]/chassis/state/platform";
  std::string resp_parse_str = "openconfig-pins-platform-chassis:platform";

  ASSIGN_OR_RETURN(
      std::string state_response,
      GetGnmiStatePathInfo(&gnmi_stub, state_path, resp_parse_str));
  if (absl::StrContains(state_response, "SOME_PLATFORM_NOT_ALPM")){
     return false;
  } else {
    return true;
  }
}

// Control switch sends packets to SUT.
void SendPackets(gnmi::gNMI::StubInterface& sut_gnmi_stub,
                 thinkit::ControlDevice& control_device,
                 absl::string_view sut_port, absl::string_view control_port,
                 IpVersion ip_version, bool l3_miss) {
  // Make test packet.
  packetlib::Packet test_packet;
  if (ip_version == IpVersion::kIpv4) {
    test_packet = gutil::ParseProtoOrDie<packetlib::Packet>(absl::Substitute(
        kIpv4TestPacket, l3_miss ? kIpv4DstIpForL3Miss : kIpv4DstIpForL3Hit));
  } else {
    test_packet = gutil::ParseProtoOrDie<packetlib::Packet>(absl::Substitute(
        kIpv6TestPacket, l3_miss ? kIpv6DstIpForL3Miss : kIpv6DstIpForL3Hit));
  }
  ASSERT_OK_AND_ASSIGN(std::string test_packet_data,
                       packetlib::SerializePacket(test_packet));
  LOG(INFO) << "Test packet to send: " << test_packet.DebugString();

  ASSERT_OK_AND_ASSIGN(
      uint64_t initial_in_pkts_on_sut_port,
      GetGnmiInterfaceStat("in-pkts", sut_port, sut_gnmi_stub));
  LOG(INFO) << "Initial Rx packets count on " << sut_port << ": "
            << initial_in_pkts_on_sut_port;

  // Send packet to SUT.
  for (uint32_t i = 0; i < kPacketsToSend; ++i) {
    ASSERT_OK(control_device.SendPacket(control_port, test_packet_data))
        << "failed to inject the packet.";
    absl::SleepFor(absl::Milliseconds(10));
  }
  LOG(INFO) << "Successfully sent " << kPacketsToSend << " packets.";
  // Wait some time before capturing the port stats.
  absl::SleepFor(absl::Seconds(15));

  ASSERT_OK_AND_ASSIGN(
      uint64_t final_in_pkts_on_sut_port,
      GetGnmiInterfaceStat("in-pkts", sut_port, sut_gnmi_stub));
  LOG(INFO) << "Final Rx packets count on " << sut_port << ": "
            << final_in_pkts_on_sut_port;

  // Verify port stats.
  uint64_t in_pkts_on_sut_port =
      final_in_pkts_on_sut_port - initial_in_pkts_on_sut_port;

  // There is a possibility that a few non-test protocol packets flowed on the
  // links while test traffic was running.
  EXPECT_GE(in_pkts_on_sut_port, kPacketsToSend);
}

// Sends the test packets and verifies the test result.
void SendPacketsAndVerifyResult(gnmi::gNMI::StubInterface& sut_gnmi_stub,
                                thinkit::ControlDevice& control_device,
                                absl::string_view sut_port,
                                absl::string_view control_port,
                                IpVersion ip_version, bool expect_l3_miss) {
  ASSERT_OK_AND_ASSIGN(uint64_t initial_miss_count,
                       GetAlpmMissStat(sut_gnmi_stub));
  LOG(INFO) << "Initial miss count: " << initial_miss_count;

  LOG(INFO) << "Sending test packets on port: " << control_port;
  ASSERT_NO_FATAL_FAILURE(SendPackets(sut_gnmi_stub, control_device, sut_port,
                                      control_port, ip_version,
                                      expect_l3_miss));

  ASSERT_OK_AND_ASSIGN(uint64_t final_miss_count,
                       GetAlpmMissStat(sut_gnmi_stub));
  LOG(INFO) << "Final miss count: " << final_miss_count;

  // There is a possibility that a few non-test packets flowed on the links
  // while test was running and may have miss the L3 route, so give margin on
  // l3 miss counter.
  if (expect_l3_miss) {
    EXPECT_GE(final_miss_count, initial_miss_count + kPacketsToSend);
    EXPECT_LE(final_miss_count,
              initial_miss_count + kPacketsToSend + kNumberOfPacketsMargin);
  } else {
    EXPECT_GE(final_miss_count, initial_miss_count);
    EXPECT_LE(final_miss_count, initial_miss_count + kNumberOfPacketsMargin);
  }
}

absl::Status ValidatePortsUp(
    thinkit::Switch& sut, thinkit::ControlDevice& control_device,
    const std::vector<std::string>& sut_interfaces,
    const std::vector<std::string>& control_device_interfaces) {
  absl::Status sut_ports_up_status =
      pins_test::PortsUp(sut, absl::Span<const std::string>(sut_interfaces));
  absl::Status control_switch_ports_up_status = control_device.ValidatePortsUp(
      absl::Span<const std::string>(control_device_interfaces));

  if (sut_ports_up_status.ok() && control_switch_ports_up_status.ok()) {
    return absl::OkStatus();
  }

  EXPECT_OK(sut_ports_up_status);
  EXPECT_OK(control_switch_ports_up_status);
  return absl::InternalError("PortsUp validation failed.");
}

void InstallTestEntries(thinkit::Switch& sut,
                        std::optional<p4::config::v1::P4Info> p4info,
                        struct AlpmRouteParams& route_params,
                        IpVersion ip_version) {
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<pdpi::P4RuntimeSession> p4_session,
                       pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
                           sut, /*gnmi_config=*/std::nullopt, p4info));

  ASSERT_OK_AND_ASSIGN(sai::TableEntries sut_test_entries,
                       ConstructTestEntries(route_params, ip_version));
  ASSERT_OK(pdpi::ClearTableEntries(p4_session.get()));

  LOG(INFO) << "Installing entries:" << sut_test_entries.ShortDebugString();
  ASSERT_OK(pdpi::InstallPdTableEntries(*p4_session, sut_test_entries));
}

// Tests that when IPv4 L3 route is added and Ipv4 test packets hit the added
// route, ALPM miss counter doesn't go up.
TEST_P(AlpmMissCountersTest, Ipv4AlpmRouteHit) {
  ASSERT_NO_FATAL_FAILURE(
      InitializeTestEnvironment("d9716769-9ca5-477b-b53b-1b96fce60e13"));

  if (GetParam().not_supported) {
    GTEST_SKIP() << "Test is not supported.";
  }
  if (!generic_testbed_->ControlDevice().SupportsSendPacket()) {
    GTEST_SKIP() << "Control device does not support SendPacket";
  }
  // Test requires at least 1 SUT interface.
  if (sut_interfaces_.empty()) {
    GTEST_SKIP() << "Need at least 1 SUT interface to test but got: "
                 << sut_interfaces_.size();
  }

  thinkit::Switch& sut = generic_testbed_->Sut();
  thinkit::ControlDevice& control_device = generic_testbed_->ControlDevice();
  ASSERT_OK(
      ValidatePortsUp(sut, control_device, sut_interfaces_, peer_interfaces_));

  std::shuffle(sut_interfaces_.begin(), sut_interfaces_.end(), absl::BitGen());
  std::string test_sut_interface = sut_interfaces_[0];
  ASSERT_OK_AND_ASSIGN(std::string sut_port_id,
                       GetPortId(*sut_gnmi_stub_, test_sut_interface));
  CreateAlpmRouteParams(route_params_, sut_port_id);

  ASSERT_NO_FATAL_FAILURE(InstallTestEntries(sut, GetParam().p4_info,
                                             route_params_, IpVersion::kIpv4));

  ASSERT_NO_FATAL_FAILURE(SendPacketsAndVerifyResult(
      *sut_gnmi_stub_, control_device, test_sut_interface,
      sut_to_peer_interface_mapping_[test_sut_interface], IpVersion::kIpv4,
      /*expect_l3_miss=*/false));

  ASSERT_OK(
      ValidatePortsUp(sut, control_device, sut_interfaces_, peer_interfaces_));
}

// Tests that when IPv4 L3 route is added and Ipv4 test packets miss the added
// route, ALPM miss counter goes up.
TEST_P(AlpmMissCountersTest, Ipv4AlpmRouteMiss) {
  ASSERT_NO_FATAL_FAILURE(
      InitializeTestEnvironment("07dda215-ad21-4c25-b89e-1128b3806c27"));

  if (GetParam().not_supported) {
    GTEST_SKIP() << "Test is not supported.";
  }
  if (!generic_testbed_->ControlDevice().SupportsSendPacket()) {
    GTEST_SKIP() << "Control device does not support SendPacket";
  }
  // Test requires at least 1 SUT interface.
  if (sut_interfaces_.empty()) {
    GTEST_SKIP() << "Need at least 1 SUT interface to test but got: "
                 << sut_interfaces_.size();
  }

  thinkit::Switch& sut = generic_testbed_->Sut();
  thinkit::ControlDevice& control_device = generic_testbed_->ControlDevice();
  ASSERT_OK(
      ValidatePortsUp(sut, control_device, sut_interfaces_, peer_interfaces_));

  std::shuffle(sut_interfaces_.begin(), sut_interfaces_.end(), absl::BitGen());
  std::string test_sut_interface = sut_interfaces_[0];
  ASSERT_OK_AND_ASSIGN(std::string sut_port_id,
                       GetPortId(*sut_gnmi_stub_, test_sut_interface));
  CreateAlpmRouteParams(route_params_, sut_port_id);

  ASSERT_NO_FATAL_FAILURE(InstallTestEntries(sut, GetParam().p4_info,
                                             route_params_, IpVersion::kIpv4));

  ASSERT_NO_FATAL_FAILURE(SendPacketsAndVerifyResult(
      *sut_gnmi_stub_, control_device, test_sut_interface,
      sut_to_peer_interface_mapping_[test_sut_interface], IpVersion::kIpv4,
      /*expect_l3_miss=*/true));

  ASSERT_OK(
      ValidatePortsUp(sut, control_device, sut_interfaces_, peer_interfaces_));
}

// Tests that when IPv6 L3 route is added and Ipv6 test packets hit the added
// route, ALPM miss counter doesn't go up.
TEST_P(AlpmMissCountersTest, Ipv6AlpmRouteHit) {
  ASSERT_NO_FATAL_FAILURE(
      InitializeTestEnvironment("552ebd5d-fa98-4298-b4ef-efab286bcc89"));

  if (GetParam().not_supported) {
    GTEST_SKIP() << "Test is not supported.";
  }
  if (!generic_testbed_->ControlDevice().SupportsSendPacket()) {
    GTEST_SKIP() << "Control device does not support SendPacket";
  }
  // Test requires at least 1 SUT interface.
  if (sut_interfaces_.empty()) {
    GTEST_SKIP() << "Need at least 1 SUT interface to test but got: "
                 << sut_interfaces_.size();
  }

  thinkit::Switch& sut = generic_testbed_->Sut();
  thinkit::ControlDevice& control_device = generic_testbed_->ControlDevice();
  ASSERT_OK(
      ValidatePortsUp(sut, control_device, sut_interfaces_, peer_interfaces_));

  std::shuffle(sut_interfaces_.begin(), sut_interfaces_.end(), absl::BitGen());
  std::string test_sut_interface = sut_interfaces_[0];
  ASSERT_OK_AND_ASSIGN(std::string sut_port_id,
                       GetPortId(*sut_gnmi_stub_, test_sut_interface));
  CreateAlpmRouteParams(route_params_, sut_port_id);

  ASSERT_NO_FATAL_FAILURE(InstallTestEntries(sut, GetParam().p4_info,
                                             route_params_, IpVersion::kIpv6));

  ASSERT_NO_FATAL_FAILURE(SendPacketsAndVerifyResult(
      *sut_gnmi_stub_, control_device, test_sut_interface,
      sut_to_peer_interface_mapping_[test_sut_interface], IpVersion::kIpv6,
      /*expect_l3_miss=*/false));

  ASSERT_OK(
      ValidatePortsUp(sut, control_device, sut_interfaces_, peer_interfaces_));
}

// Tests that when IPv6 L3 route is added and Ipv6 test packets miss the added
// route, ALPM miss counter goes up.
TEST_P(AlpmMissCountersTest, Ipv6AlpmRouteMiss) {
  ASSERT_NO_FATAL_FAILURE(
      InitializeTestEnvironment("b8c1ba7f-a8ca-429b-bb8b-9fc479fc7e71"));

  if (GetParam().not_supported) {
    GTEST_SKIP() << "Test is not supported.";
  }
  if (!generic_testbed_->ControlDevice().SupportsSendPacket()) {
    GTEST_SKIP() << "Control device does not support SendPacket";
  }
  // Test requires at least 1 SUT interface.
  if (sut_interfaces_.empty()) {
    GTEST_SKIP() << "Need at least 1 SUT interface to test but got: "
                 << sut_interfaces_.size();
  }

  thinkit::Switch& sut = generic_testbed_->Sut();
  thinkit::ControlDevice& control_device = generic_testbed_->ControlDevice();
  ASSERT_OK(
      ValidatePortsUp(sut, control_device, sut_interfaces_, peer_interfaces_));

  std::shuffle(sut_interfaces_.begin(), sut_interfaces_.end(), absl::BitGen());
  std::string test_sut_interface = sut_interfaces_[0];
  ASSERT_OK_AND_ASSIGN(std::string sut_port_id,
                       GetPortId(*sut_gnmi_stub_, test_sut_interface));
  CreateAlpmRouteParams(route_params_, sut_port_id);

  ASSERT_NO_FATAL_FAILURE(InstallTestEntries(sut, GetParam().p4_info,
                                             route_params_, IpVersion::kIpv6));

  ASSERT_NO_FATAL_FAILURE(SendPacketsAndVerifyResult(
      *sut_gnmi_stub_, control_device, test_sut_interface,
      sut_to_peer_interface_mapping_[test_sut_interface], IpVersion::kIpv6,
      /*expect_l3_miss=*/true));

  ASSERT_OK(
      ValidatePortsUp(sut, control_device, sut_interfaces_, peer_interfaces_));
}

// Tests that when IPv4 and IPv6 L3 routes are added and sent IPv4 and IPv6 test
// packets hit the added respective Ipv4/Ipv6 routes, ALPM miss counter does not
// go up.
TEST_P(AlpmMissCountersTest, Ipv4AndIpv6AlpmRoutesHit) {
  ASSERT_NO_FATAL_FAILURE(
      InitializeTestEnvironment("0fa17c84-fd92-4d79-a617-7b51e7b8c9ab"));

  if (GetParam().not_supported) {
    GTEST_SKIP() << "Test is not supported.";
  }
  if (!generic_testbed_->ControlDevice().SupportsSendPacket()) {
    GTEST_SKIP() << "Control device does not support SendPacket";
  }
  // Test requires at least 1 SUT interface.
  if (sut_interfaces_.empty()) {
    GTEST_SKIP() << "Need at least 1 SUT interface to test but got: "
                 << sut_interfaces_.size();
  }

  thinkit::Switch& sut = generic_testbed_->Sut();
  thinkit::ControlDevice& control_device = generic_testbed_->ControlDevice();
  ASSERT_OK(
      ValidatePortsUp(sut, control_device, sut_interfaces_, peer_interfaces_));

  std::shuffle(sut_interfaces_.begin(), sut_interfaces_.end(), absl::BitGen());
  std::string test_sut_interface = sut_interfaces_[0];
  ASSERT_OK_AND_ASSIGN(std::string sut_port_id,
                       GetPortId(*sut_gnmi_stub_, test_sut_interface));
  CreateAlpmRouteParams(route_params_, sut_port_id);

  ASSERT_NO_FATAL_FAILURE(InstallTestEntries(
      sut, GetParam().p4_info, route_params_, IpVersion::kIpv4And6));

  for (IpVersion ip_version : {IpVersion::kIpv4, IpVersion::kIpv6}) {
    SCOPED_TRACE(absl::StrCat(
        "Testing ", ip_version == IpVersion::kIpv4 ? "ipv4" : "ipv6"));
    ASSERT_NO_FATAL_FAILURE(SendPacketsAndVerifyResult(
        *sut_gnmi_stub_, control_device, test_sut_interface,
        sut_to_peer_interface_mapping_[test_sut_interface], ip_version,
        /*expect_l3_miss=*/false));
  }

  ASSERT_OK(
      ValidatePortsUp(sut, control_device, sut_interfaces_, peer_interfaces_));
}

// Tests that when IPv4 and IPv6 L3 routes are added and sent IPv4 and IPv6 test
// packets miss the added respective Ipv4/Ipv6 routes, ALPM miss counter goes
// up.
TEST_P(AlpmMissCountersTest, Ipv4AndIpv6AlpmRoutesMiss) {
  ASSERT_NO_FATAL_FAILURE(
      InitializeTestEnvironment("f2b48a38-bbb3-4ec0-9f91-e596a5d3dac3"));

  if (GetParam().not_supported) {
    GTEST_SKIP() << "Test is not supported.";
  }
  if (!generic_testbed_->ControlDevice().SupportsSendPacket()) {
    GTEST_SKIP() << "Control device does not support SendPacket";
  }
  // Test requires at least 1 SUT interface.
  if (sut_interfaces_.empty()) {
    GTEST_SKIP() << "Need at least 1 SUT interface to test but got: "
                 << sut_interfaces_.size();
  }

  thinkit::Switch& sut = generic_testbed_->Sut();
  thinkit::ControlDevice& control_device = generic_testbed_->ControlDevice();
  ASSERT_OK(
      ValidatePortsUp(sut, control_device, sut_interfaces_, peer_interfaces_));

  std::shuffle(sut_interfaces_.begin(), sut_interfaces_.end(), absl::BitGen());
  std::string test_sut_interface = sut_interfaces_[0];
  ASSERT_OK_AND_ASSIGN(std::string sut_port_id,
                       GetPortId(*sut_gnmi_stub_, test_sut_interface));
  CreateAlpmRouteParams(route_params_, sut_port_id);

  ASSERT_NO_FATAL_FAILURE(InstallTestEntries(
      sut, GetParam().p4_info, route_params_, IpVersion::kIpv4And6));

  for (IpVersion ip_version : {IpVersion::kIpv4, IpVersion::kIpv6}) {
    SCOPED_TRACE(absl::StrCat(
        "Testing ", ip_version == IpVersion::kIpv4 ? "ipv4" : "ipv6"));
    ASSERT_NO_FATAL_FAILURE(SendPacketsAndVerifyResult(
        *sut_gnmi_stub_, control_device, test_sut_interface,
        sut_to_peer_interface_mapping_[test_sut_interface], ip_version,
        /*expect_l3_miss=*/true));
  }

  ASSERT_OK(
      ValidatePortsUp(sut, control_device, sut_interfaces_, peer_interfaces_));
}

}  // namespace pins_test
