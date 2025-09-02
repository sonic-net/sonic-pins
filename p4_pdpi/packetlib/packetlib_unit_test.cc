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
#include <net/ethernet.h>
#include <netinet/in.h>

#include <string>

#include "absl/status/status.h"
#include "absl/strings/escaping.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4_pdpi/packetlib/bit_widths.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"

namespace packetlib {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::Eq;
using ::testing::HasSubstr;

const absl::string_view kEthernetSourceAddress = "8:0:20:86:35:4b";
const absl::string_view kEthernetDestinationAddress = "0:e0:f7:26:3f:e9";

TEST(PacketLib, BitWidthTest) {
  for (int bit_shift = 18; bit_shift >= 5; bit_shift -= 3) {
    // Generate test input data with `bit_shift + 1` bits.
    int input =
        (1 << bit_shift) | (1 << (bit_shift - 3) | (1 << (bit_shift - 5)));
    const std::string expected_error_message = absl::StrFormat(
        "Input has been truncated because maximum allowable "
        "bitwidth for this field is %d but input has %d bits: %d",
        kIpVersionBitwidth, bit_shift + 1, input);
    ASSERT_DEBUG_DEATH(IpVersion(input), HasSubstr(expected_error_message));
  }
}

TEST(PacketLib, UdpWithIpv4Header) {
  Packet packet;

  EthernetHeader* eth = packet.add_headers()->mutable_ethernet_header();
  eth->set_ethertype(EtherType(ETHERTYPE_IP));
  eth->set_ethernet_source(std::string(kEthernetSourceAddress));
  eth->set_ethernet_destination(std::string(kEthernetDestinationAddress));

  Ipv4Header* ipv4 = packet.add_headers()->mutable_ipv4_header();
  ipv4->set_version(IpVersion(4));
  ipv4->set_ihl(IpIhl(5));
  ipv4->set_ipv4_source("192.168.0.31");
  ipv4->set_ipv4_destination("192.168.0.30");
  ipv4->set_ttl(IpTtl(0x10));
  ipv4->set_dscp(IpDscp(3));
  ipv4->set_protocol(IpProtocol(IPPROTO_UDP));
  ipv4->set_ecn(IpEcn(2));
  ipv4->set_identification(IpIdentification(0));
  ipv4->set_flags(IpFlags(3));
  ipv4->set_fragment_offset(IpFragmentOffset(1234));

  UdpHeader* udp = packet.add_headers()->mutable_udp_header();
  udp->set_source_port(UdpPort(0x0014));
  udp->set_destination_port(UdpPort(0x000a));
  udp->set_length(UdpLength(0x001a));
  ASSERT_OK(SerializePacket(packet));
}

TEST(PacketLib, UdpWithIpv4HeaderIpfixDestPort) {
  Packet packet;

  EthernetHeader* eth = packet.add_headers()->mutable_ethernet_header();
  eth->set_ethertype(EtherType(ETHERTYPE_IP));
  eth->set_ethernet_source(std::string(kEthernetSourceAddress));
  eth->set_ethernet_destination(std::string(kEthernetDestinationAddress));

  Ipv4Header* ipv4 = packet.add_headers()->mutable_ipv4_header();
  ipv4->set_version(IpVersion(4));
  ipv4->set_ihl(IpIhl(5));
  ipv4->set_ipv4_source("192.168.0.31");
  ipv4->set_ipv4_destination("192.168.0.30");
  ipv4->set_ttl(IpTtl(0x10));
  ipv4->set_dscp(IpDscp(3));
  ipv4->set_protocol(IpProtocol(IPPROTO_UDP));
  ipv4->set_ecn(IpEcn(2));
  ipv4->set_identification(IpIdentification(0));
  ipv4->set_flags(IpFlags(3));
  ipv4->set_fragment_offset(IpFragmentOffset(1234));

  // Test should fail if UDP destination port == IPFIX and
  // IPFIX header is missing.
  UdpHeader* udp = packet.add_headers()->mutable_udp_header();
  udp->set_source_port(UdpPort(0x0014));
  udp->set_destination_port(UdpPort(kIpfixUdpDestPort));
  udp->set_length(UdpLength(0x001a));

  ASSERT_THAT(SerializePacket(packet),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("expected IpfixHeader")));
}

TEST(PacketLib, UdpWithIpv6Header) {
  Packet packet;
  EthernetHeader* eth = packet.add_headers()->mutable_ethernet_header();
  eth->set_ethertype(EtherType(ETHERTYPE_IPV6));
  eth->set_ethernet_source(std::string(kEthernetSourceAddress));
  eth->set_ethernet_destination(std::string(kEthernetDestinationAddress));

  Ipv6Header* ipv6 = packet.add_headers()->mutable_ipv6_header();
  ipv6->set_ipv6_source("5:6:7:8::");
  ipv6->set_ipv6_destination("2607:f8b0:c150:8114::");
  ipv6->set_flow_label(IpFlowLabel(0x12345));
  ipv6->set_next_header(IpNextHeader(17));
  ipv6->set_hop_limit(IpHopLimit(32));
  ipv6->set_dscp(IpDscp(3));
  ipv6->set_ecn(IpEcn(0));
  UdpHeader* udp = packet.add_headers()->mutable_udp_header();
  udp->set_source_port(UdpPort(0));
  udp->set_destination_port(UdpPort(0));
  ASSERT_OK(SerializePacket(packet));
}

TEST(PacketLib, TcpWithIpv4Header) {
  Packet packet;

  EthernetHeader* eth = packet.add_headers()->mutable_ethernet_header();
  eth->set_ethertype(EtherType(ETHERTYPE_IP));
  eth->set_ethernet_source(std::string(kEthernetSourceAddress));
  eth->set_ethernet_destination(std::string(kEthernetDestinationAddress));

  Ipv4Header* ipv4 = packet.add_headers()->mutable_ipv4_header();
  ipv4->set_ihl(IpIhl(0x5));
  ipv4->set_ipv4_source("139.133.217.110");
  ipv4->set_ipv4_destination("139.133.233.2");
  ipv4->set_ttl(IpTtl(0xff));
  ipv4->set_dscp(IpDscp(3));
  ipv4->set_protocol(IpProtocol(IPPROTO_TCP));
  ipv4->set_ecn(IpEcn(1));
  ipv4->set_identification(IpIdentification(0x08b8));
  ipv4->set_total_length(IpTotalLength(0x002e));
  ipv4->set_flags(IpFlags(1));
  ipv4->set_checksum(IpChecksum(0xae88));
  ipv4->set_fragment_offset(IpFragmentOffset(0x0b00));

  TcpHeader* tcp = packet.add_headers()->mutable_tcp_header();
  tcp->set_source_port(TcpPort(0x9005));
  tcp->set_destination_port(TcpPort(0x0017));
  tcp->set_sequence_number(TcpSequenceNumber(12));
  tcp->set_acknowledgement_number(TcpAcknowledgementNumber(55));
  tcp->set_data_offset(TcpDataOffset(5));
  tcp->set_rest_of_header(TcpRestOfHeader(0));
  ASSERT_OK(SerializePacket(packet));
}

TEST(PacketLib, ArpWithIpv4Header) {
  Packet packet;

  EthernetHeader* eth = packet.add_headers()->mutable_ethernet_header();
  eth->set_ethertype(EtherType(ETHERTYPE_ARP));
  eth->set_ethernet_source(std::string(kEthernetSourceAddress));
  eth->set_ethernet_destination(std::string(kEthernetDestinationAddress));

  ArpHeader* arp = packet.add_headers()->mutable_arp_header();
  arp->set_hardware_type(ArpType(0x0001));
  arp->set_protocol_type(ArpType(ETHERTYPE_IP));
  arp->set_hardware_length(ArpLength(0x06));
  arp->set_protocol_length(ArpLength(0x04));
  arp->set_operation(ArpOperation(0x0001));
  arp->set_sender_hardware_address("00:53:ff:ff:aa:aa");
  arp->set_sender_protocol_address("10.0.0.11");
  arp->set_target_hardware_address("00:00:00:00:00:00");
  arp->set_target_protocol_address("10.0.0.22");
  ASSERT_OK(SerializePacket(packet));
}

TEST(PacketLib, ICMPWithIpv4Header) {
  Packet packet;

  EthernetHeader* eth = packet.add_headers()->mutable_ethernet_header();
  eth->set_ethertype(EtherType(ETHERTYPE_IP));
  eth->set_ethernet_source(std::string(kEthernetSourceAddress));
  eth->set_ethernet_destination(std::string(kEthernetDestinationAddress));

  Ipv4Header* ipv4 = packet.add_headers()->mutable_ipv4_header();
  ipv4->set_ihl(IpIhl(0x5));
  ipv4->set_ipv4_source("139.133.217.110");
  ipv4->set_ipv4_destination("139.133.233.2");
  ipv4->set_ttl(IpTtl(252));
  ipv4->set_dscp(IpDscp(2));
  ipv4->set_protocol(IpProtocol(IPPROTO_ICMP));
  ipv4->set_ecn(IpEcn(2));
  ipv4->set_identification(IpIdentification(0x08b8));
  ipv4->set_total_length(IpTotalLength(0x002e));
  ipv4->set_flags(IpFlags(2));
  ipv4->set_fragment_offset(IpFragmentOffset(0));

  IcmpHeader* icmp = packet.add_headers()->mutable_icmp_header();
  icmp->set_type(IcmpType(0));
  icmp->set_code(IcmpCode(10));
  icmp->set_checksum(IcmpChecksum(0xfff5));
  icmp->set_rest_of_header(IcmpRestOfHeader(0));
  ASSERT_OK(SerializePacket(packet));
}

// TODO: Add unit test using example GRE header with checksum. This is not
// done for now because it's difficult to find an example GRE header with
// checksum.

TEST(PacketLib, GreHeaderIpv4EncapsulatedWithIpv4) {
  Packet packet;

  EthernetHeader* eth = packet.add_headers()->mutable_ethernet_header();
  eth->set_ethertype(EtherType(ETHERTYPE_IP));
  eth->set_ethernet_source(std::string(kEthernetSourceAddress));
  eth->set_ethernet_destination(std::string(kEthernetDestinationAddress));

  Ipv4Header* ipv4 = packet.add_headers()->mutable_ipv4_header();
  ipv4->set_ihl(IpIhl(0x5));
  ipv4->set_ipv4_source("139.133.217.110");
  ipv4->set_ipv4_destination("139.133.233.2");
  ipv4->set_ttl(IpTtl(252));
  ipv4->set_dscp(IpDscp(2));
  ipv4->set_protocol(IpProtocol(IPPROTO_GRE));
  ipv4->set_ecn(IpEcn(2));
  ipv4->set_identification(IpIdentification(0x08b8));
  ipv4->set_total_length(IpTotalLength(0x0034));
  ipv4->set_flags(IpFlags(2));
  ipv4->set_fragment_offset(IpFragmentOffset(0));

  GreHeader* gre = packet.add_headers()->mutable_gre_header();
  gre->set_checksum_present(GreChecksumPresent(0x0));
  gre->set_reserved0(GreReserved0(0x0));
  gre->set_version(GreVersion(0x0));
  gre->set_protocol_type(EtherType(ETHERTYPE_IP));

  Ipv4Header* encapsulated_ipv4 = packet.add_headers()->mutable_ipv4_header();
  encapsulated_ipv4->set_ihl(IpIhl(0x5));
  encapsulated_ipv4->set_ipv4_source("192.168.0.31");
  encapsulated_ipv4->set_ipv4_destination("192.168.0.30");
  encapsulated_ipv4->set_ttl(IpTtl(252));
  encapsulated_ipv4->set_dscp(IpDscp(2));
  encapsulated_ipv4->set_protocol(IpProtocol(IPPROTO_ICMP));
  encapsulated_ipv4->set_ecn(IpEcn(2));
  encapsulated_ipv4->set_identification(IpIdentification(0x08b8));
  encapsulated_ipv4->set_total_length(IpTotalLength(0x001c));
  encapsulated_ipv4->set_flags(IpFlags(2));
  encapsulated_ipv4->set_fragment_offset(IpFragmentOffset(0));

  IcmpHeader* icmp = packet.add_headers()->mutable_icmp_header();
  icmp->set_type(IcmpType(0));
  icmp->set_code(IcmpCode(10));
  icmp->set_checksum(IcmpChecksum(0xfff5));
  icmp->set_rest_of_header(IcmpRestOfHeader(0));

  ASSERT_OK(SerializePacket(packet));
}

TEST(PacketLib, GreHeaderWithChecksumIpv4EncapsulatedWithIpv4) {
  Packet packet;

  EthernetHeader* eth = packet.add_headers()->mutable_ethernet_header();
  eth->set_ethertype(EtherType(ETHERTYPE_IP));
  eth->set_ethernet_source(std::string(kEthernetSourceAddress));
  eth->set_ethernet_destination(std::string(kEthernetDestinationAddress));

  Ipv4Header* ipv4 = packet.add_headers()->mutable_ipv4_header();
  ipv4->set_ihl(IpIhl(0x5));
  ipv4->set_ipv4_source("139.133.217.110");
  ipv4->set_ipv4_destination("139.133.233.2");
  ipv4->set_ttl(IpTtl(252));
  ipv4->set_dscp(IpDscp(2));
  ipv4->set_protocol(IpProtocol(IPPROTO_GRE));
  ipv4->set_ecn(IpEcn(2));
  ipv4->set_identification(IpIdentification(0x08b8));
  ipv4->set_total_length(IpTotalLength(0x0038));
  ipv4->set_flags(IpFlags(2));
  ipv4->set_fragment_offset(IpFragmentOffset(0));

  GreHeader* gre = packet.add_headers()->mutable_gre_header();
  gre->set_checksum_present(GreChecksumPresent(0x1));
  gre->set_reserved0(GreReserved0(0x0));
  gre->set_version(GreVersion(0x0));
  gre->set_protocol_type(EtherType(ETHERTYPE_IP));
  gre->set_reserved1(GreReserved1(0x0));
  gre->set_checksum(GreChecksum(0x77ff));

  Ipv4Header* encapsulated_ipv4 = packet.add_headers()->mutable_ipv4_header();
  encapsulated_ipv4->set_ihl(IpIhl(0x5));
  encapsulated_ipv4->set_ipv4_source("192.168.0.31");
  encapsulated_ipv4->set_ipv4_destination("192.168.0.30");
  encapsulated_ipv4->set_ttl(IpTtl(252));
  encapsulated_ipv4->set_dscp(IpDscp(2));
  encapsulated_ipv4->set_protocol(IpProtocol(IPPROTO_ICMP));
  encapsulated_ipv4->set_ecn(IpEcn(2));
  encapsulated_ipv4->set_identification(IpIdentification(0x08b8));
  encapsulated_ipv4->set_total_length(IpTotalLength(0x001c));
  encapsulated_ipv4->set_flags(IpFlags(2));
  encapsulated_ipv4->set_fragment_offset(IpFragmentOffset(0));

  IcmpHeader* icmp = packet.add_headers()->mutable_icmp_header();
  icmp->set_type(IcmpType(0));
  icmp->set_code(IcmpCode(10));
  icmp->set_checksum(IcmpChecksum(0xfff5));
  icmp->set_rest_of_header(IcmpRestOfHeader(0));

  ASSERT_OK(SerializePacket(packet));
}

TEST(PacketLib, GreHeaderIpv6EncapsulatedWithIpv6) {
  Packet packet;
  EthernetHeader* eth = packet.add_headers()->mutable_ethernet_header();
  eth->set_ethertype(EtherType(ETHERTYPE_IPV6));
  eth->set_ethernet_source(std::string(kEthernetSourceAddress));
  eth->set_ethernet_destination(std::string(kEthernetDestinationAddress));

  Ipv6Header* ipv6 = packet.add_headers()->mutable_ipv6_header();
  ipv6->set_ipv6_source("5:6:7:8::");
  ipv6->set_ipv6_destination("2607:f8b0:c150:8114::");
  ipv6->set_flow_label(IpFlowLabel(0x12345));
  ipv6->set_next_header(IpNextHeader(0x2f));
  ipv6->set_hop_limit(IpHopLimit(32));
  ipv6->set_dscp(IpDscp(3));
  ipv6->set_ecn(IpEcn(0));

  GreHeader* gre = packet.add_headers()->mutable_gre_header();
  gre->set_checksum_present(GreChecksumPresent(0x0));
  gre->set_reserved0(GreReserved0(0x0));
  gre->set_version(GreVersion(0x0));
  gre->set_protocol_type(EtherType(ETHERTYPE_IPV6));

  Ipv6Header* encapsulated_ipv6 = packet.add_headers()->mutable_ipv6_header();
  encapsulated_ipv6->set_ipv6_source("5:6:7:8::");
  encapsulated_ipv6->set_ipv6_destination("2607:f8b0:c150:8115::");
  encapsulated_ipv6->set_flow_label(IpFlowLabel(0x12345));
  encapsulated_ipv6->set_next_header(IpNextHeader(17));
  encapsulated_ipv6->set_hop_limit(IpHopLimit(32));
  encapsulated_ipv6->set_dscp(IpDscp(3));
  encapsulated_ipv6->set_ecn(IpEcn(0));
  UdpHeader* udp = packet.add_headers()->mutable_udp_header();
  udp->set_source_port(UdpPort(0));
  udp->set_destination_port(UdpPort(0));

  ASSERT_OK(SerializePacket(packet));
}

TEST(PacketLib, GreHeaderWithChecksumIpv6EncapsulatedWithIpv6) {
  Packet packet;
  EthernetHeader* eth = packet.add_headers()->mutable_ethernet_header();
  eth->set_ethertype(EtherType(ETHERTYPE_IPV6));
  eth->set_ethernet_source(std::string(kEthernetSourceAddress));
  eth->set_ethernet_destination(std::string(kEthernetDestinationAddress));

  Ipv6Header* ipv6 = packet.add_headers()->mutable_ipv6_header();
  ipv6->set_ipv6_source("5:6:7:8::");
  ipv6->set_ipv6_destination("2607:f8b0:c150:8114::");
  ipv6->set_flow_label(IpFlowLabel(0x12345));
  ipv6->set_next_header(IpNextHeader(0x2f));
  ipv6->set_hop_limit(IpHopLimit(32));
  ipv6->set_dscp(IpDscp(3));
  ipv6->set_ecn(IpEcn(0));

  GreHeader* gre = packet.add_headers()->mutable_gre_header();
  gre->set_checksum_present(GreChecksumPresent(0x1));
  gre->set_reserved0(GreReserved0(0x0));
  gre->set_version(GreVersion(0x0));
  gre->set_protocol_type(EtherType(ETHERTYPE_IPV6));
  gre->set_reserved1(GreReserved1(0x0));
  gre->set_checksum(GreChecksum(0x640c));

  Ipv6Header* encapsulated_ipv6 = packet.add_headers()->mutable_ipv6_header();
  encapsulated_ipv6->set_ipv6_source("5:6:7:8::");
  encapsulated_ipv6->set_ipv6_destination("2607:f8b0:c150:8115::");
  encapsulated_ipv6->set_flow_label(IpFlowLabel(0x12345));
  encapsulated_ipv6->set_next_header(IpNextHeader(17));
  encapsulated_ipv6->set_hop_limit(IpHopLimit(32));
  encapsulated_ipv6->set_dscp(IpDscp(3));
  encapsulated_ipv6->set_ecn(IpEcn(0));
  UdpHeader* udp = packet.add_headers()->mutable_udp_header();
  udp->set_source_port(UdpPort(0));
  udp->set_destination_port(UdpPort(0));

  ASSERT_OK(SerializePacket(packet));
}

TEST(PacketLib, GreHeaderIpv4EncapsulatedWithIpv6) {
  Packet packet;
  EthernetHeader* eth = packet.add_headers()->mutable_ethernet_header();
  eth->set_ethertype(EtherType(ETHERTYPE_IPV6));
  eth->set_ethernet_source(std::string(kEthernetSourceAddress));
  eth->set_ethernet_destination(std::string(kEthernetDestinationAddress));

  Ipv6Header* ipv6 = packet.add_headers()->mutable_ipv6_header();
  ipv6->set_ipv6_source("2607:f8b0:c150:10::");
  ipv6->set_ipv6_destination("2002:a05:6860:749::");
  ipv6->set_flow_label(IpFlowLabel(0x0000));
  ipv6->set_next_header(IpNextHeader(0x2f));
  ipv6->set_hop_limit(IpHopLimit(63));
  ipv6->set_dscp(IpDscp(0));
  ipv6->set_ecn(IpEcn(0));

  GreHeader* gre = packet.add_headers()->mutable_gre_header();
  gre->set_checksum_present(GreChecksumPresent(0x0));
  gre->set_reserved0(GreReserved0(0x0));
  gre->set_version(GreVersion(0x0));
  gre->set_protocol_type(EtherType(ETHERTYPE_IP));

  Ipv4Header* encapsulated_ipv4 = packet.add_headers()->mutable_ipv4_header();
  encapsulated_ipv4->set_ihl(IpIhl(0x5));
  encapsulated_ipv4->set_ipv4_source("128.0.0.0");
  encapsulated_ipv4->set_ipv4_destination("185.168.204.0");
  encapsulated_ipv4->set_ttl(IpTtl(63));
  encapsulated_ipv4->set_dscp(IpDscp(0));
  encapsulated_ipv4->set_protocol(IpProtocol(IPPROTO_ICMP));
  encapsulated_ipv4->set_ecn(IpEcn(0));
  encapsulated_ipv4->set_identification(IpIdentification(0x0000));
  encapsulated_ipv4->set_total_length(IpTotalLength(0x011a));
  encapsulated_ipv4->set_flags(IpFlags(0));
  encapsulated_ipv4->set_fragment_offset(IpFragmentOffset(0));
  encapsulated_ipv4->set_checksum(IpChecksum(0x753a));

  IcmpHeader* icmp = packet.add_headers()->mutable_icmp_header();
  icmp->set_type(IcmpType(0x00));
  icmp->set_code(IcmpCode(0x00));
  icmp->set_checksum(IcmpChecksum(0x00e4));
  icmp->set_rest_of_header(IcmpRestOfHeader(0x00000000));

  packet.set_payload(
      "test packet #5: ROUTING_PINBALLL3TOGROUP_FLOW: ipv4_table_entry \t { "
      "match { vrf_id: \"vrf-210\" ipv4_dst { value: \"185.168.204.0\" "
      "prefix_length: 28 } } action { set_wcmp_group_id_and_metadata { "
      "wcmp_group_id: \"group-4294934578\" route_metadata: \"0x01\" } } }");

  ASSERT_OK(packetlib::SerializePacket(packet));
}

TEST(PacketLib, SaiP4BMv2PacketInHeader) {
  Packet packet;

  SaiP4BMv2PacketInHeader* packet_in_header =
      packet.add_headers()->mutable_sai_p4_bmv2_packet_in_header();
  packet_in_header->set_ingress_port("0x001");
  packet_in_header->set_target_egress_port("0x002");
  packet_in_header->set_unused_pad("0x00");

  EthernetHeader* eth = packet.add_headers()->mutable_ethernet_header();
  eth->set_ethertype(EtherType(ETHERTYPE_ARP));
  eth->set_ethernet_source(std::string(kEthernetSourceAddress));
  eth->set_ethernet_destination(std::string(kEthernetDestinationAddress));

  ArpHeader* arp = packet.add_headers()->mutable_arp_header();
  arp->set_hardware_type(ArpType(0x0001));
  arp->set_protocol_type(ArpType(ETHERTYPE_IP));
  arp->set_hardware_length(ArpLength(0x06));
  arp->set_protocol_length(ArpLength(0x04));
  arp->set_operation(ArpOperation(0x0001));
  arp->set_sender_hardware_address("00:53:ff:ff:aa:aa");
  arp->set_sender_protocol_address("10.0.0.11");
  arp->set_target_hardware_address("00:00:00:00:00:00");
  arp->set_target_protocol_address("10.0.0.22");
  ASSERT_OK(SerializePacket(packet));
}

TEST(PacketLib, PadPacket) {
  Packet packet;

  ASSERT_OK_AND_ASSIGN(int current_size, PacketSizeInBytes(packet));
  ASSERT_THAT(PadPacket(current_size - 1, packet), IsOkAndHolds(Eq(false)));
  ASSERT_THAT(PadPacket(current_size, packet), IsOkAndHolds(Eq(false)));
  ASSERT_THAT(PadPacket(current_size + 1, packet), IsOkAndHolds(Eq(true)));
  ASSERT_OK_AND_ASSIGN(int updated_size, PacketSizeInBytes(packet));
  EXPECT_EQ(current_size + 1, updated_size);
}

TEST(PacketLib, PadPacketWithEthernetHeader) {
  Packet packet;

  EthernetHeader* eth = packet.add_headers()->mutable_ethernet_header();
  eth->set_ethertype(EtherType(ETHERTYPE_IP));
  eth->set_ethernet_source(std::string(kEthernetSourceAddress));
  eth->set_ethernet_destination(std::string(kEthernetDestinationAddress));

  ASSERT_OK_AND_ASSIGN(int current_size, PacketSizeInBytes(packet));
  ASSERT_THAT(PadPacket(current_size - 1, packet), IsOkAndHolds(Eq(false)));
  ASSERT_THAT(PadPacket(current_size, packet), IsOkAndHolds(Eq(false)));
  ASSERT_THAT(PadPacket(current_size + 1, packet), IsOkAndHolds(Eq(true)));
  ASSERT_OK_AND_ASSIGN(int updated_size, PacketSizeInBytes(packet));
  EXPECT_EQ(current_size + 1, updated_size);
}

TEST(PacketLib, ExperimentalEncapsulatedPacket) {
  // Packet structure is:
  // Ethernet -> IP -> UDP -> IPFIX -> PSAMP ->
  // Sampled packet (ETH -> IP -> TCP/UDP -> payload)
  Packet packet;

  EthernetHeader* eth = packet.add_headers()->mutable_ethernet_header();
  eth->set_ethertype(EtherType(ETHERTYPE_IPV6));
  eth->set_ethernet_source(std::string(kEthernetSourceAddress));
  eth->set_ethernet_destination(std::string(kEthernetDestinationAddress));

  Ipv6Header* ipv6 = packet.add_headers()->mutable_ipv6_header();
  ipv6->set_ipv6_source("5:6:7:8::");
  ipv6->set_ipv6_destination("2607:f8b0:c150:8114::");
  ipv6->set_flow_label(IpFlowLabel(0x12345));
  ipv6->set_next_header(IpNextHeader(17));
  ipv6->set_hop_limit(IpHopLimit(32));
  ipv6->set_dscp(IpDscp(3));
  ipv6->set_ecn(IpEcn(0));

  UdpHeader* udp = packet.add_headers()->mutable_udp_header();
  udp->set_source_port(UdpPort(2222));
  udp->set_destination_port(UdpPort(kIpfixUdpDestPort));
  // Checksum is always zero for psamp packets
  udp->set_checksum(UdpChecksum(0x0));

  IpfixHeader* ipfix = packet.add_headers()->mutable_ipfix_header();
  ipfix->set_version(IpfixVersion(0x0A));
  // Packet came 10 seconds ago
  ipfix->set_export_time(
      IpfixExportTime(absl::ToUnixSeconds(absl::Now()) - 10));
  ipfix->set_sequence_number(IpfixSequenceNumber(1));
  ipfix->set_observation_domain_id(IpfixObservationDomainId(1));

  PsampHeader* psamp = packet.add_headers()->mutable_psamp_header();
  psamp->set_template_id(PsampTemplateId(0));
  psamp->set_observation_time(
      PsampObservationTime(absl::ToUnixNanos(absl::Now())));
  psamp->set_flowset(PsampFlowset(0x1234));
  psamp->set_next_hop_index(PsampNextHopIndex(0));
  psamp->set_epoch(PsampEpoch(0xABCD));
  psamp->set_ingress_port(PsampIngressPort(0x0d));
  psamp->set_egress_port(PsampEgressPort(0x0f));
  psamp->set_user_meta_field(PsampUserMetaField(0));
  psamp->set_dlb_id(PsampDlbId(0));
  packet.set_payload("000000000000000000");  // 18 octets

  ASSERT_OK(SerializePacket(packet));
}

TEST(GetEthernetTrailerTest, WorksForIpv4PacketWithVlanAndCsig) {
  Packet packet = gutil::ParseProtoOrDie<Packet>(R"pb(
    headers {
      ethernet_header {
        ethernet_destination: "aa:bb:cc:dd:ee:ff"
        ethernet_source: "11:22:33:44:55:66"
        ethertype: "0x8100"
      }
    }
    headers {
      vlan_header {
        priority_code_point: "0x0",
        drop_eligible_indicator: "0x0",
        vlan_identifier: "0x000",
        ethertype: "0x9900"
      }
    }
    headers {
      csig_header {
        signal_type: "0x1"
        reserved0: "0x0"
        signal_value: "0x11"
        locator_metadata: "0x00"
        ethertype: "0x0800"
      }
    }
    headers {
      ipv4_header {
        dscp: "0x1b"
        ecn: "0x1"
        identification: "0xa3cd"
        flags: "0x0"
        fragment_offset: "0x0000"
        ttl: "0x10"
        protocol: "0x05"
        ipv4_source: "10.0.0.1"
        ipv4_destination: "20.0.0.3"
      }
    }
    payload: "IPv4 packet payload"
  )pb");
  ASSERT_OK(UpdateAllComputedFields(packet));
  const std::string trailer = "Hi, I am the trailer, nice to meet you :)";
  packet.mutable_payload()->append(trailer);

  ASSERT_THAT(GetEthernetTrailer(packet), IsOkAndHolds(Eq(trailer)));
}

TEST(GetEthernetTrailerTest, WorksForIpv6Packet) {
  Packet packet = gutil::ParseProtoOrDie<Packet>(R"pb(
    headers {
      ethernet_header {
        ethernet_destination: "aa:bb:cc:dd:ee:ff"
        ethernet_source: "11:22:33:44:55:66"
        ethertype: "0x0800"
      }
    }
    headers {
      ipv6_header {
        dscp: "0x1b"
        ecn: "0x1"
        flow_label: "0x12345"
        next_header: "0x05"
        hop_limit: "0x10"
        ipv6_source: "::"
        ipv6_destination: "f::f"
      }
    }
    payload: "IPv6 packet payload"
  )pb");
  ASSERT_OK(UpdateAllComputedFields(packet));
  const std::string trailer = "Hi, I am the trailer, nice to meet you :)";
  packet.mutable_payload()->append(trailer);
  ASSERT_THAT(GetEthernetTrailer(packet), IsOkAndHolds(Eq(trailer)));
}

TEST(GetEthernetTrailerTest, PacketHeaderMustContainEthernetHeader) {
  Packet packet;
  ASSERT_THAT(GetEthernetTrailer(packet),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(GetEthernetTrailerTest,
     PacketHeaderDoesNotContainAnyHeadersAfterEthernetHeader) {
  Packet packet = gutil::ParseProtoOrDie<Packet>(R"pb(
    headers {
      ethernet_header {
        ethernet_destination: "aa:bb:cc:dd:ee:ff"
        ethernet_source: "11:22:33:44:55:66"
        ethertype: "0x0800"
      }
    }
  )pb");
  ASSERT_THAT(GetEthernetTrailer(packet),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(GetEthernetTrailerTest,
     PacketHeaderDoesNotContainAnyHeadersAfterVlanOrCsig) {
  Packet packet = gutil::ParseProtoOrDie<Packet>(R"pb(
    headers {
      ethernet_header {
        ethernet_destination: "aa:bb:cc:dd:ee:ff"
        ethernet_source: "11:22:33:44:55:66"
        ethertype: "0x0800"
      }
    }
    headers { vlan_header {} }
    headers { csig_header {} }
  )pb");
  ASSERT_THAT(GetEthernetTrailer(packet),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(GetEthernetTrailerTest, WorksForIpv4PacketWithIpv6AndUdp) {
  Packet packet = gutil::ParseProtoOrDie<Packet>(R"pb(
    headers {
      ethernet_header {
        ethernet_destination: "aa:bb:cc:dd:ee:ff"
        ethernet_source: "11:22:33:44:55:66"
        ethertype: "0x0800"
      }
    }
    headers {
      ipv4_header {
        dscp: "0x1b"
        ecn: "0x1"
        identification: "0xa3cd"
        flags: "0x0"
        fragment_offset: "0x0000"
        ttl: "0x10"
        protocol: "0x05"
        ipv4_source: "10.0.0.1"
        ipv4_destination: "20.0.0.3"
      }
    }
    headers {
      ipv6_header {
        dscp: "0x00"
        ecn: "0x0"
        flow_label: "0x00000"
        next_header: "0xfd"  # Reserved for experimentation.
        hop_limit: "0x00"
        ipv6_source: "2001:db8:0:12::1"
        ipv6_destination: "2001:db8:0:12::2"
      }
    }
    headers { udp_header { source_port: "0x0000" destination_port: "0x0000" } }
    payload: "IPv4 packet payload"
  )pb");

  ASSERT_OK(UpdateAllComputedFields(packet));
  const std::string trailer = "Hi, I am the trailer, nice to meet you :)";
  packet.mutable_payload()->append(trailer);

  ASSERT_THAT(GetEthernetTrailer(packet), IsOkAndHolds(Eq(trailer)));
}

TEST(GetEthernetTrailerTest, WorksForIpv6PacketWithIpv4AndTcp) {
  Packet packet = gutil::ParseProtoOrDie<Packet>(R"pb(
    headers {
      ethernet_header {
        ethernet_destination: "aa:bb:cc:dd:ee:ff"
        ethernet_source: "11:22:33:44:55:66"
        ethertype: "0x0800"
      }
    }
    headers {
      ipv6_header {
        dscp: "0x00"
        ecn: "0x0"
        flow_label: "0x00000"
        next_header: "0xfd"  # Reserved for experimentation.
        hop_limit: "0x00"
        ipv6_source: "2001:db8:0:12::1"
        ipv6_destination: "2001:db8:0:12::2"
      }
    }
    headers {
      ipv4_header {
        dscp: "0x1b"
        ecn: "0x1"
        identification: "0xa3cd"
        flags: "0x0"
        fragment_offset: "0x0000"
        ttl: "0x10"
        protocol: "0x05"
        ipv4_source: "10.0.0.1"
        ipv4_destination: "20.0.0.3"
      }
    }
    headers {
      tcp_header {
        source_port: "0x1001"
        destination_port: "0x2557"
        sequence_number: "0x00000001"
        acknowledgement_number: "0x00000000"
        rest_of_header: "0x002200000000000"
      }
    }
    payload: "IPv4 packet payload"
  )pb");
  ASSERT_OK(UpdateAllComputedFields(packet));
  const std::string trailer = "Hi, I am the trailer, nice to meet you :)";
  packet.mutable_payload()->append(trailer);

  ASSERT_THAT(GetEthernetTrailer(packet), IsOkAndHolds(Eq(trailer)));
}

TEST(GetEthernetTrailerTest,
     ReturnsEmptyStringWhenTrailerLengthIsTechnicallyNegativeForIpv6) {
  Packet packet = gutil::ParseProtoOrDie<Packet>(R"pb(
    headers {
      ethernet_header {
        ethernet_destination: "aa:bb:cc:dd:ee:ff"
        ethernet_source: "11:22:33:44:55:66"
        ethertype: "0x86dd"
      }
    }
    headers {
      ipv6_header {
        dscp: "0x1b"
        ecn: "0x1"
        flow_label: "0x12345"
        next_header: "0x05"
        hop_limit: "0x10"
        ipv6_source: "::"
        ipv6_destination: "f::f"
      }
    }
    payload: "IPv6 packet payload"
  )pb");
  ASSERT_OK(UpdateAllComputedFields(packet));
  *packet.mutable_headers(1)->mutable_ipv6_header()->mutable_payload_length() =
      "0x9999";
  ASSERT_THAT(GetEthernetTrailer(packet), IsOkAndHolds(Eq("")));
}

TEST(GetEthernetTrailerTest,
     ReturnsEmptyStringWhenTrailerLengthIsTechnicallyNegativeForIpv4) {
  Packet packet = gutil::ParseProtoOrDie<Packet>(R"pb(
    headers {
      ethernet_header {
        ethernet_destination: "aa:bb:cc:dd:ee:ff"
        ethernet_source: "11:22:33:44:55:66"
        ethertype: "0x0800"
      }
    }
    headers {
      ipv4_header {
        dscp: "0x1b"
        ecn: "0x1"
        identification: "0xa3cd"
        flags: "0x0"
        fragment_offset: "0x0000"
        ttl: "0x10"
        protocol: "0x05"
        ipv4_source: "10.0.0.1"
        ipv4_destination: "20.0.0.3"
      }
    }
    payload: "IPv4 packet payload"
  )pb");
  ASSERT_OK(UpdateAllComputedFields(packet));
  *packet.mutable_headers(1)->mutable_ipv4_header()->mutable_total_length() =
      "0x9999";
  ASSERT_THAT(GetEthernetTrailer(packet), IsOkAndHolds(Eq("")));
}

TEST(PacketLib, RoundTrippingForHopByHopOptions) {
  Packet packet = gutil::ParseProtoOrDie<Packet>(R"pb(
    headers {
      hop_by_hop_options_header {
        next_header: "0xfe"
        header_extension_length: "0x00"
        options_and_padding: "0x000000000000"
      }
    }
  )pb");
  ASSERT_OK_AND_ASSIGN(std::string raw_packet,
                       packetlib::RawSerializePacket(packet));
  EXPECT_EQ(absl::BytesToHexString(raw_packet), "fe00000000000000");

  Packet parsed_packet =
      ParsePacket(raw_packet, Header::kHopByHopOptionsHeader);
  EXPECT_THAT(PacketSizeInBits(parsed_packet, 0), IsOkAndHolds(64));
  EXPECT_THAT(parsed_packet, EqualsProto(packet));
}

TEST(PacketLib, UpdateAllComputedFieldsIsNoOpForHopByHopOptions) {
  Packet packet = gutil::ParseProtoOrDie<Packet>(R"pb(
    headers {
      hop_by_hop_options_header {
        next_header: "0xfe"
        header_extension_length: "0x00"
        options_and_padding: "0x010400000000"
      }
    }
  )pb");
  // Update is a no-op when N-padding is correct.
  ASSERT_OK(packetlib::UpdateAllComputedFields(packet).status());
  ASSERT_OK_AND_ASSIGN(std::string raw_packet,
                       packetlib::RawSerializePacket(packet));
  EXPECT_EQ(absl::BytesToHexString(raw_packet), "fe00010400000000");

  // Verify that the round-tripped packet is the same as the original packet.
  Packet parsed_packet =
      ParsePacket(raw_packet, Header::kHopByHopOptionsHeader);
  EXPECT_THAT(PacketSizeInBits(parsed_packet, 0), IsOkAndHolds(64));
  EXPECT_THAT(parsed_packet, EqualsProto(packet));
  EXPECT_TRUE(parsed_packet.reasons_invalid().empty());
}

TEST(PacketLib, UpdateComputedFieldsAddsSinglePaddingForHopByHopOptions) {
  Packet packet = gutil::ParseProtoOrDie<Packet>(R"pb(
    headers {
      hop_by_hop_options_header {
        next_header: "0xfe"
        header_extension_length: "0x00"
        options_and_padding: "0x0503000000"
      }
    }
  )pb");
  // Update adds a single padding.
  ASSERT_OK(packetlib::UpdateAllComputedFields(packet).status());
  ASSERT_OK_AND_ASSIGN(std::string raw_packet,
                       packetlib::RawSerializePacket(packet));
  EXPECT_EQ(absl::BytesToHexString(raw_packet), "fe00050300000000");

  // Verify that the round-tripped packet is the same as the original packet.
  Packet parsed_packet =
      ParsePacket(raw_packet, Header::kHopByHopOptionsHeader);
  EXPECT_THAT(PacketSizeInBits(parsed_packet, 0), IsOkAndHolds(64));
  EXPECT_THAT(parsed_packet, EqualsProto(packet));
}

TEST(PacketLib,
     UpdateComputedFieldsAddsSinglePaddingForNPaddingForHopByHopOptions) {
  Packet packet = gutil::ParseProtoOrDie<Packet>(R"pb(
    headers {
      hop_by_hop_options_header {
        next_header: "0xfe"
        header_extension_length: "0x00"
        options_and_padding: "0x00000000"
      }
    }
  )pb");
  
  // Update adds a single padding for N-padding.
  ASSERT_OK(packetlib::UpdateAllComputedFields(packet).status());
  ASSERT_OK_AND_ASSIGN(std::string raw_packet,
                       packetlib::RawSerializePacket(packet));
  EXPECT_EQ(absl::BytesToHexString(raw_packet), "fe00000000000100");

  // Verify that the round-tripped packet is the same as the original packet.
  Packet parsed_packet =
      ParsePacket(raw_packet, Header::kHopByHopOptionsHeader);
  EXPECT_THAT(PacketSizeInBits(parsed_packet, 0), IsOkAndHolds(64));
  EXPECT_THAT(parsed_packet, EqualsProto(packet));
}

TEST(PacketLib,
     UpdateComputedFieldsAddsNPaddingForOptionsAndPaddingForHopByHopOptions) {
  Packet packet = gutil::ParseProtoOrDie<Packet>(R"pb(
    headers {
      hop_by_hop_options_header {
        next_header: "0xfe"
        header_extension_length: "0x00"
        options_and_padding: "0x000000"
      }
    }
  )pb");
  
  // Update adds a N-padding.
  ASSERT_OK(packetlib::UpdateAllComputedFields(packet).status());
  ASSERT_OK_AND_ASSIGN(std::string raw_packet,
                       packetlib::RawSerializePacket(packet));
  EXPECT_EQ(absl::BytesToHexString(raw_packet), "fe00000000010100");

  // Verify that the round-tripped packet is the same as the original packet.
  Packet parsed_packet =
      ParsePacket(raw_packet, Header::kHopByHopOptionsHeader);
  EXPECT_THAT(PacketSizeInBits(parsed_packet, 0), IsOkAndHolds(64));

  EXPECT_THAT(parsed_packet, EqualsProto(packet));
}

TEST(PacketLib,
     UpdateAllComputedFieldsHasExceedingDataLengthForHopByHopOptions) {
  Packet packet = gutil::ParseProtoOrDie<Packet>(R"pb(
    headers {
      hop_by_hop_options_header {
        next_header: "0xfe"
        header_extension_length: "0x00"
        # The data length of 9 exceeds the maximum.
        options_and_padding: "0x010900000000"
      }
    }
  )pb");
  ASSERT_OK(packetlib::UpdateAllComputedFields(packet).status());
  ASSERT_OK_AND_ASSIGN(std::string raw_packet,
                       packetlib::RawSerializePacket(packet));
  EXPECT_EQ(absl::BytesToHexString(raw_packet), "fe00010900000000");

  // Verify that the round-tripped packet is the same as the original packet.
  Packet parsed_packet =
      ParsePacket(raw_packet, Header::kHopByHopOptionsHeader);
  EXPECT_EQ(parsed_packet.reasons_invalid_size(), 1);
  EXPECT_THAT(parsed_packet.mutable_reasons_invalid()->Get(0),
              HasSubstr("data length exceeds"));
}

TEST(PacketLib,
     UpdateAllComputedFieldsHasNonZeroPaddingForNPaddingInHopByHopOptions) {
  Packet packet = gutil::ParseProtoOrDie<Packet>(R"pb(
    headers {
      hop_by_hop_options_header {
        next_header: "0xfe"
        header_extension_length: "0x00"
        # The data length of  exceeds the maximum.
        options_and_padding: "0x010400010000"
      }
    }
  )pb");
  ASSERT_OK(packetlib::UpdateAllComputedFields(packet).status());
  ASSERT_OK_AND_ASSIGN(std::string raw_packet,
                       packetlib::RawSerializePacket(packet));
  EXPECT_EQ(absl::BytesToHexString(raw_packet), "fe00010400010000");

  // Verify that the round-tripped packet is the same as the original packet.
  Packet parsed_packet =
      ParsePacket(raw_packet, Header::kHopByHopOptionsHeader);
  EXPECT_EQ(parsed_packet.reasons_invalid_size(), 1);
  EXPECT_THAT(parsed_packet.mutable_reasons_invalid()->Get(0),
              HasSubstr("byte was non-zero"));
}

TEST(PacketLib,
     UpdateComputedFieldsAddNPaddingForEmptyOptionsAndPaddingHopByHopOptions) {
  Packet packet = gutil::ParseProtoOrDie<Packet>(R"pb(
    headers { hop_by_hop_options_header { next_header: "0xfe" } }
  )pb");
  // Update adds a N-padding for an empty options_and_padding.
  ASSERT_OK(packetlib::UpdateAllComputedFields(packet).status());
  ASSERT_OK_AND_ASSIGN(std::string raw_packet,
                       packetlib::RawSerializePacket(packet));
  EXPECT_EQ(absl::BytesToHexString(raw_packet), "fe00010400000000");

  // Verify that the round-tripped packet is the same as the original packet.
  Packet parsed_packet =
      ParsePacket(raw_packet, Header::kHopByHopOptionsHeader);
  EXPECT_THAT(PacketSizeInBits(parsed_packet, 0), IsOkAndHolds(64));
  EXPECT_THAT(parsed_packet, EqualsProto(packet));
}

TEST(PacketLib, MldPacket) {
  Packet mld_packet = gutil::ParseProtoOrDie<Packet>(R"pb(
    headers {
      ethernet_header {
        ethernet_destination: "33:33:ff:02:00:02"
        ethernet_source: "5e:33:7b:02:00:02"
        ethertype: "0x8100"
      }
    }
    headers {
      vlan_header {
        priority_code_point: "0x0"
        drop_eligible_indicator: "0x0"
        vlan_identifier: "0x0ff"
        ethertype: "0x86dd"
      }
    }
    headers {
      ipv6_header {
        version: "0x6"
        dscp: "0x00"
        ecn: "0x0"
        flow_label: "0x00000"
        payload_length: "0x0020"
        next_header: "0x00"
        hop_limit: "0x01"
        ipv6_source: "fe80::5c33:7bff:fe02:2"
        ipv6_destination: "ff02::1:ff02:2"
      }
    }
    headers {
      hop_by_hop_options_header {
        next_header: "0x3a"
        header_extension_length: "0x00"
        options_and_padding: "0x050200000100"
      }
    }
    headers {
      icmp_header {
        type: "0x83"
        code: "0x00"
        checksum: "0xabe2"
        rest_of_header: "0x00000000"
      }
    }
    payload: "0x3d3bef82a3dea76e75947c7b2c8a0b994526d01652c87564739cbe81b7fa73d8"
  )pb");
  ASSERT_OK(packetlib::UpdateAllComputedFields(mld_packet).status());
  ASSERT_OK_AND_ASSIGN(std::string raw_packet,
                       packetlib::RawSerializePacket(mld_packet));
  Packet parsed_mld_packet = ParsePacket(raw_packet);
  EXPECT_OK(ValidatePacket(parsed_mld_packet));
}

}  // namespace
}  // namespace packetlib
