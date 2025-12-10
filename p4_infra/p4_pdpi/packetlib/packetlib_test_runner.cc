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

#include <iostream>
#include <ostream>
#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/ascii.h"
#include "absl/strings/escaping.h"
#include "absl/strings/str_cat.h"
#include "google/protobuf/util/message_differencer.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/testing.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_infra/p4_pdpi/string_encodings/readable_byte_string.h"

namespace packetlib {

using ::gutil::PrintShortTextProto;
using ::gutil::PrintTextProto;

constexpr char kBanner[] =
    "=========================================================================="
    "======\n";
constexpr char kInputHeader[] =
    "-- INPUT -----------------------------------------------------------------"
    "------\n";
constexpr char kOutputHeader[] =
    "-- OUTPUT ----------------------------------------------------------------"
    "------\n";
constexpr char kRoundtripHeader[] =
    "-- ROUNDTRIP ERRORS ------------------------------------------------------"
    "------\n";

// Return "<status_code>: <status_message>. The ToString method for absl::Status
// is not meant to be used directly in tests.
std::string StatusToStableString(const absl::Status& status) {
  std::string status_message = absl::StatusCodeToString(status.code());
  if (!status.ok()) {
    absl::StrAppend(&status_message, ": ", status.message());
  }
  return status_message;
}

// Parses packet from bytes, and if it succeeds, re-serializes the parsed packet
// to check that the resulting bytes match the original input.
void RunPacketParseTest(
    const std::string& name, const std::string& readable_byte_string,
    Header::HeaderCase first_header = Header::kEthernetHeader) {
  std::cout << kBanner << "Parsing test: " << name << "\n" << kBanner;
  std::cout << kInputHeader << absl::StripAsciiWhitespace(readable_byte_string)
            << "\n"
            << kOutputHeader;

  // Attempt to parse.
  auto byte_string = pdpi::ReadableByteStringToByteString(readable_byte_string);
  if (!byte_string.ok()) {
    std::cout << "TEST BUG, DO NOT"
              << " SUBMIT! ReadableByteStringToByteString failed: "
              << byte_string.status() << "\n";
    return;
  }
  Packet packet = ParsePacket(*byte_string, first_header);
  std::cout << PrintTextProto(packet) << "\n";

  // Check roundtrip if parsing succeeded, or try to fix packet otherwise.
  if (packet.reasons_invalid().empty()) {
    auto byte_string_after_roundtrip = SerializePacket(packet);
    if (!byte_string_after_roundtrip.ok()) {
      std::cout << kRoundtripHeader
                << StatusToStableString(byte_string_after_roundtrip.status())
                << "\n";
    } else if (*byte_string_after_roundtrip != *byte_string) {
      std::cout << kRoundtripHeader
                << "Original packet does not match packet after parsing and "
                << "reserialization.\nOriginal packet:\n"
                << absl::BytesToHexString(*byte_string)
                << "\nParsed and reserialized packet:\n"
                << absl::BytesToHexString(*byte_string_after_roundtrip) << "\n";
    }
  } else {
    // The packet is invalid. Try to fix it.
    auto padded = PadPacketToMinimumSize(packet);
    std::cout << "PadPacketToMinimumSize(packet) = ";
    if (padded.ok()) {
      std::cout << (*padded ? "true" : "false") << "\n";
    } else {
      std::cout << StatusToStableString(padded.status()) << "\n";
    }
    auto updated = UpdateAllComputedFields(packet);
    std::cout << "UpdateAllComputedFields(packet) = ";
    if (updated.ok()) {
      std::cout << (*updated ? "true" : "false") << "\n";
    } else {
      std::cout << StatusToStableString(updated.status()) << "\n";
    }
    if ((padded.ok() && *padded) || (updated.ok() && *updated)) {
      packet.clear_reason_not_fully_parsed();
      packet.clear_reasons_invalid();
      std::cout << "ValidatePacket(packet) = "
                << StatusToStableString(ValidatePacket(packet)) << "\n";
    }
  }
}

// Validates the packet, and if it's not valid, attempts to
// UpdateAllComputedFields and revalidate.
// Then attempt to serialize the packet, and if this succeeds, parse the
// serialized packet back and verify that it matches the original packet.
void RunProtoPacketTest(
    const std::string& name, Packet packet,
    Header::HeaderCase first_header = Header::kEthernetHeader) {
  const std::string packet_text_proto = PrintTextProto(packet);

  std::cout << kBanner << "Proto packet test: " << name << "\n" << kBanner;
  std::cout << kInputHeader << "packet =" << std::endl
            << packet_text_proto << std::endl
            << kOutputHeader;

  auto valid = ValidatePacket(packet);
  std::cout << "ValidatePacket(packet) = " << StatusToStableString(valid)
            << std::endl;

  if (!valid.ok()) {
    std::cout << std::endl << "PadPacketToMinimumSize(packet) = ";
    if (auto padded = PadPacketToMinimumSize(packet); padded.ok()) {
      std::cout << (*padded ? "true" : "false") << std::endl;
      if (*padded) {
        // To print the payload in protobuf style, we put it in an otherwise
        // empty packet.
        Packet payload_only;
        payload_only.set_payload(packet.payload());
        std::cout << "new " << PrintShortTextProto(payload_only) << std::endl;
      }
    } else {
      std::cout << StatusToStableString(padded.status()) << std::endl;
    }

    std::cout << std::endl << "UpdateMissingComputedFields(packet) = ";
    if (auto updated = UpdateMissingComputedFields(packet); updated.ok()) {
      std::cout << (*updated ? "true" : "false") << std::endl;
      if (*updated) {
        std::cout << "packet =" << std::endl
                  << PrintTextProto(packet) << std::endl;
        // Try validating once more.
        std::cout << "ValidatePacket(packet) = "
                  << StatusToStableString(ValidatePacket(packet)) << std::endl;
      }
    } else {
      std::cout << StatusToStableString(updated.status()) << std::endl;
    }
  }

  // Try serializing (valid or invalid) packet.
  absl::StatusOr<std::string> bytes = SerializePacket(packet);
  std::cout << std::endl
            << "Serialize(Packet) = " << StatusToStableString(bytes.status())
            << "\n\n";
  absl::StatusOr<std::string> bytes_from_proto =
      SerializePacket(packet_text_proto);
  if (bytes != bytes_from_proto) {
    std::cout << "BUG: The two overloads of the Serialize function return "
                 "different results:\n- Serialize(Packet): "
              << gutil::StreamableStatusOr(bytes)
              << "\n- Serialize(absl::string_view): "
              << gutil::StreamableStatusOr(bytes_from_proto);
  }
  if (!bytes.ok()) return;

  // Test if the packet can be parsed back.
  auto reparsed_packet = ParsePacket(*bytes, first_header);
  // Check roundtrip property modulo `reason_not_fully_parsed` field.
  reparsed_packet.clear_reason_not_fully_parsed();
  google::protobuf::util::MessageDifferencer differ;
  std::string diff;
  differ.ReportDifferencesToString(&diff);
  if (!differ.Compare(packet, reparsed_packet)) {
    std::cout << kRoundtripHeader
              << "Original packet does not match packet after serialization "
                 "and reparsing:\n"
              << diff << "\n\n";
  }
}

void RunPacketParseTests() {
  RunPacketParseTest("Ethernet packet (valid)", R"pb(
    # ethernet header
    ethernet_destination: 0xaabbccddeeff
    ethernet_source: 0x112233445566
    ether_type: 0x002e  # This means size(payload) = 0x2e bytes = 46 bytes.
    # payload
    payload: 0x00 11 22 33 44 55 66 77 88 99 aa bb cc dd ee ff
    payload: 0x00 11 22 33 44 55 66 77 88 99 aa bb cc dd ee ff
    payload: 0x00 11 22 33 44 55 66 77 88 99 aa bb cc dd
  )pb");

  RunPacketParseTest("Ethernet packet (invalid)", R"pb(
    # ethernet header
    ethernet_destination: 0xaabbccddeeff
    ethernet_source: 0x112233445566
    ether_type: 0x0001  # This means size(payload) = 1 byte.
    # payload
    payload: 0x0102  # 2 bytes, but ether_type says 1 byte & minimum size is 46.
  )pb");

  RunPacketParseTest("Ethernet packet (unsupported EtherType)", R"pb(
    # ethernet header
    ethernet_destination: 0xaabbccddeeff
    ethernet_source: 0x112233445566
    ether_type: 0x0842  # Wake-on-LAN
  )pb");

  RunPacketParseTest("IPv4 packet (invalid)", R"pb(
    # ethernet header
    ethernet_destination: 0xaabbccddeeff
    ethernet_source: 0x112233445566
    ether_type: 0x0800
    # IPv4 header:
    version: 0x4
    ihl: 0x5
    dscp: 0b011011
    ecn: 0b01
    total_length: 0x6fc6
    identification: 0xa3cd
    flags: 0b000
    fragment_offset: 0b0000000000000
    ttl: 0x10
    protocol: 0x05  # some unsupported protocol
    checksum: 0x1234
    ipv4_source: 0x0a000001
    ipv4_destination: 0x14000003
    # other headers:
    payload: 0x1234
  )pb");

  RunPacketParseTest("IPv4 packet (valid)", R"pb(
    # ethernet header
    ethernet_destination: 0xaabbccddeeff
    ethernet_source: 0x112233445566
    ether_type: 0x0800
    # IPv4 header:
    version: 0x4
    ihl: 0x5
    dscp: 0b011011
    ecn: 0b01
    total_length: 0x0034
    identification: 0xa3cd
    flags: 0b000
    fragment_offset: 0b0000000000000
    ttl: 0x10
    protocol: 0x05  # some unsupported protocol
    checksum: 0xe887
    ipv4_source: 0x0a000001
    ipv4_destination: 0x14000003
    # payload:
    payload: 0x00 11 22 33 44 55 66 77 88 99 aa bb cc dd ee ff
    payload: 0x00 11 22 33 44 55 66 77 88 99 aa bb cc dd ee ff
  )pb");

  RunPacketParseTest("IPv4 packet (checksum example)", R"pb(
    # Taken from
    # wikipedia.org/wiki/IPv4_header_checksum#Calculating_the_IPv4_header_checksum
    #
    # ethernet header
    ethernet_destination: 0xaabbccddeeff
    ethernet_source: 0x112233445566
    ether_type: 0x0800
    # IPv4 header and payload
    ipv4_header: 0x 4500 0073 0000 4000 4011 b861 c0a8 0001 c0a8 00c7
    payload: 0x 0035 e97c 005f 279f 1e4b 8180
  )pb");

  RunPacketParseTest("IPv4 packet with options (valid)", R"pb(
    # Ethernet header
    ethernet_destination: 0xaabbccddeeff
    ethernet_source: 0x112233445566
    ether_type: 0x0800
    # IPv4 header:
    version: 0x4
    ihl: 0x6  # 5 + 1 x 32-bit suffix
    dscp: 0b011011
    ecn: 0b01
    total_length: 0x0038
    identification: 0xa3cd
    flags: 0b000
    fragment_offset: 0b0000000000000
    ttl: 0x10
    protocol: 0x05  # some unsupported protocol
    checksum: 0xa31d
    ipv4_source: 0x0a000001
    ipv4_destination: 0x14000003
    uninterpreted_suffix: 0x11223344
    # Payload
    payload: 0x00 11 22 33 44 55 66 77 88 99 aa bb cc dd ee ff
    payload: 0x00 11 22 33 44 55 66 77 88 99 aa bb cc dd ee ff
  )pb");

  RunPacketParseTest("IPv4 packet with options (too short)", R"pb(
    # Ethernet header
    ethernet_destination: 0xaabbccddeeff
    ethernet_source: 0x112233445566
    ether_type: 0x0800
    # IPv4 header:
    version: 0x4
    ihl: 0x6  # 5 + 1 x 32-bit suffix
    dscp: 0b011011
    ecn: 0b01
    total_length: 0x0018
    identification: 0xa3cd
    flags: 0b000
    fragment_offset: 0b0000000000000
    ttl: 0x10
    protocol: 0x05  # some unsupported protocol
    checksum: 0xd6a3
    ipv4_source: 0x0a000001
    ipv4_destination: 0x14000003
    uninterpreted_suffix: 0x11  # Should be 32 bits, but is only 8 bits.
  )pb");

  RunPacketParseTest("IPv4 packet with IP protocol 0xfd", R"pb(
    # ethernet header
    ethernet_destination: 0xaabbccddeeff
    ethernet_source: 0x112233445566
    ether_type: 0x0800
    # IPv4 header:
    version: 0x4
    ihl: 0x5
    dscp: 0b011011
    ecn: 0b01
    total_length: 0x0034
    identification: 0xa3cd
    flags: 0b000
    fragment_offset: 0b0000000000000
    ttl: 0x10
    protocol: 0xfd  # Reserved for experimentation -- payload is arbitrary.
    checksum: 0xe78f
    ipv4_source: 0x0a000001
    ipv4_destination: 0x14000003
    # payload:
    payload: 0x00 11 22 33 44 55 66 77 88 99 aa bb cc dd ee ff
    payload: 0x00 11 22 33 44 55 66 77 88 99 aa bb cc dd ee ff
  )pb");

  RunPacketParseTest("IPv6 packet with IP protocol 0xfe", R"pb(
    # ethernet header
    ethernet_destination: 0xffeeddccbbaa
    ethernet_source: 0x554433221100
    ether_type: 0x86DD
    # IPv6 header:
    version: 0x6
    dscp: 0b011011
    ecn: 0b01
    flow_label: 0x12345
    payload_length: 0x0010
    next_header: 0xfd  # Reserved for experimentation -- payload is arbitrary.
    hop_limit: 0x03
    ipv6_source: 0x00001111222233334444555566667777
    ipv6_destination: 0x88889999aaaabbbbccccddddeeeeffff
    # other headers:
    payload: 0x00 11 22 33 44 55 66 77 88 99 aa bb cc dd ee ff
  )pb");

  RunPacketParseTest("IPv6 packet (invalid)", R"pb(
    # ethernet header
    ethernet_destination: 0xffeeddccbbaa
    ethernet_source: 0x554433221100
    ether_type: 0x86DD
    # IPv6 header:
    version: 0x4
    dscp: 0b011011
    ecn: 0b01
    flow_label: 0x12345
    payload_length: 0x0000
    next_header: 0x90  # some unassigned protocol
    hop_limit: 0xff
    ipv6_source: 0x00001111222233334444555566667777
    ipv6_destination: 0x88889999aaaabbbbccccddddeeeeffff
    # other headers:
    payload: 0x12
  )pb");

  RunPacketParseTest("IPv6 packet (valid)", R"pb(
    # ethernet header
    ethernet_destination: 0xffeeddccbbaa
    ethernet_source: 0x554433221100
    ether_type: 0x86DD
    # IPv6 header:
    version: 0x6
    dscp: 0b011011
    ecn: 0b01
    flow_label: 0x12345
    payload_length: 0x0020
    next_header: 0x90  # some unassigned protocol
    hop_limit: 0x03
    ipv6_source: 0x00001111222233334444555566667777
    ipv6_destination: 0x88889999aaaabbbbccccddddeeeeffff
    # other headers:
    payload: 0x00 11 22 33 44 55 66 77 88 99 aa bb cc dd ee ff
    payload: 0x00 11 22 33 44 55 66 77 88 99 aa bb cc dd ee ff
  )pb");

  RunPacketParseTest("UDP packet (valid)", R"pb(
    # Taken from
    # www.securitynik.com/2015/08/calculating-udp-checksum-with-taste-of.html
    # --------------------------------------------------------------------------
    # Ethernet header
    ethernet_destination: 0xaabbccddeeff
    ethernet_source: 0x112233445566
    ether_type: 0x0800
    # IPv4 header
    version: 0x4
    ihl: 0x5
    dscp: 0b011011
    ecn: 0b01
    total_length: 0x002e
    identification: 0x0000
    flags: 0b000
    fragment_offset: 0b0000000000000
    ttl: 0x10
    protocol: 0x11  # UDP
    checksum: 0x28c5
    ipv4_source: 0xc0a8001f       # 192.168.0.31
    ipv4_destination: 0xc0a8001e  # 192.168.0.30
    # UDP header
    source_port: 0x0014       # 20
    destination_port: 0x000a  # 10
    length: 0x001a            # 26
    checksum: 0x7961
    # Payload
    payload: 0x4869                                             # "Hi" in ASCII
    payload: 0x00 11 22 33 44 55 66 77 88 99 aa bb cc dd ee ff  # Padding
  )pb");

  RunPacketParseTest("TCP packet (valid)", R"pb(
    # Taken from
    # www.erg.abdn.ac.uk/users/gorry/course/inet-pages/packet-decode3.html
    # --------------------------------------------------------------------------
    # Ethernet header
    ethernet_destination: 0x 00 e0 f7 26 3f e9
    ethernet_source: 0x 08 00 20 86 35 4b
    ether_type: 0x0800
    # IPv4 header
    version: 0x4
    ihl: 0x5
    dscp: 0b000000
    ecn: 0b00
    total_length: 0x002e
    identification: 0x08b8
    flags: 0b010
    fragment_offset: 0b0000000000000
    ttl: 0xff
    protocol: 0x06  # TCP
    checksum: 0x9995
    ipv4_source: 0x8b85d96e       # 139.133.217.110
    ipv4_destination: 0x8b85e902  # 139.133.233.2
    # TCP header
    source_port: 0x9005          # 36869
    destination_port: 0x0017     # 23 (TELNET)
    sequence_number: 0x7214f114  # 1913975060
    acknowledgement_number: 0x00000000
    data_offset: 0x6  # 6 x 32 bits = 24 bytes
    reserved: 0b000
    flags: 0b 0 0 0 0 0 0 0 1 0  # SYN
    window_size: 0x2238          # 8760
    checksum: 0xa92c
    urgent_pointer: 0x0000
    options: 0x 0204 05b4
    # Payload
    payload: 0x 11 22
  )pb");

  RunPacketParseTest("ARP Packet (Valid)", R"pb(
    # Ethernet header
    ethernet_destination: 0x ff ff ff ff ff ff
    ethernet_source: 0x 00 11 22 33 44 55
    ether_type: 0x0806
    # ARP header
    hardware_type: 0x0001  # Ethernet
    protocol_type: 0x0800  # IPv4
    hardware_length: 0x06
    protocol_length: 0x04
    operation: 0x0001  # Request
    sender_hardware_address: 0x 00 11 22 33 44 55
    sender_protocol_address: 0x 0a 00 00 01
    target_hardware_address: 0x 00 00 00 00 00 00
    target_protocol_address: 0x 0a 00 00 02
    # Payload
    payload: 0x 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
  )pb");

  RunPacketParseTest("ICMPv4 Packet (Valid)", R"pb(
    # Taken from
    # www.erg.abdn.ac.uk/users/gorry/course/inet-pages/packet-dec1.html
    # --------------------------------------------------------------------------
    # Ethernet header
    ethernet_destination: 0x 08 00 20 86 35 4b
    ethernet_source: 0x 00 e0 f7 26 3f e9
    ether_type: 0x0800
    # IPv4 header
    version: 0x4
    ihl: 0x5
    dscp: 0b000000
    ecn: 0b00
    total_length: 0x0054
    identification: 0xaafb
    flags: 0b010  # website's 0x4 is from interpreting 4 bits.
    fragment_offset: 0b0000000000000
    ttl: 0xfc       # 252
    protocol: 0x01  # ICMP
    checksum: 0xfa30
    ipv4_source: 0x 8b 85 e9 02       # 139.133.233.2
    ipv4_destination: 0x 8b 85 d9 6e  # 139.133.233.110
    # ICMP header
    type: 0x00
    code: 0x00
    checksum: 0x45da
    rest_of_header: 0x 1e 60 00 00
    # payload
    payload: 0x 33 5e 3a b8 00 00 42 ac 08 09 0a 0b 0c 0d 0e 0f 10 11 12 13 14
    payload: 0x 15 16 17 18 19 1a 1b 1c 1d 1e 1f 20 21 22 23 24 25 26 27 28 29
    payload: 0x 2a 2b 2c 2d 2e 2f 30 31 32 33 34 35 36 37
  )pb");
  RunPacketParseTest("ICMPv6 Packet (Valid)", R"pb(
    # Taken from
    # www.cloudshark.org/captures/e98730aee1fb
    # --------------------------------------------------------------------------
    # Ethernet header
    ethernet_destination: 0x c2 01 51 fa 00 00
    ethernet_source: 0x c2 00 51 fa 00 00
    ethertype: 0x86dd
    # IPv6 header:
    version: 0x6
    dscp: 0b000000
    ecn: 0b00
    flow_label: 0x00000
    payload_length: 0x003c
    next_header: 0x3a  # ICMP
    hop_limit: 0x40
    ipv6_source: 0x20010db8000000120000000000000001
    ipv6_destination: 0x20010db8000000120000000000000002
    # ICMP header:
    type: 0x80
    code: 0x00
    checksum: 0x863c
    rest_of_header: 0x 11 0d 00 00
    # payload
    payload: 0x 00 01 02 03 04 05 06 07 08 09 0a 0b 0c 0d 0e 0f 10 11 12 13 14
    payload: 0x 15 16 17 18 19 1a 1b 1c 1d 1e 1f 20 21 22 23 24 25 26 27 28 29
    payload: 0x 2a 2b 2c 2d 2e 2f 30 31 32 33
  )pb");
  RunPacketParseTest("VLAN Packet with ARP (Valid)", R"pb(
    # Taken from
    # www.cloudshark.org/captures/e7f1b8c0b434
    # --------------------------------------------------------------------------
    # Ethernet header
    ethernet_destination: 0x ff ff ff ff ff ff
    ethernet_source: 0x 00 19 06 ea b8 c1
    ether_type: 0x8100
    # VLAN header
    priority_code_point: 0b000
    drop_eligibility_indicator: 0b0
    vlan_identifier: 0x07b
    ether_type: 0x0806
    # ARP header
    hardware_type: 0x0001  # Ethernet
    protocol_type: 0x0800  # IPv4
    hardware_length: 0x06
    protocol_length: 0x04
    operation: 0x0002  # Reply
    sender_hardware_address: 0x 00 19 06 ea b8 c1
    sender_protocol_address: 0x c0 a8 7b 01
    target_hardware_address: 0x ff ff ff ff ff ff
    target_protocol_address: 0x c0 a8 7b 01
    # Payload
    payload: 0x 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
  )pb");

  RunPacketParseTest("Packet too short to parse a GRE header (Invalid)", R"pb(
    # Ethernet header
    ethernet_destination: 0x c2 01 51 fa 00 00
    ethernet_source: 0x c2 00 51 fa 00 00
    ethertype: 0x86DD
    # IPv6 header:
    version: 0x6
    dscp: 0b000000
    ecn: 0b00
    flow_label: 0x00000
    payload_length: 0x0001
    next_header: 0x2f  # GRE
    hop_limit: 0x3f
    ipv6_source: 0x2607F8B0C15000100000000000000000
    ipv6_destination: 0x20020A05686007490000000000000000
    # GRE header:
    checksum_present: 0b0
    reserved0: 0b0000000
  )pb");
  RunPacketParseTest(
      "Packet too short to parse a GRE header with optional fields (Invalid)",
      R"pb(
        # Ethernet header
        ethernet_destination: 0x c2 01 51 fa 00 00
        ethernet_source: 0x c2 00 51 fa 00 00
        ethertype: 0x86DD
        # IPv6 header:
        version: 0x6
        dscp: 0b000000
        ecn: 0b00
        flow_label: 0x00000
        payload_length: 0x0004
        next_header: 0x2f  # GRE
        hop_limit: 0x3f
        ipv6_source: 0x2607F8B0C15000100000000000000000
        ipv6_destination: 0x20020A05686007490000000000000000
        # GRE header:
        checksum_present: 0b1
        reserved0: 0b000000000000
        version: 0b000
        protocol_type: 0x0800
      )pb");

  RunPacketParseTest("GRE Ipv4 Encapsulated with Ipv6 Header (Valid)", R"pb(
    # Ethernet header
    ethernet_destination: 0x c2 01 51 fa 00 00
    ethernet_source: 0x c2 00 51 fa 00 00
    ethertype: 0x86DD
    # IPv6 header:
    version: 0x6
    dscp: 0b000000
    ecn: 0b00
    flow_label: 0x00000
    payload_length: 0x011e
    next_header: 0x2f  # GRE
    hop_limit: 0x3f
    ipv6_source: 0x2607F8B0C15000100000000000000000
    ipv6_destination: 0x20020A05686007490000000000000000
    # GRE header:
    checksum_present: 0b0
    reserved0: 0b000000000000
    version: 0b000
    protocol_type: 0x0800
    # Encapsulated IPv4 header
    version: 0x4
    ihl: 0x5
    dscp: 0b000000
    ecn: 0b00
    total_length: 0x011a
    identification: 0x0000
    flags: 0b000
    fragment_offset: 0b0000000000000
    ttl: 0x3f       # 63
    protocol: 0x01  # ICMP
    checksum: 0x753a
    ipv4_source: 0x 80 00 00 00       # 128.0.0.0
    ipv4_destination: 0x b9 a8 cc 00  # 185.168.204.0
    # ICMP header:
    type: 0x00
    code: 0x00
    checksum: 0x00e4
    rest_of_header: 0x 00 00 00 00
    # Payload
    payload: 0x 74 65 73 74 20 70 61 63 6b 65 74 20 23 35 3a 20 52 4f 55 54 49
    payload: 0x 4e 47 5f 50 49 4e 42 41 4c 4c 4c 33 54 4f 47 52 4f 55 50 5f 46
    payload: 0x 4c 4f 57 3a 20 69 70 76 34 5F 74 61 62 6c 65 5f 65 6e 74 72 79
    payload: 0x 20 09 20 7b 20 6d 61 74 63 68 20 7b 20 76 72 66 5f 69 64 3a 20
    payload: 0x 22 76 72 66 2d 32 31 30 22 20 69 70 76 34 5f 64 73 74 20 7b 20
    payload: 0x 76 61 6c 75 65 3a 20 22 31 38 35 2e 31 36 38 2e 32 30 34 2e 30
    payload: 0x 22 20 70 72 65 66 69 78 5f 6c 65 6e 67 74 68 3a 20 32 38 20 7d
    payload: 0x 20 7d 20 61 63 74 69 6f 6e 20 7b 20 73 65 74 5f 77 63 6d 70 5f
    payload: 0x 67 72 6f 75 70 5f 69 64 5f 61 6e 64 5f 6d 65 74 61 64 61 74 61
    payload: 0x 20 7b 20 77 63 6d 70 5f 67 72 6f 75 70 5f 69 64 3a 20 22 67 72
    payload: 0x 6f 75 70 2d 34 32 39 34 39 33 34 35 37 38 22 20 72 6f 75 74 65
    payload: 0x 5f 6d 65 74 61 64 61 74 61 3a 20 22 30 78 30 31 22 20 7d 20 7d
    payload: 0x 20 7d
  )pb");
  RunPacketParseTest(
      "GRE Ipv4 Encapsulated with Ipv6 Header with checksum present (Valid)",
      R"pb(
        # Ethernet header
        ethernet_destination: 0x c2 01 51 fa 00 00
        ethernet_source: 0x c2 00 51 fa 00 00
        ethertype: 0x86DD
        # IPv6 header:
        version: 0x6
        dscp: 0b000000
        ecn: 0b00
        flow_label: 0x00000
        payload_length: 0x0122
        next_header: 0x2f  # GRE
        hop_limit: 0x3f
        ipv6_source: 0x2607F8B0C15000100000000000000000
        ipv6_destination: 0x20020A05686007490000000000000000
        # GRE header:
        checksum_present: 0b1
        reserved0: 0b000000000000
        version: 0b000
        protocol_type: 0x0800
        checksum: 0x77ff
        reserved1: 0x0000
        # Encapsulated IPv4 header
        version: 0x4
        ihl: 0x5
        dscp: 0b000000
        ecn: 0b00
        total_length: 0x011a
        identification: 0x0000
        flags: 0b000
        fragment_offset: 0b0000000000000
        ttl: 0x3f       # 63
        protocol: 0x01  # ICMP
        checksum: 0x753a
        ipv4_source: 0x 80 00 00 00       # 128.0.0.0
        ipv4_destination: 0x b9 a8 cc 00  # 185.168.204.0
        # ICMP header:
        type: 0x00
        code: 0x00
        checksum: 0x00e4
        rest_of_header: 0x 00 00 00 00
        # Payload
        payload:
            0x 74 65 73 74 20 70 61 63 6b 65 74 20 23 35 3a 20 52 4f 55 54 49
        payload:
            0x 4e 47 5f 50 49 4e 42 41 4c 4c 4c 33 54 4f 47 52 4f 55 50 5f 46
        payload:
            0x 4c 4f 57 3a 20 69 70 76 34 5F 74 61 62 6c 65 5f 65 6e 74 72 79
        payload:
            0x 20 09 20 7b 20 6d 61 74 63 68 20 7b 20 76 72 66 5f 69 64 3a 20
        payload:
            0x 22 76 72 66 2d 32 31 30 22 20 69 70 76 34 5f 64 73 74 20 7b 20
        payload:
            0x 76 61 6c 75 65 3a 20 22 31 38 35 2e 31 36 38 2e 32 30 34 2e 30
        payload:
            0x 22 20 70 72 65 66 69 78 5f 6c 65 6e 67 74 68 3a 20 32 38 20 7d
        payload:
            0x 20 7d 20 61 63 74 69 6f 6e 20 7b 20 73 65 74 5f 77 63 6d 70 5f
        payload:
            0x 67 72 6f 75 70 5f 69 64 5f 61 6e 64 5f 6d 65 74 61 64 61 74 61
        payload:
            0x 20 7b 20 77 63 6d 70 5f 67 72 6f 75 70 5f 69 64 3a 20 22 67 72
        payload:
            0x 6f 75 70 2d 34 32 39 34 39 33 34 35 37 38 22 20 72 6f 75 74 65
        payload:
            0x 5f 6d 65 74 61 64 61 74 61 3a 20 22 30 78 30 31 22 20 7d 20 7d
        payload: 0x 20 7d
      )pb");
  RunPacketParseTest(
      "SAI P4 BMv2 packet_in header (Valid)", R"pb(
        # SAI P4 BMv2 packet_in header
        ingress_port: 0b000000001
        target_egress_port: 0b000000010
        unused_pad: 0b000000
        # Ethernet header
        ethernet_destination: 0x ff ff ff ff ff ff
        ethernet_source: 0x 00 11 22 33 44 55
        ether_type: 0x0806
        # ARP header
        hardware_type: 0x0001  # Ethernet
        protocol_type: 0x0800  # IPv4
        hardware_length: 0x06
        protocol_length: 0x04
        operation: 0x0001  # Request
        sender_hardware_address: 0x 00 11 22 33 44 55
        sender_protocol_address: 0x 0a 00 00 01
        target_hardware_address: 0x 00 00 00 00 00 00
        target_protocol_address: 0x 0a 00 00 02
        # Payload
        payload: 0x 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
      )pb",
      /*first_header=*/Header::kSaiP4Bmv2PacketInHeader);
  RunPacketParseTest(
      "SAI P4 BMv2 packet_in header unused_pad value is not 0 (Invalid)",
      R"pb(
        # SAI P4 BMv2 packet_in header
        ingress_port: 0b000000001
        target_egress_port: 0b000000010
        unused_pad: 0b000001
        # Ethernet header
        ethernet_destination: 0x ff ff ff ff ff ff
        ethernet_source: 0x 00 11 22 33 44 55
        ether_type: 0x0806
        # ARP header
        hardware_type: 0x0001  # Ethernet
        protocol_type: 0x0800  # IPv4
        hardware_length: 0x06
        protocol_length: 0x04
        operation: 0x0001  # Request
        sender_hardware_address: 0x 00 11 22 33 44 55
        sender_protocol_address: 0x 0a 00 00 01
        target_hardware_address: 0x 00 00 00 00 00 00
        target_protocol_address: 0x 0a 00 00 02
        # Payload
        payload: 0x 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
      )pb",
      /*first_header=*/Header::kSaiP4Bmv2PacketInHeader);
  RunPacketParseTest("IPv6-in-IPv6 packet (valid)",
                     R"pb(
                       # Ethernet header.
                       ethernet_destination: 0xffeeddccbbaa
                       ethernet_source: 0x554433221100
                       ether_type: 0x86DD
                       # IPv6 header.
                       version: 0x6
                       dscp: 0b000000
                       ecn: 0b00
                       flow_label: 0x12345
                       payload_length: 0x0043
                       next_header: 0x29  # IPv6
                       hop_limit: 0x42
                       ipv6_source: 0x00001111222233334444555566667777
                       ipv6_destination: 0x88889999aaaabbbbccccddddeeeeffff
                       # IPv6 header.
                       version: 0x6
                       dscp: 0b000000
                       ecn: 0b00
                       flow_label: 0x12345
                       payload_length: 0x001b
                       next_header: 0xfd  # Experimental
                       hop_limit: 0x42
                       ipv6_source: 0x00001111222233334444555566667777
                       ipv6_destination: 0x88889999aaaabbbbccccddddeeeeffff
                       # Payload.
                       payload: "IPv6-in-IPv6 packet payload"
                     )pb");
  RunPacketParseTest("IPv4-in-IPv6 packet (valid except for computed fields)",
                     R"pb(
                       # Ethernet header.
                       ethernet_destination: 0xffeeddccbbaa
                       ethernet_source: 0x554433221100
                       ether_type: 0x86DD
                       # IPv6 header.
                       version: 0x6
                       dscp: 0b000000
                       ecn: 0b00
                       flow_label: 0x12345
                       payload_length: 0x0000
                       next_header: 0x04  # IPv4
                       hop_limit: 0x42
                       ipv6_source: 0x00001111222233334444555566667777
                       ipv6_destination: 0x88889999aaaabbbbccccddddeeeeffff
                       # IPv4 header.
                       version: 0x4
                       ihl: 0x5
                       dscp: 0b011011
                       ecn: 0b01
                       total_length: 0x0000
                       identification: 0x0000
                       flags: 0b000
                       fragment_offset: 0b0000000000000
                       ttl: 0x10
                       protocol: 0xfd  # Experimental
                       checksum: 0x0000
                       ipv4_source: 0xc0a8001f       # 192.168.0.31
                       ipv4_destination: 0xc0a8001e  # 192.168.0.30
                       # Payload.
                       payload: "IPv4-in-IPv6 packet payload"
                     )pb");
  RunPacketParseTest("IPv6-in-IPv4 packet (valid except for computed fields)",
                     R"pb(
                       # Ethernet header.
                       ethernet_destination: 0xffeeddccbbaa
                       ethernet_source: 0x554433221100
                       ether_type: 0x0800
                       # IPv4 header.
                       version: 0x4
                       ihl: 0x5
                       dscp: 0b011011
                       ecn: 0b01
                       total_length: 0x0000
                       identification: 0x0000
                       flags: 0b000
                       fragment_offset: 0b0000000000000
                       ttl: 0x10
                       protocol: 0x29  # IPv6
                       checksum: 0x0000
                       ipv4_source: 0xc0a8001f       # 192.168.0.31
                       ipv4_destination: 0xc0a8001e  # 192.168.0.30
                       # IPv6 header.
                       version: 0x6
                       dscp: 0b000000
                       ecn: 0b00
                       flow_label: 0x12345
                       payload_length: 0x0000
                       next_header: 0xfd  # Experimental
                       hop_limit: 0x42
                       ipv6_source: 0x00001111222233334444555566667777
                       ipv6_destination: 0x88889999aaaabbbbccccddddeeeeffff
                       # Payload.
                       payload: "IPv6-in-IPv4 packet payload"
                     )pb");
  RunPacketParseTest("IPv4-in-IPv4 packet (valid)",
                     R"pb(
                       # Ethernet header.
                       ethernet_destination: 0xffeeddccbbaa
                       ethernet_source: 0x554433221100
                       ether_type: 0x0800
                       # IPv4 header.
                       version: 0x4
                       ihl: 0x5
                       dscp: 0b011011
                       ecn: 0b01
                       total_length: 0x0043
                       identification: 0x2900
                       flags: 0b000
                       fragment_offset: 0b0000000000000
                       ttl: 0x10
                       protocol: 0x04  # IPv4
                       checksum: 0xffbc
                       ipv4_source: 0xc0a8001f       # 192.168.0.31
                       ipv4_destination: 0xc0a8001e  # 192.168.0.30
                       # IPv4 header.
                       version: 0x4
                       ihl: 0x5
                       dscp: 0b011011
                       ecn: 0b01
                       total_length: 0x002f
                       identification: 0x0000
                       flags: 0b000
                       fragment_offset: 0b0000000000000
                       ttl: 0x10
                       protocol: 0xfd  # Experimental
                       checksum: 0x27d8
                       ipv4_source: 0xc0a8001f       # 192.168.0.31
                       ipv4_destination: 0xc0a8001e  # 192.168.0.30
                       # Payload.
                       payload: "IPv4-in-IPv4 packet payload"
                     )pb");
  RunPacketParseTest(
      "PSAMP packet (valid)",
      R"pb(
        # Ethernet header.
        ethernet_destination: 0xffeeddccbbaa
        ethernet_source: 0x554433221100
        ether_type: 0x86DD
        # IPv6 header.
        version: 0x6
        dscp: 0b000000
        ecn: 0b00
        flow_label: 0x12345
        payload_length: 0x0046
        next_header: 0x11  # UDP
        hop_limit: 0x42
        ipv6_source: 0x00001111222233334444555566667777
        ipv6_destination: 0x88889999aaaabbbbccccddddeeeeffff
        # UDP Header
        source_port: 0x08ae       # 2222
        destination_port: 0x1283  # 4739
        length: 0x0046            # 70
        checksum: 0x0000          # Always zero for PSAMP
        # IPFIX Header
        version: 0x000A
        length: 0x003e
        export_time: 0x 64 c1 8c 23  # 1690405923 - 2023-07-26 5:12:03PM EST
        sequence_number: 0x00000001
        observation_domain_id: 0x00000001
        # PSAMP Header
        template_id: 0x0000
        length: 0x002e
        observation_time: 0x 17 75 87 3B 16 A1 9E 00  # 1690405923000000000
        flowset: 0x04D2                               # 1234
        next_hop_index: 0x0000
        epoch: 0xabcd
        ingress_port: 0x000d
        egress_port: 0x000f
        user_meta_field: 0x0000
        dlb_id: 0x00
        variable_length: 0xff
        packet_sampled_length: 0x0012
        # Payload - 18 octets
        payload: 0x 22 22 22 22 22 22 22 22
        payload: 0x 22 22 22 22 22 22 22 22
        payload: 0x 22 22
      )pb");
  RunPacketParseTest(
      "PSAMP packet (valid except for computed fields)",
      R"pb(
        # Ethernet header.
        ethernet_destination: 0xffeeddccbbaa
        ethernet_source: 0x554433221100
        ether_type: 0x86DD
        # IPv6 header.
        version: 0x6
        dscp: 0b000000
        ecn: 0b00
        flow_label: 0x12345
        payload_length: 0x0000
        next_header: 0x11  # UDP
        hop_limit: 0x42
        ipv6_source: 0x00001111222233334444555566667777
        ipv6_destination: 0x88889999aaaabbbbccccddddeeeeffff
        # UDP Header
        source_port: 0x08ae       # 2222
        destination_port: 0x1283  # 4739
        length: 0x0000
        checksum: 0x0012  # Always zero for PSAMP
        # IPFIX Header
        version: 0x000A
        length: 0x0000
        export_time: 0x 64 c1 8c 23  # 1690405923 - 2023-07-26 5:12:03PM EST
        sequence_number: 0x00000001
        observation_domain_id: 0x00000001
        # PSAMP Header
        template_id: 0x0000
        length: 0x0000
        observation_time: 0x 17 75 87 3B 16 A1 9E 00  # 1690405923000000000
        flowset: 0x04D2                               # 1234
        next_hop_index: 0x0000
        epoch: 0xabcd
        ingress_port: 0x000d
        egress_port: 0x000f
        user_meta_field: 0x0000
        dlb_id: 0x00
        variable_length: 0xff
        packet_sampled_length: 0x0013
        # Payload - 18 octets
        payload: 0x 22 22 22 22 22 22 22 22
        payload: 0x 22 22 22 22 22 22 22 22
        payload: 0x 22 22
      )pb");
  RunPacketParseTest("Inner and outer UDP checksums can both be zero (valid)",
                     R"pb(
                       # Ethernet header
                       ethernet_destination: 0xaabbccddeeff
                       ethernet_source: 0x112233445566
                       ethertype: 0x86DD
                       # IPv6 header.
                       version: 0x6
                       dscp: 0b000000
                       ecn: 0b00
                       flow_label: 0x12345
                       payload_length: 0x0032
                       next_header: 0x11  # UDP
                       hop_limit: 0x42
                       ipv6_source: 0x00001111222233334444555566667777
                       ipv6_destination: 0x88889999aaaabbbbccccddddeeeeffff
                       # UDP header
                       source_port: 0x0014
                       destination_port: 0x03e8  # 1000
                       length: 0x0032
                       checksum: 0x0000
                       # PSP Header
                       next_header: 0x11  # UDP
                       header_ext_length: 0x00
                       reserved0: 0b00
                       crypt_offset: 0b000010
                       sample_bit: 0b0
                       drop_bit: 0b0
                       version: 0x1
                       virtualization_cookie_present: 0b0
                       reserved1: 0b1
                       security_parameters_index: 0x00000000
                       initialization_vector: 0x0000000000000000
                       # Inner UDP Header
                       source_port: 0xbeef
                       destination_port: 0xabcd
                       length: 0x001a
                       checksum: 0x0000
                       # Payload - 18 octets
                       payload: 0x 22 22 22 22 22 22 22 22
                       payload: 0x 22 22 22 22 22 22 22 22
                       payload: 0x 22 22
                     )pb");
  RunPacketParseTest(
      "Inner UDP checksum can be anything, but the outer checksum must be "
      "correct (valid)",
      R"pb(
        # Ethernet header
        ethernet_destination: 0xaabbccddeeff
        ethernet_source: 0x112233445566
        ethertype: 0x86DD
        # IPv6 header.
        version: 0x6
        dscp: 0b000000
        ecn: 0b00
        flow_label: 0x12345
        payload_length: 0x0032
        next_header: 0x11  # UDP
        hop_limit: 0x42
        ipv6_source: 0x00001111222233334444555566667777
        ipv6_destination: 0x88889999aaaabbbbccccddddeeeeffff
        # UDP header
        source_port: 0x0014
        destination_port: 0x03e8  # 1000
        length: 0x0032
        checksum: 0x4a7d
        # PSP Header
        next_header: 0x11  # UDP
        header_ext_length: 0x00
        reserved0: 0b00
        crypt_offset: 0b000010
        sample_bit: 0b0
        drop_bit: 0b0
        version: 0x1
        virtualization_cookie_present: 0b0
        reserved1: 0b1
        security_parameters_index: 0x00000000
        initialization_vector: 0x0000000000000000
        # Inner UDP Header
        source_port: 0xbeef
        destination_port: 0xabcd
        length: 0x001a
        checksum: 0x0002
        # Payload - 18 octets
        payload: 0x 22 22 22 22 22 22 22 22
        payload: 0x 22 22 22 22 22 22 22 22
        payload: 0x 22 22
      )pb");
  RunPacketParseTest(
      "Inner UDP checksum can be anything, but the outer checksum must be "
      "correct (invalid)",
      R"pb(
        # Ethernet header
        ethernet_destination: 0xaabbccddeeff
        ethernet_source: 0x112233445566
        ethertype: 0x86DD
        # IPv6 header.
        version: 0x6
        dscp: 0b000000
        ecn: 0b00
        flow_label: 0x12345
        payload_length: 0x0032
        next_header: 0x11  # UDP
        hop_limit: 0x42
        ipv6_source: 0x00001111222233334444555566667777
        ipv6_destination: 0x88889999aaaabbbbccccddddeeeeffff
        # UDP header
        source_port: 0x0014
        destination_port: 0x03e8  # 1000
        length: 0x0032
        checksum: 0x0001
        # PSP Header
        next_header: 0x11  # UDP
        header_ext_length: 0x00
        reserved0: 0b00
        crypt_offset: 0b000010
        sample_bit: 0b0
        drop_bit: 0b0
        version: 0x1
        virtualization_cookie_present: 0b0
        reserved1: 0b1
        security_parameters_index: 0x00000000
        initialization_vector: 0x0000000000000000
        # Inner UDP Header
        source_port: 0xbeef
        destination_port: 0xabcd
        length: 0x001a
        checksum: 0x0001
        # Payload - 18 octets
        payload: 0x 22 22 22 22 22 22 22 22
        payload: 0x 22 22 22 22 22 22 22 22
        payload: 0x 22 22
      )pb");
  RunPacketParseTest("PSP packet unencrypted UDP (valid)",
                     R"pb(
                       # Ethernet header
                       ethernet_destination: 0xaabbccddeeff
                       ethernet_source: 0x112233445566
                       ethertype: 0x86DD
                       # IPv6 header.
                       version: 0x6
                       dscp: 0b000000
                       ecn: 0b00
                       flow_label: 0x12345
                       payload_length: 0x0032
                       next_header: 0x11  # UDP
                       hop_limit: 0x42
                       ipv6_source: 0x00001111222233334444555566667777
                       ipv6_destination: 0x88889999aaaabbbbccccddddeeeeffff
                       # UDP header
                       source_port: 0x0014
                       destination_port: 0x03e8  # 1000
                       length: 0x0032
                       checksum: 0x0000
                       # PSP Header
                       next_header: 0x11  # UDP
                       header_ext_length: 0x00
                       reserved0: 0b00
                       crypt_offset: 0b000010
                       sample_bit: 0b0
                       drop_bit: 0b0
                       version: 0x1
                       virtualization_cookie_present: 0b0
                       reserved1: 0b1
                       security_parameters_index: 0x00000000
                       initialization_vector: 0x0000000000000000
                       # Inner UDP Header
                       source_port: 0xbeef
                       destination_port: 0xabcd
                       length: 0x001a
                       checksum: 0x0025
                       # Payload - 18 octets
                       payload: 0x 22 22 22 22 22 22 22 22
                       payload: 0x 22 22 22 22 22 22 22 22
                       payload: 0x 22 22
                     )pb");
  RunPacketParseTest("PSP packet with encrypted UDP (valid)",
                     R"pb(
                       # Ethernet header
                       ethernet_destination: 0xaabbccddeeff
                       ethernet_source: 0x112233445566
                       ethertype: 0x86DD
                       # IPv6 header.
                       version: 0x6
                       dscp: 0b000000
                       ecn: 0b00
                       flow_label: 0x12345
                       payload_length: 0x002a
                       next_header: 0x11  # UDP
                       hop_limit: 0x42
                       ipv6_source: 0x00001111222233334444555566667777
                       ipv6_destination: 0x88889999aaaabbbbccccddddeeeeffff
                       # UDP header
                       source_port: 0x0014
                       destination_port: 0x03e8  # 1000
                       length: 0x002a
                       checksum: 0x0000
                       # PSP Header
                       next_header: 0x11  # UDP
                       header_ext_length: 0x00
                       reserved0: 0b00
                       crypt_offset: 0b000000
                       sample_bit: 0b0
                       drop_bit: 0b0
                       version: 0x1
                       virtualization_cookie_present: 0b0
                       reserved1: 0b1
                       security_parameters_index: 0x00000000
                       initialization_vector: 0x0000000000000000
                       # Payload - 18 octets
                       payload: 0x 22 22 22 22 22 22 22 22
                       payload: 0x 22 22 22 22 22 22 22 22
                       payload: 0x 22 22
                     )pb");
  RunPacketParseTest("PSP packet with virtualization cookie (unsupported)",
                     R"pb(
                       # Ethernet header
                       ethernet_destination: 0xaabbccddeeff
                       ethernet_source: 0x112233445566
                       ethertype: 0x86DD
                       # IPv6 header.
                       version: 0x6
                       dscp: 0b000000
                       ecn: 0b00
                       flow_label: 0x12345
                       payload_length: 0x002a
                       next_header: 0x11  # UDP
                       hop_limit: 0x42
                       ipv6_source: 0x00001111222233334444555566667777
                       ipv6_destination: 0x88889999aaaabbbbccccddddeeeeffff
                       # UDP header
                       source_port: 0x0014
                       destination_port: 0x03e8  # 1000
                       length: 0x002a
                       checksum: 0x0000
                       # PSP Header
                       next_header: 0x04
                       header_ext_length: 0x00
                       reserved0: 0b00
                       crypt_offset: 0b000000
                       sample_bit: 0b0
                       drop_bit: 0b0
                       version: 0x1
                       virtualization_cookie_present: 0b1
                       reserved1: 0b1
                       security_parameters_index: 0x00000000
                       initialization_vector: 0x0000000000000000
                       # Payload - 18 octets
                       payload: 0x 22 22 22 22 22 22 22 22
                       payload: 0x 22 22 22 22 22 22 22 22
                       payload: 0x 22 22
                     )pb");
  RunPacketParseTest("PSP packet that is too short (invalid)",
                     R"pb(
                       # Ethernet header
                       ethernet_destination: 0xaabbccddeeff
                       ethernet_source: 0x112233445566
                       ethertype: 0x86DD
                       # IPv6 header.
                       version: 0x6
                       dscp: 0b000000
                       ecn: 0b00
                       flow_label: 0x12345
                       payload_length: 0x0010
                       next_header: 0x11  # UDP
                       hop_limit: 0x42
                       ipv6_source: 0x00001111222233334444555566667777
                       ipv6_destination: 0x88889999aaaabbbbccccddddeeeeffff
                       # UDP header
                       source_port: 0x0014
                       destination_port: 0x03e8  # 1000
                       length: 0x0010
                       checksum: 0x0000
                       # PSP Header
                       next_header: 0x11  # UDP
                       header_ext_length: 0x00
                       reserved0: 0b00
                       crypt_offset: 0b000000
                       sample_bit: 0b0
                       drop_bit: 0b0
                       version: 0x1
                       virtualization_cookie_present: 0b0
                       reserved1: 0b1
                       security_parameters_index: 0x00000000
                     )pb");
}  // NOLINT(readability/fn_size)

void RunProtoPacketTests() {
  RunProtoPacketTest("UDP header not preceded by other header",
                     gutil::ParseProtoOrDie<Packet>(R"pb(
                       headers {
                         udp_header {
                           source_port: "0x0014"
                           destination_port: "0x000a"
                           length: "0x000a"
                           checksum: "0x35c5"
                         }
                       }
                       payload: "Hi"
                     )pb"));

  RunProtoPacketTest("UDP header not preceded by IP header",
                     gutil::ParseProtoOrDie<Packet>(R"pb(
                       headers {
                         ethernet_header {
                           ethernet_destination: "aa:bb:cc:dd:ee:ff"
                           ethernet_source: "11:22:33:44:55:66"
                           ethertype: "0x000a"
                         }
                       }
                       headers {
                         udp_header {
                           source_port: "0x0014"
                           destination_port: "0x000a"
                           length: "0x000a"
                           checksum: "0x35c5"
                         }
                       }
                       payload: "Hi"
                     )pb"));

  RunProtoPacketTest(
      "UDP header empty length and checksum",
      gutil::ParseProtoOrDie<Packet>(R"pb(
        headers {
          ethernet_header {
            ethernet_destination: "aa:bb:cc:dd:ee:ff"
            ethernet_source: "11:22:33:44:55:66"
            ethertype: "0x0800"
          }
        }
        headers {
          ipv4_header {
            version: "0x4"
            ihl: "0x5"
            dscp: "0x1b"
            ecn: "0x1"
            identification: "0x0000"
            flags: "0x0"
            fragment_offset: "0x0000"
            ttl: "0x10"
            protocol: "0x11"  # UDP
            ipv4_source: "192.168.0.31"
            ipv4_destination: "192.168.0.30"
          }
        }
        headers {
          udp_header { source_port: "0x0014" destination_port: "0x000a" }
        }
        payload: "Some random payload."
      )pb"));

  RunProtoPacketTest(
      "UDP header illegally succeeding IPv6 header whose next_header is not "
      "UDP",
      gutil::ParseProtoOrDie<Packet>(R"pb(
        headers {
          ethernet_header {
            ethernet_destination: "aa:bb:cc:dd:ee:ff"
            ethernet_source: "11:22:33:44:55:66"
            ethertype: "0x86dd"
          }
        }
        headers {
          ipv6_header {
            version: "0x6"
            dscp: "0x1b"
            ecn: "0x1"
            flow_label: "0x12345"
            payload_length: "0x000a"
            next_header: "0x90"  # some unassigned protocol
            hop_limit: "0x03"
            ipv6_source: "0000:1111:2222:3333:4444:5555:6666:7777"
            ipv6_destination: "8888:9999:aaaa:bbbb:cccc:dddd:eeee:ffff"
          }
        }
        headers {
          udp_header { source_port: "0x0014" destination_port: "0x000a" }
        }
        payload: "Hi"
      )pb"));

  RunProtoPacketTest("TCP header whose options field is not word-aligned",
                     gutil::ParseProtoOrDie<Packet>(R"pb(
                       headers {
                         tcp_header {
                           source_port: "0x0001"
                           destination_port: "0x0002"
                           sequence_number: "0x00000001"
                           acknowledgement_number: "0x00000000"
                           rest_of_header: "0x000000000000000"
                           uninterpreted_options: "0x00"
                         }
                       }
                     )pb"));

  RunProtoPacketTest(
      "TCP header whose options field is too long",
      gutil::ParseProtoOrDie<Packet>(R"pb(
        headers {
          tcp_header {
            source_port: "0x0001"
            destination_port: "0x0002"
            sequence_number: "0x00000001"
            acknowledgement_number: "0x00000000"
            rest_of_header: "0x000000000000000"
            uninterpreted_options: "0x0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"  # 11 * 32 bits
          }
        }
      )pb"));

  RunProtoPacketTest("IPv4 without computed fields",
                     gutil::ParseProtoOrDie<Packet>(R"pb(
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
                       payload: "payloads everywhere"
                     )pb"));

  RunProtoPacketTest("Ipv4 empty ihl, invalid options",
                     gutil::ParseProtoOrDie<Packet>(R"pb(
                       headers {
                         ethernet_header {
                           ethernet_destination: "aa:bb:cc:dd:ee:ff"
                           ethernet_source: "11:22:33:44:55:66"
                           ethertype: "0x0800"
                         }
                       }
                       headers {
                         ipv4_header {
                           version: "0x4"
                           dscp: "0x1b"
                           ecn: "0x1"
                           total_length: "0x0025"
                           identification: "0xa3cd"
                           flags: "0x0"
                           fragment_offset: "0x0000"
                           ttl: "0x10"
                           protocol: "0x05"  # some unsupported protocol
                           checksum: "0xe887"
                           ipv4_source: "10.0.0.1"
                           ipv4_destination: "20.0.0.3"
                           uninterpreted_options: "0x12"
                         }
                       }
                       payload: "A somewhat longer payload."
                     )pb"));

  RunProtoPacketTest("Ipv4 empty ihl, valid options",
                     gutil::ParseProtoOrDie<Packet>(R"pb(
                       headers {
                         ethernet_header {
                           ethernet_destination: "aa:bb:cc:dd:ee:ff"
                           ethernet_source: "11:22:33:44:55:66"
                           ethertype: "0x0800"
                         }
                       }
                       headers {
                         ipv4_header {
                           version: "0x4"
                           dscp: "0x011011"
                           ecn: "0x01"
                           total_length: "0x0034"
                           identification: "0xa3cd"
                           flags: "0x000"
                           fragment_offset: "0x0000000000000"
                           ttl: "0x10"
                           protocol: "0x05"  # some unsupported protocol
                           checksum: "0xe887"
                           ipv4_source: "0x0a000001"
                           ipv4_destination: "0x14000003"
                           uninterpreted_options: "0x12345678"
                         }
                       }
                       payload: "A somewhat longer payload."
                     )pb"));

  RunProtoPacketTest("IPv4 with various invalid fields",
                     gutil::ParseProtoOrDie<Packet>(R"pb(
                       headers {
                         ethernet_header {
                           ethernet_destination: "aa:bb:cc:dd:ee:ff"
                           ethertype: "0x0800"
                         }
                       }
                       headers {
                         ipv4_header {
                           version: "0x3"
                           ihl: "0x6k"
                           dscp: "0x1b"
                           ecn: "0x1"
                           identification: "0xa3cd"
                           flags: "0x0"
                           fragment_offset: "0x0000"
                           ttl: "0x10"
                           protocol: "0x05"
                           ipv4_source: "ffff:1::"
                           ipv4_destination: "20.0.0.3"
                         }
                       }
                       payload: "Hi"
                     )pb"));

  RunProtoPacketTest("IPv6 without computed fields",
                     gutil::ParseProtoOrDie<Packet>(R"pb(
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
                       payload: "Hello"
                     )pb"));

  RunProtoPacketTest("IPv6 with various invalid fields",
                     gutil::ParseProtoOrDie<Packet>(R"pb(
                       headers {
                         ethernet_header {
                           ethernet_destination: "aa:bb:cc:dd:ee:ff"
                           ethernet_source: "11:22:33:44:55:66"
                           ethertype: "0x86dd"
                         }
                       }
                       headers {
                         ipv6_header {
                           version: "0x4"
                           dscp: "1b"
                           ecn: "0b01"
                           flow_label: "0x1234"
                           payload_length: "0x0000"
                           next_header: "0x050"
                           hop_limit: "0x1"
                           ipv6_source: "20.0.0.3"
                           ipv6_destination: ":"
                         }
                       }
                       payload: "I am the payload"
                     )pb"));

  RunProtoPacketTest("IPv6 packet with IPv4 ethertype",
                     gutil::ParseProtoOrDie<Packet>(R"pb(
                       headers {
                         ethernet_header {
                           ethernet_destination: "aa:bb:cc:dd:ee:ff"
                           ethernet_source: "11:22:33:44:55:66"
                           ethertype: "0x0800"
                         }
                       }
                       headers {
                         ipv6_header {
                           version: "0x6"
                           dscp: "0x1b"
                           ecn: "0x1"
                           flow_label: "0x12345"
                           payload_length: "0x0000"
                           next_header: "0x05"
                           hop_limit: "0x10"
                           ipv6_source: "::"
                           ipv6_destination: "f::f"
                         }
                       }
                     )pb"));

  RunProtoPacketTest("IPv6 packet without IPv6 header",
                     gutil::ParseProtoOrDie<Packet>(R"pb(
                       headers {
                         ethernet_header {
                           ethernet_destination: "aa:bb:cc:dd:ee:ff"
                           ethernet_source: "11:22:33:44:55:66"
                           ethertype: "0x86dd"
                         }
                       }
                       payload: "hi"
                     )pb"));

  RunProtoPacketTest("ARP packet without computed fields",
                     gutil::ParseProtoOrDie<Packet>(
                         R"pb(
                           headers {
                             ethernet_header {
                               ethernet_destination: "ff:ff:ff:ff:ff:ff"
                               ethernet_source: "11:22:33:44:55:66"
                               ethertype: "0x0806"
                             }
                           }
                           headers {
                             arp_header {
                               operation: "0x0001"
                               sender_hardware_address: "11:22:33:44:55:66"
                               sender_protocol_address: "1.2.3.4"
                               target_hardware_address: "00:00:00:00:00:00"
                               target_protocol_address: "1.2.3.5"
                             }
                           }
                         )pb"));
  RunProtoPacketTest("ARP packet with unsupported computed field values",
                     gutil::ParseProtoOrDie<Packet>(
                         R"pb(
                           headers {
                             ethernet_header {
                               ethernet_destination: "ff:ff:ff:ff:ff:ff"
                               ethernet_source: "11:22:33:44:55:66"
                               ethertype: "0x0806"
                             }
                           }
                           headers {
                             arp_header {
                               hardware_type: "0x0002"
                               protocol_type: "0x0801"
                               hardware_length: "0x07"
                               protocol_length: "0x05"
                               operation: "0x0001"
                               sender_hardware_address: "11:22:33:44:55:66"
                               sender_protocol_address: "1.2.3.4"
                               target_hardware_address: "00:00:00:00:00:00"
                               target_protocol_address: "1.2.3.5"
                             }
                           }
                         )pb"));

  RunProtoPacketTest(
      "ICMPv4 packet without computed fields",
      gutil::ParseProtoOrDie<Packet>(R"pb(
        headers {
          ethernet_header {
            ethernet_destination: "08:00:20:86:35:4b"
            ethernet_source: "00:e0:f7:26:3f:e9"
            ethertype: "0x0800"
          }
        }
        headers {
          ipv4_header {
            dscp: "0x00"
            ecn: "0x0"
            identification: "0xaafb"
            flags: "0x2"
            fragment_offset: "0x0000"
            ttl: "0xfc"
            protocol: "0x01"
            ipv4_source: "139.133.233.2"
            ipv4_destination: "139.133.217.110"
          }
        }
        headers {
          icmp_header { type: "0x00" code: "0x00" rest_of_header: "0x1e600000" }
        }
        payload: "ICMPv4 packet without computed fields"
      )pb"));
  RunProtoPacketTest(
      "ICMPv6 packet without computed fields",
      gutil::ParseProtoOrDie<Packet>(R"pb(
        headers {
          ethernet_header {
            ethernet_destination: "c2:01:51:fa:00:00"
            ethernet_source: "c2:00:51:fa:00:00"
            ethertype: "0x86dd"
          }
        }
        headers {
          ipv6_header {
            dscp: "0x00"
            ecn: "0x0"
            flow_label: "0x00000"
            next_header: "0x3a"
            hop_limit: "0x40"
            ipv6_source: "2001:db8:0:12::1"
            ipv6_destination: "2001:db8:0:12::2"
          }
        }
        headers {
          icmp_header { type: "0x80" code: "0x00" rest_of_header: "0x110d0000" }
        }
        payload: "ICMPv6 packet without computed fields"
      )pb"));
  RunProtoPacketTest(
      "ICMP packet without a preceding IP header",
      gutil::ParseProtoOrDie<Packet>(R"pb(
        headers {
          ethernet_header {
            ethernet_destination: "c2:01:51:fa:00:00"
            ethernet_source: "c2:00:51:fa:00:00"
            ethertype: "0x86dd"
          }
        }
        headers {
          icmp_header { type: "0x80" code: "0x00" rest_of_header: "0x110d0000" }
        }
        payload: "ICMP packet without a preceding IP header"
      )pb"));
  RunProtoPacketTest("VLAN ARP packet",
                     gutil::ParseProtoOrDie<Packet>(
                         R"pb(
                           headers {
                             ethernet_header {
                               ethernet_destination: "ff:ff:ff:ff:ff:ff"
                               ethernet_source: "11:22:33:44:55:66"
                               ethertype: "0x8100"
                             }
                           }
                           headers {
                             vlan_header {
                               priority_code_point: "0x0"
                               drop_eligible_indicator: "0x1"
                               vlan_identifier: "0x123"
                               ethertype: "0x0806"
                             }
                           }
                           headers {
                             arp_header {
                               operation: "0x0001"
                               sender_hardware_address: "11:22:33:44:55:66"
                               sender_protocol_address: "1.2.3.4"
                               target_hardware_address: "00:00:00:00:00:00"
                               target_protocol_address: "1.2.3.5"
                             }
                           }
                         )pb"));
  RunProtoPacketTest("Uninitialized (empty packet) - should be invalid",
                     gutil::ParseProtoOrDie<Packet>(R"pb()pb"));
  RunProtoPacketTest(
      "GRE Ipv4 Encapsulated with Ipv6 Header (Valid)",
      gutil::ParseProtoOrDie<Packet>(R"pb(
        headers {
          ethernet_header {
            ethernet_destination: "c2:01:51:fa:00:00"
            ethernet_source: "c2:00:51:fa:00:00"
            ethertype: "0x86dd"
          }
        }
        headers {
          ipv6_header {
            version: "0x6"
            dscp: "0x00"
            ecn: "0x0"
            flow_label: "0x00000"
            payload_length: "0x011e"
            next_header: "0x2f"
            hop_limit: "0x3f"
            ipv6_source: "2607:f8b0:c150:10::"
            ipv6_destination: "2002:a05:6860:749::"
          }
        }
        headers {
          gre_header {
            checksum_present: "0x0"
            reserved0: "0x000"
            version: "0x0"
            protocol_type: "0x0800"
          }
        }
        headers {
          ipv4_header {
            version: "0x4"
            ihl: "0x5"
            dscp: "0x00"
            ecn: "0x0"
            total_length: "0x011a"
            identification: "0x0000"
            flags: "0x0"
            fragment_offset: "0x0000"
            ttl: "0x3f"
            protocol: "0x01"
            checksum: "0x753a"
            ipv4_source: "128.0.0.0"
            ipv4_destination: "185.168.204.0"
          }
        }
        headers {
          icmp_header {
            type: "0x00"
            code: "0x00"
            checksum: "0x00e4"
            rest_of_header: "0x00000000"
          }
        }
        payload: "test packet #5: ROUTING_PINBALLL3TOGROUP_FLOW: ipv4_table_entry \t { match { vrf_id: \"vrf-210\" ipv4_dst { value: \"185.168.204.0\" prefix_length: 28 } } action { set_wcmp_group_id_and_metadata { wcmp_group_id: \"group-4294934578\" route_metadata: \"0x01\" } } }"
      )pb"));
  RunProtoPacketTest("SAI P4 BMv2 packet_in Header (Valid)",
                     gutil::ParseProtoOrDie<Packet>(
                         R"pb(
                           headers {
                             sai_p4_bmv2_packet_in_header {
                               ingress_port: "0x001"
                               target_egress_port: "0x002"
                               unused_pad: "0x00"
                             }
                           }
                           headers {
                             ethernet_header {
                               ethernet_destination: "ff:ff:ff:ff:ff:ff"
                               ethernet_source: "11:22:33:44:55:66"
                               ethertype: "0x0806"
                             }
                           }
                           headers {
                             arp_header {
                               operation: "0x0001"
                               sender_hardware_address: "11:22:33:44:55:66"
                               sender_protocol_address: "1.2.3.4"
                               target_hardware_address: "00:00:00:00:00:00"
                               target_protocol_address: "1.2.3.5"
                             }
                           }
                         )pb"),
                     /*first_header=*/Header::kSaiP4Bmv2PacketInHeader);
  RunProtoPacketTest(
      "SAI P4 BMv2 packet_in Header ingress_port number out of range (Invalid)",
      gutil::ParseProtoOrDie<Packet>(
          R"pb(
            headers {
              sai_p4_bmv2_packet_in_header {
                ingress_port: "0xf00"
                target_egress_port: "0x002"
                unused_pad: "0x00"
              }
            }
            headers {
              ethernet_header {
                ethernet_destination: "ff:ff:ff:ff:ff:ff"
                ethernet_source: "11:22:33:44:55:66"
                ethertype: "0x0806"
              }
            }
            headers {
              arp_header {
                operation: "0x0001"
                sender_hardware_address: "11:22:33:44:55:66"
                sender_protocol_address: "1.2.3.4"
                target_hardware_address: "00:00:00:00:00:00"
                target_protocol_address: "1.2.3.5"
              }
            }
          )pb"),
      /*first_header=*/Header::kSaiP4Bmv2PacketInHeader);
  RunProtoPacketTest(
      "SAI P4 BMv2 packet_in Header target_egress_port number out of range "
      "(Invalid)",
      gutil::ParseProtoOrDie<Packet>(
          R"pb(
            headers {
              sai_p4_bmv2_packet_in_header {
                ingress_port: "0x001"
                target_egress_port: "0xf00"
                unused_pad: "0x00"
              }
            }
            headers {
              ethernet_header {
                ethernet_destination: "ff:ff:ff:ff:ff:ff"
                ethernet_source: "11:22:33:44:55:66"
                ethertype: "0x0806"
              }
            }
            headers {
              arp_header {
                operation: "0x0001"
                sender_hardware_address: "11:22:33:44:55:66"
                sender_protocol_address: "1.2.3.4"
                target_hardware_address: "00:00:00:00:00:00"
                target_protocol_address: "1.2.3.5"
              }
            }
          )pb"),
      /*first_header=*/Header::kSaiP4Bmv2PacketInHeader);
  RunProtoPacketTest(
      "PSAMP packet header (valid)", gutil::ParseProtoOrDie<Packet>(R"pb(
        headers {
          ethernet_header {
            ethernet_destination: "ff:ee:dd:cc:bb:aa"
            ethernet_source: "55:44:33:22:11:00"
            ethertype: "0x86dd"
          }
        }
        headers {
          ipv6_header {
            version: "0x6"
            dscp: "0x00"
            ecn: "0x0"
            flow_label: "0x12345"
            payload_length: "0x0046"
            next_header: "0x11"  # UDP
            hop_limit: "0x42"
            ipv6_source: "2607:f8b0:c150:10::"
            ipv6_destination: "2002:a05:6860:749::"
          }
        }
        headers {
          udp_header {
            source_port: "0x08ae"       # 2222
            destination_port: "0x1283"  # 4739
            length: "0x0046"            # 70
            checksum: "0x0000"
          }
        }
        headers {
          ipfix_header {
            version: "0x000a"
            length: "0x003e"
            export_time: "0x64c18c23"  # 1690405923 - 2023-07-26 5:12:03PM EST
            sequence_number: "0x00000001"
            observation_domain_id: "0x00000001"
          }
        }
        headers {
          psamp_header {
            template_id: "0x0000"
            length: "0x002e"
            observation_time: "0x1775873b16a19e00"  # 1690405923000000000
            flowset: "0x04d2"                       # 1234
            next_hop_index: "0x0000"
            epoch: "0xabcd"
            ingress_port: "0x000d"
            egress_port: "0x000f"
            user_meta_field: "0x0000"
            dlb_id: "0x00"
            variable_length: "0xff"
            packet_sampled_length: "0x0012"
          }
        }
        payload: "AAAAAAAAAAAAAAAAAA"  # 18 octets
      )pb"));
  // UpdateMissingComputedFields should not update anything here - all fields
  // are in place but not correct.
  RunProtoPacketTest(
      "PSAMP packet header (length of IPFIX & PSAMP is invalid)",
      gutil::ParseProtoOrDie<Packet>(R"pb(
        headers {
          ethernet_header {
            ethernet_destination: "ff:ee:dd:cc:bb:aa"
            ethernet_source: "55:44:33:22:11:00"
            ethertype: "0x86dd"
          }
        }
        headers {
          ipv6_header {
            version: "0x6"
            dscp: "0x00"
            ecn: "0x0"
            flow_label: "0x12345"
            payload_length: "0x0046"
            next_header: "0x11"  # UDP
            hop_limit: "0x42"
            ipv6_source: "2607:f8b0:c150:10::"
            ipv6_destination: "2002:a05:6860:749::"
          }
        }
        headers {
          udp_header {
            source_port: "0x08ae"       # 2222
            destination_port: "0x1283"  # 4739
            length: "0x0046"            # 70
            checksum: "0x0000"
          }
        }
        headers {
          ipfix_header {
            version: "0x000a"
            length: "0x0000"
            export_time: "0x64c18c23"  # 1690405923 - 2023-07-26 5:12:03PM EST
            sequence_number: "0x00000001"
            observation_domain_id: "0x00000001"
          }
        }
        headers {
          psamp_header {
            template_id: "0x0000"
            length: "0x0000"
            observation_time: "0x1775873b16a19e00"  # 1690405923000000000
            flowset: "0x04d2"                       # 1234
            next_hop_index: "0x0000"
            epoch: "0xabcd"
            ingress_port: "0x000d"
            egress_port: "0x000f"
            user_meta_field: "0x0000"
            dlb_id: "0x00"
            variable_length: "0xff"
            packet_sampled_length: "0x0001"
          }
        }
        payload: "AAAAAAAAAAAAAAAAAA"  # 18 octets
      )pb"));
  RunProtoPacketTest(
      "PSAMP packet header (UDP checksum invalid)",
      gutil::ParseProtoOrDie<Packet>(R"pb(
        headers {
          ethernet_header {
            ethernet_destination: "ff:ee:dd:cc:bb:aa"
            ethernet_source: "55:44:33:22:11:00"
            ethertype: "0x86dd"
          }
        }
        headers {
          ipv6_header {
            version: "0x6"
            dscp: "0x00"
            ecn: "0x0"
            flow_label: "0x12345"
            payload_length: "0x0046"
            next_header: "0x11"  # UDP
            hop_limit: "0x42"
            ipv6_source: "2607:f8b0:c150:10::"
            ipv6_destination: "2002:a05:6860:749::"
          }
        }
        headers {
          udp_header {
            source_port: "0x08ae"       # 2222
            destination_port: "0x1283"  # 4739
            length: "0x0046"            # 70
            checksum: "0x0011"
          }
        }
        headers {
          ipfix_header {
            version: "0x000a"
            length: "0x003e"
            export_time: "0x64c18c23"  # 1690405923 - 2023-07-26 5:12:03PM EST
            sequence_number: "0x00000001"
            observation_domain_id: "0x00000001"
          }
        }
        headers {
          psamp_header {
            template_id: "0x0000"
            length: "0x002e"
            observation_time: "0x1775873b16a19e00"  # 1690405923000000000
            flowset: "0x04d2"                       # 1234
            next_hop_index: "0x0000"
            epoch: "0xabcd"
            ingress_port: "0x000d"
            egress_port: "0x000f"
            user_meta_field: "0x0000"
            dlb_id: "0x00"
            variable_length: "0xff"
            packet_sampled_length: "0x0012"
          }
        }
        payload: "AAAAAAAAAAAAAAAAAA"  # 18 octets
      )pb"));
  RunProtoPacketTest("PSP packet with UDP port 1000 (valid)",
                     gutil::ParseProtoOrDie<Packet>(
                         R"pb(headers {
                                ethernet_header {
                                  ethernet_destination: "00:ee:dd:cc:bb:aa"
                                  ethernet_source: "00:44:33:22:11:00"
                                  ethertype: "0x86dd"
                                }
                              }
                              headers {
                                ipv6_header {
                                  version: "0x6"
                                  dscp: "0x00"
                                  ecn: "0x0"
                                  flow_label: "0x12345"
                                  payload_length: "0x0034"
                                  next_header: "0x11"  # UDP
                                  hop_limit: "0x42"
                                  ipv6_source: "2607:f8b0:11::"
                                  ipv6_destination: "2607:f8b0:12::"
                                }
                              }
                              headers {
                                udp_header {
                                  source_port: "0x08ae"       # 2222
                                  destination_port: "0x03e8"  # 1000
                                  length: "0x0034"
                                  checksum: "0x0000"
                                }
                              }
                              headers {
                                psp_header {
                                  next_header: "0x11"
                                  header_ext_length: "0x00"
                                  reserved0: "0x0"
                                  crypt_offset: "0x02"
                                  sample_bit: "0x0"
                                  drop_bit: "0x0"
                                  version: "0x1"
                                  virtualization_cookie_present: "0x0"
                                  reserved1: "0x1"
                                  security_parameters_index: "0x00000000"
                                  initialization_vector: "0x0000000000000000"
                                }
                              }
                              headers {
                                udp_header {
                                  source_port: "0xbeef"
                                  destination_port: "0xabcd"
                                  length: "0x001c"
                                  checksum: "0xfe85"
                                }
                              }
                              payload: "ABCDABCDABCDABCDABCD"  # 20 octets
                         )pb"));
  RunProtoPacketTest(
      "PSP packet with empty computed fields (valid except for computed "
      "fields)",
      gutil::ParseProtoOrDie<Packet>(
          R"pb(headers {
                 ethernet_header {
                   ethernet_destination: "00:ee:dd:cc:bb:aa"
                   ethernet_source: "00:44:33:22:11:00"
                   ethertype: "0x86dd"
                 }
               }
               headers {
                 ipv6_header {
                   version: "0x6"
                   dscp: "0x00"
                   ecn: "0x0"
                   flow_label: "0x12345"
                   next_header: "0x11"  # UDP
                   hop_limit: "0x42"
                   ipv6_source: "2607:f8b0:11::"
                   ipv6_destination: "2607:f8b0:12::"
                 }
               }
               headers {
                 udp_header {
                   source_port: "0x08ae"       # 2222
                   destination_port: "0x03e8"  # 1000
                 }
               }
               headers {
                 psp_header {
                   next_header: "0x11"
                   header_ext_length: "0x00"
                   reserved0: "0x0"
                   crypt_offset: "0x02"
                   sample_bit: "0x0"
                   drop_bit: "0x0"
                   version: "0x1"
                   virtualization_cookie_present: "0x0"
                   reserved1: "0x1"
                   security_parameters_index: "0x00000000"
                   initialization_vector: "0x0000000000000000"
                 }
               }
               headers {
                 udp_header { source_port: "0xbeef" destination_port: "0xabcd" }
               }
               payload: "ABCDABCDABCDABCDABCD"  # 20 octets
          )pb"));
  RunProtoPacketTest("PSP packet with encrypted payload (valid)",
                     gutil::ParseProtoOrDie<Packet>(
                         R"pb(headers {
                                ethernet_header {
                                  ethernet_destination: "00:ee:dd:cc:bb:aa"
                                  ethernet_source: "00:44:33:22:11:00"
                                  ethertype: "0x86dd"
                                }
                              }
                              headers {
                                ipv6_header {
                                  version: "0x6"
                                  dscp: "0x00"
                                  ecn: "0x0"
                                  flow_label: "0x12345"
                                  payload_length: "0x002c"
                                  next_header: "0x11"  # UDP
                                  hop_limit: "0x42"
                                  ipv6_source: "2607:f8b0:11::"
                                  ipv6_destination: "2607:f8b0:12::"
                                }
                              }
                              headers {
                                udp_header {
                                  source_port: "0x08ae"       # 2222
                                  destination_port: "0x03e8"  # 1000
                                  length: "0x002c"
                                  checksum: "0x0000"
                                }
                              }
                              headers {
                                psp_header {
                                  next_header: "0x04"
                                  header_ext_length: "0x00"
                                  reserved0: "0x0"
                                  crypt_offset: "0x00"
                                  sample_bit: "0x0"
                                  drop_bit: "0x0"
                                  version: "0x1"
                                  virtualization_cookie_present: "0x1"
                                  reserved1: "0x1"
                                  security_parameters_index: "0x00000000"
                                  initialization_vector: "0x0000000000000000"
                                }
                              }
                              payload: "ABCDABCDABCDABCDABCD"  # 20 octets
                         )pb"));
  RunProtoPacketTest(
      "PSP packet with UDP payload but not crypt_offset (invalid)",
      gutil::ParseProtoOrDie<Packet>(
          R"pb(headers {
                 ethernet_header {
                   ethernet_destination: "00:ee:dd:cc:bb:aa"
                   ethernet_source: "00:44:33:22:11:00"
                   ethertype: "0x86dd"
                 }
               }
               headers {
                 ipv6_header {
                   version: "0x6"
                   dscp: "0x00"
                   ecn: "0x0"
                   flow_label: "0x12345"
                   payload_length: "0x0034"
                   next_header: "0x11"  # UDP
                   hop_limit: "0x42"
                   ipv6_source: "2607:f8b0:11::"
                   ipv6_destination: "2607:f8b0:12::"
                 }
               }
               headers {
                 udp_header {
                   source_port: "0x08ae"
                   destination_port: "0x03e8"  # 1000
                   length: "0x0034"
                   checksum: "0x0000"
                 }
               }
               headers {
                 psp_header {
                   next_header: "0x11"
                   header_ext_length: "0x00"
                   reserved0: "0x0"
                   crypt_offset: "0x00"
                   sample_bit: "0x0"
                   drop_bit: "0x0"
                   version: "0x1"
                   virtualization_cookie_present: "0x0"
                   reserved1: "0x1"
                   security_parameters_index: "0x00000000"
                   initialization_vector: "0x0000000000000000"
                 }
               }
               headers {
                 udp_header {
                   source_port: "0xbeef"
                   destination_port: "0xabcd"
                   length: "0x001c"
                   checksum: "0xfe85"
                 }
               }
               payload: "ABCDABCDABCDABCDABCD"  # 20 octets
          )pb"));
  RunProtoPacketTest("PSP packet with UDP port 1001 (invalid)",
                     gutil::ParseProtoOrDie<Packet>(
                         R"pb(headers {
                                ethernet_header {
                                  ethernet_destination: "00:ee:dd:cc:bb:aa"
                                  ethernet_source: "00:44:33:22:11:00"
                                  ethertype: "0x86dd"
                                }
                              }
                              headers {
                                ipv6_header {
                                  version: "0x6"
                                  dscp: "0x00"
                                  ecn: "0x0"
                                  flow_label: "0x12345"
                                  payload_length: "0x002c"
                                  next_header: "0x11"  # UDP
                                  hop_limit: "0x42"
                                  ipv6_source: "2607:f8b0:11::"
                                  ipv6_destination: "2607:f8b0:12::"
                                }
                              }
                              headers {
                                udp_header {
                                  source_port: "0x08ae"       # 2222
                                  destination_port: "0x03e9"  # 1001
                                  length: "0x002c"
                                  checksum: "0x0000"
                                }
                              }
                              headers {
                                psp_header {
                                  next_header: "0x11"
                                  header_ext_length: "0x00"
                                  reserved0: "0x0"
                                  crypt_offset: "0x00"
                                  sample_bit: "0x0"
                                  drop_bit: "0x0"
                                  version: "0x1"
                                  virtualization_cookie_present: "0x0"
                                  reserved1: "0x1"
                                  security_parameters_index: "0x00000000"
                                  initialization_vector: "0x0000000000000000"
                                }
                              }
                              payload: "ABCDABCDABCDABCDABCD"  # 20 octets
                         )pb"));
  RunProtoPacketTest("PSP packet with wrong reserved values (invalid)",
                     gutil::ParseProtoOrDie<Packet>(
                         R"pb(headers {
                                ethernet_header {
                                  ethernet_destination: "00:ee:dd:cc:bb:aa"
                                  ethernet_source: "00:44:33:22:11:00"
                                  ethertype: "0x86dd"
                                }
                              }
                              headers {
                                ipv6_header {
                                  version: "0x6"
                                  dscp: "0x00"
                                  ecn: "0x0"
                                  flow_label: "0x12345"
                                  payload_length: "0x002c"
                                  next_header: "0x11"  # UDP
                                  hop_limit: "0x42"
                                  ipv6_source: "2607:f8b0:11::"
                                  ipv6_destination: "2607:f8b0:12::"
                                }
                              }
                              headers {
                                udp_header {
                                  source_port: "0x08ae"       # 2222
                                  destination_port: "0x03e8"  # 1000
                                  length: "0x002c"
                                  checksum: "0x0000"
                                }
                              }
                              headers {
                                psp_header {
                                  next_header: "0x11"
                                  header_ext_length: "0x00"
                                  reserved0: "0x1"
                                  crypt_offset: "0x00"
                                  sample_bit: "0x0"
                                  drop_bit: "0x0"
                                  version: "0x1"
                                  virtualization_cookie_present: "0x0"
                                  reserved1: "0x0"
                                  security_parameters_index: "0x00000000"
                                  initialization_vector: "0x0000000000000000"
                                }
                              }
                              payload: "ABCDABCDABCDABCDABCD"  # 20 octets
                         )pb"));
}  // NOLINT(readability/fn_size)

void main() {
  RunPacketParseTests();
  RunProtoPacketTests();
}

}  // namespace packetlib

int main() {
  packetlib::main();
  return 0;
}
