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
#include <string>

#include "absl/log/check.h"
#include "absl/log/log.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_infra/p4_pdpi/string_encodings/readable_byte_string.h"

// This file contains tests for manually debugging the packetlib library. If
// you're adding a new test it should focus on general library behaviors:
//   * Parsing a byte string
//   * Update computable fields and validate the packet

namespace packetlib {
namespace {

using ::testing::IsEmpty;

class PacketlibParsingTest : public testing::Test {
 public:
  std::string ByteStringToTest() const {
    auto byte_string =
        pdpi::ReadableByteStringToByteString(readable_byte_string_);
    CHECK_OK(byte_string.status());  // CRASH OK
    return *byte_string;
  }

  const Header::HeaderCase first_header_ = Header::kEthernetHeader;
  const std::string readable_byte_string_ = R"pb(
    # ethernet header
    ethernet_destination: 0xaabbccddeeff
    ethernet_source: 0x112233445566
    ether_type: 0x002e
    # payload
    payload: 0x00 11 22 33 44 55 66 77 88 99 aa bb cc dd ee ff
    payload: 0x00 11 22 33 44 55 66 77 88 99 aa bb cc dd ee ff
    payload: 0x00 11 22 33 44 55 66 77 88 99 aa bb cc dd
  )pb";
};

TEST_F(PacketlibParsingTest, CanParseThePacket) {
  Packet result = ParsePacket(ByteStringToTest(), first_header_);
  EXPECT_THAT(result.reason_not_fully_parsed(), IsEmpty());
  EXPECT_THAT(result.reasons_invalid(), IsEmpty());
}

TEST_F(PacketlibParsingTest, CanUpdateAndParseThePacket) {
  Packet packet = ParsePacket(ByteStringToTest(), first_header_);

  ASSERT_OK(PadPacketToMinimumSize(packet));
  ASSERT_OK(UpdateAllComputedFields(packet));
  packet.clear_reason_not_fully_parsed();
  packet.clear_reasons_invalid();

  LOG(INFO) << "Updated packet: " << packet.ShortDebugString();
  EXPECT_OK(ValidatePacket(packet));
}

class PacketlibProtoPacketTest : public testing::Test {
 public:
  Packet PacketToTest() const {
    return gutil::ParseProtoOrDie<Packet>(packet_proto_string_);
  }

  const Header::HeaderCase first_header_ = Header::kEthernetHeader;
  const std::string packet_proto_string_ = R"pb(
    headers {
      ethernet_header {
        ethernet_destination: "aa:bb:cc:dd:ee:ff"
        ethernet_source: "11:22:33:44:55:66"
        ethertype: "0x000f"
      }
    }
    payload: "random payload."
  )pb";
};

TEST_F(PacketlibProtoPacketTest, IsAValidPacket) {
  EXPECT_OK(ValidatePacket(PacketToTest()));
}

TEST_F(PacketlibProtoPacketTest, UpdatedPacketIsAValid) {
  Packet packet = PacketToTest();
  ASSERT_OK(PadPacketToMinimumSize(packet));
  ASSERT_OK(UpdateAllComputedFields(packet));

  
  LOG(INFO) << "Updated packet: " << packet.ShortDebugString();
  EXPECT_OK(ValidatePacket(packet));
} 

}  // namespace
}  // namespace packetlib
