// Copyright 2021 Google LLC
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
#include "p4_infra/p4_pdpi/netaddr/mac_address.h"

#include <cstdint>
#include <string>
#include <vector>

#include "absl/strings/ascii.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "p4_infra/p4_pdpi/netaddr/network_address.h"
#include "p4_infra/p4_pdpi/string_encodings/safe.h"

namespace netaddr {
namespace {

using ::gutil::IsOk;
using ::gutil::IsOkAndHolds;
using ::testing::Eq;
using ::testing::Not;

// An MAC address, in 3 different representations.
struct MacTriple {
  // Cannonical representation
  std::string canonical_notation;
  // Other legal human readable strings, e.g. using uppercase.
  std::vector<std::string> alternative_notations;
  // Padded byte string (big-endian).
  std::string byte_string;
  MacAddress mac;
};

std::vector<MacTriple> CorrectMacTriples() {
  std::vector<MacTriple> triples;

  triples.push_back(MacTriple{
      .canonical_notation = "00:00:00:00:00:00",
      .alternative_notations = {"00:00:00:00:0:0", "0:0:0:0:0:0"},
      .byte_string = pdpi::SafeString({0, 0, 0, 0, 0, 0}),
      .mac = MacAddress::AllZeros(),
  });
  triples.push_back(MacTriple{
      .canonical_notation = "01:23:45:67:89:ab",
      .alternative_notations = {"01:23:45:67:89:ab", "1:23:45:67:89:ab",
                                "01:23:45:67:89:Ab"},
      .byte_string = pdpi::SafeString({0x01, 0x23, 0x45, 0x67, 0x89, 0xab}),
      .mac = MacAddress(0x01, 0x23, 0x45, 0x67, 0x89, 0xab),
  });
  triples.push_back(MacTriple{
      .canonical_notation = "ff:ff:ff:ff:ff:ff",
      .alternative_notations = {"ff:ff:ff:FF:fF:ff", "FF:FF:FF:FF:FF:FF"},
      .byte_string = pdpi::SafeString({0xff, 0xff, 0xff, 0xff, 0xff, 0xff}),
      .mac = MacAddress::AllOnes(),
  });

  return triples;
}

TEST(MacAddressTest, ConversionsCorrect) {
  for (auto [canonical_notation, alternative_notations, byte_string, mac] :
       CorrectMacTriples()) {
    EXPECT_THAT(mac.ToPaddedByteString(), byte_string);
    EXPECT_THAT(mac.ToString(), canonical_notation);
    EXPECT_THAT(MacAddress::OfString(canonical_notation), IsOkAndHolds(Eq(mac)))
        << canonical_notation;
    alternative_notations.push_back(absl::AsciiStrToUpper(canonical_notation));
    for (const auto& notation : alternative_notations) {
      EXPECT_THAT(MacAddress::OfString(notation), IsOkAndHolds(Eq(mac)))
          << notation;
    }
  }
}

std::vector<std::string> IncorrectMacStrings() {
  return std::vector<std::string>{
      // Nonsense.
      ":",
      "",
      "192.168.2.1",
      "11:22:33:44:55::66",
      "11:22:33:44::66",
      // Too short.
      "11",
      "11:22",
      "11:22:33",
      "11:22:33:44",
      "11:22:33:44:55",
      // Too long.
      "11:22:33:44:55:66:77",
      "11:22:33:44:55:66:77:88",
      "11:22:33:44:55:66:77:88:99",
  };
}

TEST(MacAddressTest, Ipv6AddressOfString_NegativeTests) {
  for (std::string mac_str : IncorrectMacStrings()) {
    EXPECT_THAT(MacAddress::OfString(mac_str), Not(IsOk()))
        << "mac_str = " << mac_str;
  }
}

struct MacAndCoresspondingLinkLocalIpv6Address {
  std::string mac;
  std::string ip;
};

std::vector<MacAndCoresspondingLinkLocalIpv6Address>
ValidMacAndCorrespondLinkLocalIpv6Addresses() {
  // Cases can be generated using tools such as https://ben.akrin.com/?p=1347.
  return {
      // Format: {<MAC address>, <link local IPv6 address>}.
      {"00:00:00:00:00:00", "fe80::200:00ff:fe00:0000"},
      {"ff:ff:ff:ff:ff:ff", "fe80::fdff:ffff:feff:ffff"},
      {"01:23:45:67:89:ab", "fe80::323:45ff:fe67:89ab"},
  };
}

std::vector<std::string> InvalidLinkLocalIpv6Addresses() {
  std::vector<std::string> result = {
      "::",
      "fe80::",
  };
  // Take valid IP, and flip one bit to make it invalid.
  for (auto& [_, ip_str] : ValidMacAndCorrespondLinkLocalIpv6Addresses()) {
    auto ip = Ipv6Address::OfString(ip_str).value();  // Crash ok: test code.
    // The upper 64 bits must be equal to fe80::/64.
    for (int i = 64; i < 128; ++i) {
      auto one_hot = Ipv6Address(std::bitset<128>(1) << i);
      result.push_back((ip ^ one_hot).ToString());
    }
    // The middle bits of the lower 64 bits must be equal to ff fe.
    for (int i = 24; i < 32; ++i) {
      auto one_hot = Ipv6Address(std::bitset<128>(1) << i);
      result.push_back((ip ^ one_hot).ToString());
    }
  }
  return result;
}

// Also covers OfInterfaceId.
TEST(MacAddressTest, OfLinkLocalIpv6Address) {
  for (auto& [mac_str, ip_str] :
       ValidMacAndCorrespondLinkLocalIpv6Addresses()) {
    ASSERT_OK_AND_ASSIGN(auto mac, MacAddress::OfString(mac_str));
    ASSERT_OK_AND_ASSIGN(auto ip, Ipv6Address::OfString(ip_str));
    ASSERT_OK_AND_ASSIGN(auto extracted_mac,
                         MacAddress::OfLinkLocalIpv6Address(ip));
    EXPECT_THAT(extracted_mac, Eq(mac)) << " where ip = " << ip;
  }
}

// Also covers OfInterfaceId.
TEST(MacAddressTest, OfLinkLocalIpv6AddressRejectsInvalidAddresses) {
  for (auto& ip_str : InvalidLinkLocalIpv6Addresses()) {
    ASSERT_OK_AND_ASSIGN(auto ip, Ipv6Address::OfString(ip_str));
    EXPECT_THAT(MacAddress::OfLinkLocalIpv6Address(ip),
                gutil::StatusIs(absl::StatusCode::kInvalidArgument))
        << "where ip = " << ip;
  }
}

// Also covers ToInterfaceId.
TEST(MacAddressTest, ToLinkLocalIpv6Address) {
  // Cases can be generated using tools such as https://ben.akrin.com/?p=1347.
  std::vector<std::pair<std::string, std::string>> test_cases = {
      // Format: {<MAC address>, <link local IPv6 address>}.
      {"00:00:00:00:00:00", "fe80::200:00ff:fe00:0000"},
      {"ff:ff:ff:ff:ff:ff", "fe80::fdff:ffff:feff:ffff"},
      {"01:23:45:67:89:ab", "fe80::323:45ff:fe67:89ab"},
  };

  for (auto& [mac_str, ip_str] : test_cases) {
    ASSERT_OK_AND_ASSIGN(auto mac, MacAddress::OfString(mac_str));
    ASSERT_OK_AND_ASSIGN(auto ip, Ipv6Address::OfString(ip_str));
    EXPECT_THAT(mac.ToLinkLocalIpv6Address(), Eq(ip)) << " where mac = " << mac;
  }
}

}  // namespace
}  // namespace netaddr
