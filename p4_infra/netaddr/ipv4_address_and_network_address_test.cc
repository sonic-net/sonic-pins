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
#include <bitset>
#include <cstdint>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/strings/escaping.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "p4_infra/netaddr/ipv4_address.h"
#include "p4_infra/string_encodings/safe.h"

// This file serves double duty, testing both Ipv4Address and the template class
// NetworkAddress from which Ipv4Address derives.
//
// For other classes derived from NetworkAddress, it suffices to test the
// non-inherited functions.

namespace netaddr {
namespace {

using ::gutil::IsOk;
using ::gutil::IsOkAndHolds;
using ::string_encodings::SafeString;
using ::testing::Eq;
using ::testing::Not;

constexpr std::pair<Ipv4Address, absl::string_view> kIpsAndIpStrings[]{
    {Ipv4Address(0, 0, 0, 0), "0.0.0.0"},
    {Ipv4Address(255, 255, 255, 255), "255.255.255.255"},
    {Ipv4Address(1, 1, 1, 1), "1.1.1.1"},
    {Ipv4Address(10, 0, 0, 2), "10.0.0.2"},
    {Ipv4Address(192, 168, 2, 1), "192.168.2.1"},
};

constexpr absl::string_view kBadIpStrings[]{
    "0.0.0",        "255.256.255.255", "1",           "0",
    "192.168.+1.2", "a.a.a.a",         "00:00:00:00", "",
};

absl::flat_hash_map<Ipv4Address, std::string> IpsAndPaddedByteStrings() {
  return {
      {Ipv4Address(0, 0, 0, 0), SafeString({0, 0, 0, 0})},
      {Ipv4Address(255, 255, 255, 255), SafeString({255, 255, 255, 255})},
      {Ipv4Address(1, 1, 1, 1), SafeString({1, 1, 1, 1})},
      {Ipv4Address(10, 0, 0, 2), SafeString({10, 0, 0, 2})},
      {Ipv4Address(192, 168, 2, 1), SafeString({192, 168, 2, 1})},
      {Ipv4Address(0, 0, 2, 1), SafeString({0, 0, 2, 1})},
  };
}

absl::flat_hash_map<Ipv4Address, std::string> IpsAndP4RuntimeByteStrings() {
  return {
      {Ipv4Address(0, 0, 0, 0), SafeString({0})},
      {Ipv4Address(255, 255, 255, 255), SafeString({255, 255, 255, 255})},
      {Ipv4Address(1, 1, 1, 1), SafeString({1, 1, 1, 1})},
      {Ipv4Address(0, 1, 1, 1), SafeString({1, 1, 1})},
      {Ipv4Address(0, 0, 1, 1), SafeString({1, 1})},
      {Ipv4Address(0, 0, 0, 1), SafeString({1})},
      {Ipv4Address(10, 0, 0, 0), SafeString({10, 0, 0, 0})},
  };
}

TEST(Ipv4AddressTest, OfStringSuccess) {
  for (auto& [ip, ip_str] : kIpsAndIpStrings) {
    EXPECT_THAT(Ipv4Address::OfString(ip_str), IsOkAndHolds(Eq(ip))) << ip_str;
  }
}

TEST(Ipv4AddressTest, ToStringSuccess) {
  for (auto& [ip, ip_str] : kIpsAndIpStrings) {
    EXPECT_EQ(ip.ToString(), ip_str);
  }
}

TEST(Ipv4AddressTest, OfStringFails) {
  for (absl::string_view bad_ip_str : kBadIpStrings) {
    EXPECT_THAT(Ipv4Address::OfString(bad_ip_str), Not(IsOk())) << bad_ip_str;
  }
}

TEST(Ipv4AddressTest, IpsAreHashableAndDistinct) {
  absl::flat_hash_map<Ipv4Address, absl::string_view> ip_string_by_ip;
  for (auto& [ip, ip_str] : kIpsAndIpStrings) {
    ASSERT_FALSE(ip_string_by_ip.contains(ip))
        << ip_str << " and " << ip_string_by_ip[ip]
        << " map to the same address " << ip.ToBitset();
    ip_string_by_ip[ip] = ip_str;
  }
  ASSERT_EQ(ip_string_by_ip.size(),
            std::extent<decltype(kIpsAndIpStrings)>::value);
}

TEST(Ipv4AddressTest, DefaultConstructedIpIsAllZeros) {
  Ipv4Address ip;
  EXPECT_EQ(ip, Ipv4Address::AllZeros());
}

TEST(Ipv4AddressTest, AllZerosIsIndeedAllZeros) {
  Ipv4Address ip = Ipv4Address::AllZeros();
  EXPECT_TRUE(ip.IsAllZeros());
  EXPECT_EQ(ip, Ipv4Address(0, 0, 0, 0));
  EXPECT_EQ(ip.ToBitset(), std::bitset<32>(0u));
}

TEST(Ipv4AddressTest, AllOnesIsIndeedAllOnes) {
  Ipv4Address ip = Ipv4Address::AllOnes();
  EXPECT_TRUE(ip.IsAllOnes());
  EXPECT_EQ(ip, Ipv4Address(255, 255, 255, 255));
  EXPECT_EQ(ip.ToBitset(), std::bitset<32>(-1u));
}

TEST(Ipv4AddressTest, OfByteStringSuccess) {
  // Extra zeros are tolerated.
  std::vector<std::string> harmless_prefixes = {
      "", SafeString({0}), SafeString({0, 0}), SafeString({0, 0, 0})};
  for (auto& harmless_prefix : harmless_prefixes) {
    // Padded byte strings are okay.
    for (auto [ip, byte_str] : IpsAndPaddedByteStrings()) {
      byte_str = harmless_prefix + byte_str;
      EXPECT_THAT(Ipv4Address::OfByteString(byte_str), IsOkAndHolds(Eq(ip)))
          << "byte_str = " << absl::BytesToHexString(byte_str);
    }
    // P4Runtime byte strings are also okay.
    for (auto [ip, byte_str] : IpsAndP4RuntimeByteStrings()) {
      byte_str = harmless_prefix + byte_str;
      EXPECT_THAT(Ipv4Address::OfByteString(byte_str), IsOkAndHolds(Eq(ip)))
          << "byte_str = " << absl::BytesToHexString(byte_str);
    }
  }
}

TEST(Ipv4AddressTest, OfByteStringErrors) {
  // Extra non-zeros are illegal.
  std::vector<std::string> harmful_prefixes = {
      SafeString({1}), SafeString({100}), SafeString({0, 1}),
      SafeString({1, 0})};
  for (auto& harmful_prefix : harmful_prefixes) {
    for (auto [ip, byte_str] : IpsAndPaddedByteStrings()) {
      byte_str = harmful_prefix + byte_str;
      EXPECT_THAT(Ipv4Address::OfByteString(byte_str), Not(IsOk()))
          << "byte_str = " << absl::BytesToHexString(byte_str);
    }
  }
  // The empty string is illegal.
  EXPECT_THAT(Ipv4Address::OfByteString(""), Not(IsOk()));
}

TEST(Ipv4AddressTest, ToPaddedByteStringSuccess) {
  for (auto& [ip, byte_str] : IpsAndPaddedByteStrings()) {
    EXPECT_THAT(ip.ToPaddedByteString(), Eq(byte_str)) << "ip = " << ip;
  }
}

TEST(Ipv4AddressTest, ToP4RuntimeByteStringSuccess) {
  for (auto& [ip, byte_str] : IpsAndP4RuntimeByteStrings()) {
    EXPECT_THAT(ip.ToP4RuntimeByteString(), Eq(byte_str)) << "ip = " << ip;
  }
}

// Also tests `ToLpmPrefixLength` for all valid masks.
TEST(Ipv4AddressTest, MaskForPrefixLength_ValidLengths) {
  for (int length = 0; length <= 32; ++length) {
    // Construction of mask succeeds.
    ASSERT_OK_AND_ASSIGN(auto mask, Ipv4Address::MaskForPrefixLength(length));

    // Rountrip property.
    EXPECT_THAT(mask.ToLpmPrefixLength(), IsOkAndHolds(Eq(length)));

    // Characteristic properties of mask.
    for (int i = 0; i < 32 - length; ++i) {
      EXPECT_FALSE(mask.ToBitset()[i]) << " for i = " << i;
    }
    for (int i = 32 - length; i < 32; ++i) {
      EXPECT_TRUE(mask.ToBitset()[i]) << " for i = " << i;
    }
  }
}

TEST(Ipv4AddressTest, MaskForPrefixLength_InvalidLengths) {
  std::vector<int> bad_prefix_lengths = {-32, -2, -1, 33, 64, 1000};
  for (int prefix_length : bad_prefix_lengths) {
    EXPECT_THAT(Ipv4Address::MaskForPrefixLength(prefix_length), Not(IsOk()))
        << "for prefix_length = " << prefix_length;
  }
}

TEST(Ipv4AddressTest, ToLpmPrefixLength_InvalidMasks) {
  std::vector<Ipv4Address> bad_masks = {
      Ipv4Address::OfBitset(0b1111'0000'0000'0000'0000'0000'0000'0001),
      Ipv4Address::OfBitset(0b1111'0111'1111'1111'1111'1111'1111'1111),
      Ipv4Address::OfBitset(0b0111'1111'1111'1111'1111'1111'1111'1111),
      Ipv4Address::OfBitset(0b0000'1111'1111'1111'1111'1111'1111'1111),
  };
  for (const Ipv4Address& bad_mask : bad_masks) {
    EXPECT_THAT(bad_mask.ToLpmPrefixLength(), Not(IsOk()))
        << "for bad_mask = " << bad_mask;
  }
}

}  // namespace
}  // namespace netaddr
