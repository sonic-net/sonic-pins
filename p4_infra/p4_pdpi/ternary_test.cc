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

#include "p4_infra/p4_pdpi/ternary.h"

#include <bitset>
#include <optional>

#include "gtest/gtest.h"
#include "p4_infra/p4_pdpi/netaddr/ipv4_address.h"
#include "p4_infra/p4_pdpi/netaddr/ipv6_address.h"
#include "p4_infra/p4_pdpi/netaddr/mac_address.h"

namespace pdpi {
namespace {

//---- Bitset tests ------------------------------------------------------------

constexpr std::bitset<32> kBitset32(0x12345678);

TEST(BitsetTernaryTest, DefaultConstructorMakesWildcard) {
  Ternary<std::bitset<32>> ternary;
  EXPECT_EQ(ternary.mask, std::bitset<32>());
}

TEST(BitsetTernaryTest, UnaryConstructorMakesExactForNonOptional) {
  // Passing in just a bitset, creates an exact match.
  Ternary<std::bitset<32>> ternary(kBitset32);
  EXPECT_EQ(ternary.value, kBitset32);
  EXPECT_EQ(ternary.mask, AllOnes<32>());
}

TEST(BitsetTernaryTest, UnaryConstructorMakesExactForNonNullOptional) {
  // Passing in an optional bitset that is set, creates an exact match.
  std::optional<std::bitset<32>> mac_address = kBitset32;
  Ternary<std::bitset<32>> ternary(mac_address);
  EXPECT_EQ(ternary.value, kBitset32);
  EXPECT_EQ(ternary.mask, AllOnes<32>());
}

TEST(BitsetTernaryTest, UnaryConstructorMakesWildcardForNullopt) {
  // Passing in an optional bitset that is unset, creates a wildcard match.
  std::optional<std::bitset<32>> mac_address = std::nullopt;
  Ternary<std::bitset<32>> ternary(mac_address);
  EXPECT_EQ(ternary.mask, std::bitset<32>());
}

TEST(BitsetTernaryTest, BinaryConstructorSetsValueAndMask) {
  constexpr std::bitset<32> kSomeMask(0x87654321);
  Ternary<std::bitset<32>> ternary(kBitset32, kSomeMask);
  EXPECT_EQ(ternary.value, kBitset32);
  EXPECT_EQ(ternary.mask, kSomeMask);
}

//---- MAC address tests -------------------------------------------------------

constexpr netaddr::MacAddress kMacAddress(0x00, 0x01, 0x02, 0x03, 0x04, 0x05);

TEST(MacAddressTernaryTest, DefaultConstructorMakesWildcard) {
  Ternary<netaddr::MacAddress> ternary;
  EXPECT_EQ(ternary.mask, netaddr::MacAddress::AllZeros());
}

TEST(MacAddressTernaryTest, UnaryConstructorMakesExactForNonOptional) {
  // Passing in just a MAC address, creates an exact match.
  Ternary<netaddr::MacAddress> ternary(kMacAddress);
  EXPECT_EQ(ternary.value, kMacAddress);
  EXPECT_EQ(ternary.mask, netaddr::MacAddress::AllOnes());
}

TEST(MacAddressTernaryTest, UnaryConstructorMakesExactForNonNullOptional) {
  // Passing in an optional MAC address that is set, creates an exact match.
  std::optional<netaddr::MacAddress> mac_address = kMacAddress;
  Ternary<netaddr::MacAddress> ternary(mac_address);
  EXPECT_EQ(ternary.value, kMacAddress);
  EXPECT_EQ(ternary.mask, netaddr::MacAddress::AllOnes());
}

TEST(MacAddressTernaryTest, UnaryConstructorMakesWildcardForNullopt) {
  // Passing in an optional MAC address that is unset, creates a wildcard match.
  std::optional<netaddr::MacAddress> mac_address = std::nullopt;
  Ternary<netaddr::MacAddress> ternary(mac_address);
  EXPECT_EQ(ternary.mask, netaddr::MacAddress::AllZeros());
}

TEST(MacAddressTernaryTest, BinaryConstructorSetsValueAndMask) {
  constexpr netaddr::MacAddress kSomeMask(0x02, 0x03, 0x04, 0x05, 0x06, 0x07);
  Ternary<netaddr::MacAddress> ternary(kMacAddress, kSomeMask);
  EXPECT_EQ(ternary.value, kMacAddress);
  EXPECT_EQ(ternary.mask, kSomeMask);
}

//---- IPv4 address tests ------------------------------------------------------

constexpr netaddr::Ipv4Address kIpv4Address(192, 168, 2, 1);

TEST(Ipv4AddressTernaryTest, DefaultConstructorMakesWildcard) {
  Ternary<netaddr::Ipv4Address> ternary;
  EXPECT_EQ(ternary.mask, netaddr::Ipv4Address::AllZeros());
}

TEST(Ipv4AddressTernaryTest, UnaryConstructorMakesExactForNonOptional) {
  // Passing in just an IPv4 address, creates an exact match.
  Ternary<netaddr::Ipv4Address> ternary(kIpv4Address);
  EXPECT_EQ(ternary.value, kIpv4Address);
  EXPECT_EQ(ternary.mask, netaddr::Ipv4Address::AllOnes());
}

TEST(Ipv4AddressTernaryTest, UnaryConstructorMakesExactForNonNullOptional) {
  // Passing in an optional IPv4 address that is set, creates an exact match.
  std::optional<netaddr::Ipv4Address> mac_address = kIpv4Address;
  Ternary<netaddr::Ipv4Address> ternary(mac_address);
  EXPECT_EQ(ternary.value, kIpv4Address);
  EXPECT_EQ(ternary.mask, netaddr::Ipv4Address::AllOnes());
}

TEST(Ipv4AddressTernaryTest, UnaryConstructorMakesWildcardForNullopt) {
  // Passing in an optional IPv4 address that is unset, creates a wildcard
  // match.
  std::optional<netaddr::Ipv4Address> mac_address = std::nullopt;
  Ternary<netaddr::Ipv4Address> ternary(mac_address);
  EXPECT_EQ(ternary.mask, netaddr::Ipv4Address::AllZeros());
}

TEST(Ipv4AddressTernaryTest, BinaryConstructorSetsValueAndMask) {
  constexpr netaddr::Ipv4Address kSomeMask(10, 15, 20, 25);
  Ternary<netaddr::Ipv4Address> ternary(kIpv4Address, kSomeMask);
  EXPECT_EQ(ternary.value, kIpv4Address);
  EXPECT_EQ(ternary.mask, kSomeMask);
}

//---- IPv6 address tests ------------------------------------------------------

const netaddr::Ipv6Address kIpv6Address(0xffff, 0x1);

TEST(Ipv6AddressTernaryTest, DefaultConstructorMakesWildcard) {
  Ternary<netaddr::Ipv6Address> ternary;
  EXPECT_EQ(ternary.mask, netaddr::Ipv6Address::AllZeros());
}

TEST(Ipv6AddressTernaryTest, UnaryConstructorMakesExactForNonOptional) {
  // Passing in just an IPv6 address, creates an Exact match.
  Ternary<netaddr::Ipv6Address> ternary(kIpv6Address);
  EXPECT_EQ(ternary.value, kIpv6Address);
  EXPECT_EQ(ternary.mask, netaddr::Ipv6Address::AllOnes());
}

TEST(Ipv6AddressTernaryTest, UnaryConstructorMakesExactForNonNullOptional) {
  // Passing in an optional IPv6 address that is set, creates an Exact match.
  std::optional<netaddr::Ipv6Address> mac_address = kIpv6Address;
  Ternary<netaddr::Ipv6Address> ternary(mac_address);
  EXPECT_EQ(ternary.value, kIpv6Address);
  EXPECT_EQ(ternary.mask, netaddr::Ipv6Address::AllOnes());
}

TEST(Ipv6AddressTernaryTest, UnaryConstructorMakesWildcardForNullopt) {
  // Passing in an optional IPv6 address that is unset, creates a wildcard
  // match.
  std::optional<netaddr::Ipv6Address> mac_address = std::nullopt;
  Ternary<netaddr::Ipv6Address> ternary(mac_address);
  EXPECT_EQ(ternary.mask, netaddr::Ipv6Address::AllZeros());
}

TEST(Ipv6AddressTernaryTest, BinaryConstructorSetsValueAndMask) {
  const netaddr::Ipv6Address kSomeMask(0xff00, 0x0121);
  Ternary<netaddr::Ipv6Address> ternary(kIpv6Address, kSomeMask);
  EXPECT_EQ(ternary.value, kIpv6Address);
  EXPECT_EQ(ternary.mask, kSomeMask);
}

}  // namespace
}  // namespace pdpi
