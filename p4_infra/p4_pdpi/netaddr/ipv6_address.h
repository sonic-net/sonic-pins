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
#ifndef PINS_P4_PDPI_NETADDR_IPV6_ADDRESS_H_
#define PINS_P4_PDPI_NETADDR_IPV6_ADDRESS_H_

#include <cstdint>
#include <string>

#include "absl/numeric/int128.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "p4_infra/p4_pdpi/netaddr/network_address.h"

namespace netaddr {

class Ipv6Address : public NetworkAddress<128, Ipv6Address> {
public:
  // The default constructor returns the address with all bits set to zero.
  constexpr Ipv6Address() = default;

  // Constructs address with the given bit representation.
  explicit constexpr Ipv6Address(std::bitset<128> bits)
      : NetworkAddress{std::move(bits)} {};

  // Ipv6Address(0xffff, 0x1) constructs the IP address ffff:1::.
  explicit Ipv6Address(uint16_t hextet8, uint16_t hextet7 = 0,
                       uint16_t hextet6 = 0, uint16_t hextet5 = 0,
                       uint16_t hextet4 = 0, uint16_t hextet3 = 0,
                       uint16_t hextet2 = 0, uint16_t hextet1 = 0);

  // Constructs an Ipv6Address from uint128.
  explicit Ipv6Address(absl::uint128 ipv6_128)
      : Ipv6Address(std::bitset<128>(absl::Uint128High64(ipv6_128)) << 64 |
                    std::bitset<128>(absl::Uint128Low64(ipv6_128))) {}

  // Constructs an IPv6Address from an string in IPv6 address notation,
  // e.g. "2001:0db8:85a3::7334".
  static absl::StatusOr<Ipv6Address> OfString(absl::string_view address);

  // Returns address in IPv6 address notation, e.g. "2001:0db8:85a3::7334".
  std::string ToString() const;

  // Returns the IP address corresponding to an upper-64-bit IPv6 mask.
  // (ffff:ffff:ffff:ffff::)
  static Ipv6Address Upper64BitMask() { return Ipv6Address::AllOnes() << 64; }

  // Returns true if the IPv6 address only uses the upper 64-bits.
  bool IsUpper64BitAddress() const { return (bits_ << 64).none(); }

  // Returns the minimum mask length of the IPv6 address.
  // The mask length is the number of bits required to capture all non-zero bits
  // starting from the most-significant-bit in the IPv6 address (left-to-right
  // in the string format).
  int MinimumMaskLength() const;
};

} // namespace netaddr

#endif // PINS_P4_PDPI_NETADDR_IPV6_ADDRESS_H_
