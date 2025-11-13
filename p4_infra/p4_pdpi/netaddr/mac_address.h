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

#ifndef PINS_P4_INFRA_P4_PDPI_NETADDR_MAC_ADDRESS_H_
#define PINS_P4_INFRA_P4_PDPI_NETADDR_MAC_ADDRESS_H_

#include <cstdint>
#include <string>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "p4_infra/p4_pdpi/netaddr/ipv6_address.h"
#include "p4_infra/p4_pdpi/netaddr/network_address.h"

namespace netaddr {

class MacAddress : public NetworkAddress<48, MacAddress> {
 public:
  // The default constructor returns the address with all bits set to zero.
  constexpr MacAddress() = default;

  // Constructs address with the given bit representation.
  explicit constexpr MacAddress(std::bitset<48> bits)
      : NetworkAddress{std::move(bits)} {};

  // MacAddress(0x01, 0x23, 0x45, 0x67, 0x89, 0xab) constructs the MAC address
  // 01:23:45:67:89:ab.
  explicit constexpr MacAddress(uint8_t byte6, uint8_t byte5, uint8_t byte4,
                                uint8_t byte3, uint8_t byte2, uint8_t byte1)
      : NetworkAddress{(static_cast<uint64_t>(byte6) << 40) +
                       (static_cast<uint64_t>(byte5) << 32) +
                       (static_cast<uint64_t>(byte4) << 24) +
                       (static_cast<uint64_t>(byte3) << 16) +
                       (static_cast<uint64_t>(byte2) << 8) +
                       (static_cast<uint64_t>(byte1) << 0)} {};

  // Constructs an MAC address from a string,
  // e.g. "01:23:45:67:89:ab".
  static absl::StatusOr<MacAddress> OfString(absl::string_view address);

  // Returns MAC address in dot-hexadecimal notation, e.g. "01:23:45:67:89:ab".
  std::string ToString() const;

  // If the given IPv6 address is a link-local address derived from a MAC
  // address following RFC 4862, Section 5.3, returns the MAC address.
  // Otherwise, returns an invalid argument error status.
  static absl::StatusOr<MacAddress> OfLinkLocalIpv6Address(
      const Ipv6Address& ipv6);

  // Returns link-local IPv6 address for this MAC address, following
  // RFC 4862, Section 5.3, and RFC4291, Section 2.5.1 & Appendix A.
  Ipv6Address ToLinkLocalIpv6Address() const;

  // If the given interface identifier is derived from a MAC address following
  // RFC4291, Section 2.5.1 & Appendix A, returns the MAC address.
  // Otherwise, return an invalid argument error status.
  static absl::StatusOr<MacAddress> OfInterfaceId(
      const std::bitset<64>& interface_id);

  // Returns 64-bit interface identifier for this MAC address,
  // following RFC4291, Section 2.5.1 & Appendix A.
  std::bitset<64> ToInterfaceId() const;
};

}  // namespace netaddr

#endif  // PINS_P4_INFRA_P4_PDPI_NETADDR_MAC_ADDRESS_H_
