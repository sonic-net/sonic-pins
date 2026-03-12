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

#ifndef PINS_P4_INFRA_NETADDR_IPV4_ADDRESS_H_
#define PINS_P4_INFRA_NETADDR_IPV4_ADDRESS_H_

#include <cstdint>
#include <string>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "p4_infra/netaddr/network_address.h"

namespace netaddr {

class Ipv4Address : public NetworkAddress<32, Ipv4Address> {
public:
  // The default constructor returns the address with all bits set to zero.
  constexpr Ipv4Address() = default;

  // Constructs address with the given bit representation.
  explicit constexpr Ipv4Address(std::bitset<32> bits)
      : NetworkAddress{std::move(bits)} {};

  // Ipv4Address(192, 168, 2, 1) constructs the IP address 192.168.2.1.
  explicit constexpr Ipv4Address(uint8_t byte4, uint8_t byte3, uint8_t byte2,
                                 uint8_t byte1)
      : NetworkAddress{(static_cast<uint32_t>(byte4) << 24) +
                       (static_cast<uint32_t>(byte3) << 16) +
                       (static_cast<uint32_t>(byte2) << 8) +
                       (static_cast<uint32_t>(byte1) << 0)} {};

  // Constructs an IPv4Address from an IP string in dot-decimal notation,
  // e.g. "192.168.2.1".
  static absl::StatusOr<Ipv4Address> OfString(absl::string_view address);

  // Returns IP address in dot-decimal notation, e.g. "192.168.2.1".
  std::string ToString() const;
};

} // namespace netaddr

#endif  // PINS_P4_INFRA_NETADDR_IPV4_ADDRESS_H_
