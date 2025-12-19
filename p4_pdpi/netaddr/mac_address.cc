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
#include "p4_pdpi/netaddr/mac_address.h"

#include <bitset>
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/ascii.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "gutil/status.h"
#include "p4_pdpi/netaddr/ipv6_address.h"
#include "p4_pdpi/netaddr/network_address.h"

namespace netaddr {

namespace {

bool ParseByteInBase16(absl::string_view base16_string, uint8_t& byte) {
  if (base16_string.empty() || base16_string.size() > 2) return false;
  int buffer = 0;
  for (char c : base16_string) {
    if (!absl::ascii_isxdigit(c)) return false;
    int value =
        (c >= 'A') ? (c >= 'a') ? (c - 'a' + 10) : (c - 'A' + 10) : (c - '0');
    buffer = buffer * 16 + value;
  }
  memcpy(&byte, &buffer, 1);
  return true;
}

}  // namespace

absl::StatusOr<MacAddress> MacAddress::OfString(absl::string_view address) {
  auto invalid = [=]() {
    return gutil::InvalidArgumentErrorBuilder()
           << "Invalid MAC address: '" << address << "'";
  };

  std::vector<std::string> bytes = absl::StrSplit(address, ':');
  if (bytes.size() != 6) return invalid();

  std::bitset<48> bits;
  for (absl::string_view byte_string : bytes) {
    uint8_t byte;
    if (!ParseByteInBase16(byte_string, byte)) return invalid();
    bits <<= 8;
    bits |= byte;
  }
  return MacAddress(bits);
}

std::string MacAddress::ToString() const {
  uint8_t byte6 = (bits_ >> 40).to_ulong() & 0xFFu;
  uint8_t byte5 = (bits_ >> 32).to_ulong() & 0xFFu;
  uint8_t byte4 = (bits_ >> 24).to_ulong() & 0xFFu;
  uint8_t byte3 = (bits_ >> 16).to_ulong() & 0xFFu;
  uint8_t byte2 = (bits_ >> 8).to_ulong() & 0xFFu;
  uint8_t byte1 = (bits_ >> 0).to_ulong() & 0xFFu;
  return absl::StrFormat("%02x:%02x:%02x:%02x:%02x:%02x", byte6, byte5, byte4,
                         byte3, byte2, byte1);
}

absl::StatusOr<MacAddress> MacAddress::OfLinkLocalIpv6Address(
    const Ipv6Address& ipv6) {
  std::bitset<128> bits = ipv6.ToBitset();
  uint64_t upper = (bits >> 64).to_ullong();
  uint64_t lower =
      (bits & std::bitset<128>(0xFFFF'FFFF'FFFF'FFFFu)).to_ullong();
  if (upper != 0xFE80'0000'0000'0000u) {
    return gutil::InvalidArgumentErrorBuilder()
           << "invalid link-local IPv6 address " << ipv6
           << ": the upper 64 bits must be fe80::/64";
  }
  ASSIGN_OR_RETURN(auto mac, MacAddress::OfInterfaceId(lower),
                   _.SetPrepend()
                       << "in lower 64 bits of link-local IPv6 address '"
                       << ipv6 << "': ");
  return mac;
}

absl::StatusOr<MacAddress> MacAddress::OfInterfaceId(
    const std::bitset<64>& interface_id) {
  uint64_t id = interface_id.to_ullong();
  if ((id & 0x0000'00FF'FF00'0000) != 0x0000'00FF'FE00'0000) {
    return gutil::InvalidArgumentErrorBuilder()
           << "invalid interface ID " << pdpi::BitsetToHexString(interface_id)
           << ": the two middle bytes must be equal to FF FE.";
  }
  std::bitset<48> mac = ((id & 0xFFFF'FF00'0000'0000u) >> 16) |
                        ((id & 0x0000'0000'00FF'FFFF) >> 0);
  // Invert 'u' bit of MAC address (7-th most significant bit).
  mac ^= 0x02'00'00'00'00'00;
  return MacAddress(std::move(mac));
}

Ipv6Address MacAddress::ToLinkLocalIpv6Address() const {
  std::bitset<64> interface_id = ToInterfaceId();
  auto padded_interface_id = std::bitset<128>(interface_id.to_ullong());
  auto link_local_prefix = std::bitset<128>(0xFE80) << 112;
  return Ipv6Address(link_local_prefix | padded_interface_id);
}

std::bitset<64> MacAddress::ToInterfaceId() const {
  std::bitset<64> result = 0x0000'00FF'FE00'0000;
  // Invert 'u' bit of MAC address (7-th most significant bit).
  uint64_t mac = bits_.to_ullong() ^ 0x02'00'00'00'00'00;
  result |= (mac & 0x00'00'00'FF'FF'FF) << 0;
  result |= (mac & 0xFF'FF'FF'00'00'00) << 16;
  return result;
}

}  // namespace netaddr
