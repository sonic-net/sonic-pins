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
#include "p4_pdpi/netaddr/ipv6_address.h"

#include <arpa/inet.h>
#include <resolv.h>
#include <sys/socket.h>

#include <bitset>
#include <cstdint>
#include <string>
#include <utility>

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "gutil/status.h"
#include "p4_pdpi/netaddr/network_address.h"
#include "p4_pdpi/string_encodings/hex_string.h"

namespace netaddr {

absl::StatusOr<Ipv6Address> Ipv6Address::OfString(absl::string_view address) {
  std::string bytes = std::string(128 / 8, '\x0');
  if (inet_pton(AF_INET6, address.data(), bytes.data()) == 1) {
    auto ip = Ipv6Address::OfByteString(bytes);
    if (ip.ok()) return ip;
    LOG(DFATAL) << "failed to parse IPv6 byte string produced by inet_pton: "
                << ip.status();
  }
  return gutil::InvalidArgumentErrorBuilder()
         << "invalid IPv6 address: '" << address << "'";
}

std::string Ipv6Address::ToString() const {
  char result[INET6_ADDRSTRLEN];
  std::string bytes = ToPaddedByteString();
  if (inet_ntop(AF_INET6, bytes.c_str(), result, sizeof(result)) != nullptr) {
    return std::string(std::move(result));
  }
  LOG(DFATAL) << "inet_ntop failed to convert IPv6 address " << ToHexString()
              << " to readable string";
  return "::";
}

Ipv6Address::Ipv6Address(uint16_t hextet8, uint16_t hextet7, uint16_t hextet6,
                         uint16_t hextet5, uint16_t hextet4, uint16_t hextet3,
                         uint16_t hextet2, uint16_t hextet1)
    : NetworkAddress{(std::bitset<128>(hextet8) << 112) |
                     (std::bitset<128>(hextet7) << 96) |
                     (std::bitset<128>(hextet6) << 80) |
                     (std::bitset<128>(hextet5) << 64) |
                     (std::bitset<128>(hextet4) << 48) |
                     (std::bitset<128>(hextet3) << 32) |
                     (std::bitset<128>(hextet2) << 16) |
                     (std::bitset<128>(hextet1) << 0)} {};

int Ipv6Address::MinimumMaskLength() const {
  for (int i = 0; i < 128; ++i) {
    if (bits_.test(i)) return 128 - i;
  }
  return 0;
}

}  // namespace netaddr
