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

#include "p4_infra/netaddr/ipv4_address.h"

#include <bitset>
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "gutil/gutil/status.h"
#include "p4_infra/netaddr/network_address.h"

namespace netaddr {

namespace {

bool ParseByteInBase10(absl::string_view base10_string, uint8_t& byte) {
  if (base10_string.empty() || base10_string.size() > 3) return false;
  int buffer = 0;
  for (char c : base10_string) {
    if (c > '9' || c < '0') return false;
    buffer = buffer * 10 + (c - '0');
  }
  if (buffer > 255) return false;  // Too large to fit into a byte.
  memcpy(&byte, &buffer, 1);
  return true;
}

}  // namespace

absl::StatusOr<Ipv4Address> Ipv4Address::OfString(absl::string_view address) {
  auto invalid = [=]() {
    return gutil::InvalidArgumentErrorBuilder()
           << "Invalid IPv4 address: '" << address << "'";
  };

  std::vector<std::string> bytes = absl::StrSplit(address, '.');
  if (bytes.size() != 4) return invalid();

  std::bitset<32> bits;
  for (absl::string_view byte_string : bytes) {
    uint8_t byte;
    if (!ParseByteInBase10(byte_string, byte)) return invalid();
    bits <<= 8;
    bits |= byte;
  }
  return Ipv4Address(bits);
}

std::string Ipv4Address::ToString() const {
  uint8_t byte4 = (bits_ >> 24).to_ulong() & 0xFFu;
  uint8_t byte3 = (bits_ >> 16).to_ulong() & 0xFFu;
  uint8_t byte2 = (bits_ >> 8).to_ulong() & 0xFFu;
  uint8_t byte1 = (bits_ >> 0).to_ulong() & 0xFFu;
  return absl::StrFormat("%d.%d.%d.%d", byte4, byte3, byte2, byte1);
}

}  // namespace netaddr
