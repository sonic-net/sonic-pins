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

#include "p4_infra/string_encodings/bit_string.h"

#include <algorithm>

#include "absl/status/status.h"
#include "absl/strings/escaping.h"
#include "absl/strings/str_cat.h"
#include "gutil/gutil/status.h"
#include "p4_infra/netaddr/mac_address.h"

namespace string_encodings {

absl::Status BitString::Consume(int num_bits) {
  if (num_bits < 0) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Cannot consume " << num_bits << " bits.";
  }
  if (size() < num_bits) {
    return gutil::FailedPreconditionErrorBuilder()
           << "Only " << size() << " bits left, but attempted to consume "
           << num_bits << " bits.";
  }
  start_index_ += num_bits;
  return absl::OkStatus();
}

absl::StatusOr<std::string> BitString::PeekHexString(int num_bits) {
  if (num_bits < 0) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Cannot peek " << num_bits << " bits.";
  }
  if (size() < num_bits) {
    return gutil::FailedPreconditionErrorBuilder()
           << "Only " << size() << " bits left, but attempted to peek "
           << num_bits << " bits.";
  }
  return ToHexString(start_index_, num_bits);
}

absl::StatusOr<std::string> BitString::ConsumeHexString(int num_bits) {
  RETURN_IF_ERROR(Consume(num_bits));
  return ToHexString(start_index_ - num_bits, num_bits);
}

absl::StatusOr<netaddr::MacAddress> BitString::ConsumeMacAddress() {
  ASSIGN_OR_RETURN(auto hex_string, ConsumeHexString(48));
  return netaddr::MacAddress::OfHexString(hex_string);
}
absl::StatusOr<netaddr::Ipv4Address> BitString::ConsumeIpv4Address() {
  ASSIGN_OR_RETURN(auto hex_string, ConsumeHexString(32));
  return netaddr::Ipv4Address::OfHexString(hex_string);
}
absl::StatusOr<netaddr::Ipv6Address> BitString::ConsumeIpv6Address() {
  ASSIGN_OR_RETURN(auto hex_string, ConsumeHexString(128));
  return netaddr::Ipv6Address::OfHexString(hex_string);
}

absl::StatusOr<std::string> BitString::ToByteString() const {
  if (size() % 8 != 0)
    return gutil::FailedPreconditionErrorBuilder()
           << "Only bit strings with a size that a multiple of 8 can be "
              "converted to a byte string. Got "
           << size();

  std::string result;
  result.reserve(size() / 8);
  for (int byte = 0; byte < size() / 8; byte++) {
    uint8_t character = 0;
    for (int bit = 0; bit < 8; bit++) {
      character <<= 1;
      character |= bits_[start_index_ + byte * 8 + bit];
    }
    result += character;
  }
  return result;
}

absl::StatusOr<std::string> BitString::ToHexString() const {
  if (size() == 0) {
    return gutil::FailedPreconditionErrorBuilder()
           << "Cannot represent the empty bit string as a hex string";
  }
  return ToHexString(start_index_, size());
}

std::string BitString::ToHexString(int start, int num_bits) const {
  // Process, starting with the last byte.
  std::string result;
  for (int byte = 0; byte < (num_bits + 7) / 8; byte++) {
    uint8_t character = 0;
    // Note: first byte may only be partially filled
    int bit;
    for (bit = 0; bit < 8 && (byte * 8 + bit < num_bits); bit++) {
      character >>= 1;
      character |= bits_[start + num_bits - 1 - (byte * 8 + bit)] << 7;
    }
    // Finish shifting bits in the first byte
    for (int i = bit; i < 8; i++) {
      character >>= 1;
    }
    std::string hex = absl::BytesToHexString(std::string(1, character));
    if (bit <= 4) hex = hex.substr(1, 1);
    std::reverse(hex.begin(), hex.end());
    result += hex;
  }

  std::reverse(result.begin(), result.end());
  return absl::StrCat("0x", result);
}

}  // namespace string_encodings
