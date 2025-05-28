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

#ifndef PINS_P4_INFRA_STRING_ENCODINGS_BIT_STRING_H_
#define PINS_P4_INFRA_STRING_ENCODINGS_BIT_STRING_H_

#include <bitset>
#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "p4_infra/netaddr/ipv4_address.h"
#include "p4_infra/netaddr/ipv6_address.h"
#include "p4_infra/netaddr/mac_address.h"
#include "p4_infra/string_encodings/hex_string.h"

namespace string_encodings {

// Represents a bitstring of arbitrary size that grows as necessary. Useful when
// working with byte strings, but also needing the ability to operate on a
// bit-level.
// Provides both methods for constructing bit strings (from scratch or
// incrementally), as well as methods for consuming bits and outputting them in
// various formats.
class BitString {
public:
  // Constructs a bit string from a byte string.
  static BitString OfByteString(absl::string_view data) {
    BitString result;
    for (uint8_t character : data) {
      result.AppendBits(std::bitset<8>(character));
    }
    return result;
  }

  void AppendBit(bool bit) { bits_.push_back(bit); }
  template <size_t num_bits>
  void AppendBits(const std::bitset<num_bits> &bits) {
    for (int i = 0; i < num_bits; i++) {
      bits_.push_back(bits.test(num_bits - 1 - i));
    }
  }

  void AppendBytes(absl::string_view bytes) {
    for (int i = 0; i < bytes.size(); i++) {
      AppendBits(std::bitset<8>(bytes[i]));
    }
  }

  absl::Status AppendHexString(absl::string_view hex_string) {
    ASSIGN_OR_RETURN(auto bytes,
                     string_encodings::HexStringToByteString(hex_string));
    AppendBytes(bytes);
    return absl::OkStatus();
  }

  // Peaks at the given number of bits from the front of the bit string, and
  // returns them as a hex string. Returns an error if there are not enough bits
  // left.
  absl::StatusOr<std::string> PeekHexString(int num_bits);
  // Consumes the given number of bits from the front of the bit string, and
  // returns them as a hex string. Returns an error if there are not enough bits
  // left.
  absl::StatusOr<std::string> ConsumeHexString(int num_bits);
  // Consumes the given number of bits from the front of the bit string, and
  // returns them as a MAC address. Returns an error if there are not enough
  // bits left.
  absl::StatusOr<netaddr::MacAddress> ConsumeMacAddress();
  // Consumes the given number of bits from the front of the bit string, and
  // returns them as a IP address. Returns an error if there are not enough bits
  // left.
  absl::StatusOr<netaddr::Ipv4Address> ConsumeIpv4Address();
  // Consumes the given number of bits from the front of the bit string, and
  // returns them as a IP address. Returns an error if there are not enough bits
  // left.
  absl::StatusOr<netaddr::Ipv6Address> ConsumeIpv6Address();

  // Consumes the given number of bits and returns them as a std::bitset.
  template <size_t num_bits>
  absl::StatusOr<std::bitset<num_bits>> ConsumeBitset() {
    const int start_index = start_index_;
    RETURN_IF_ERROR(Consume(num_bits));
    std::bitset<num_bits> result;
    for (int i = 0; i < num_bits; ++i) {
      result[num_bits - i - 1] = bits_[start_index + i];
    }
    return result;
  }

  // Returns the number of bits.
  int size() const { return bits_.size() - start_index_; }

  // Returns a byte string representation. Only works if size() % 8 == 0.
  absl::StatusOr<std::string> ToByteString() const;

  // Returns a hex string representation. Fails if there are no bits.
  absl::StatusOr<std::string> ToHexString() const;

private:
  // Consumes num_bits and returns ok if BitString is long enough, or an error
  // status otherwise.
  absl::Status Consume(int num_bits);

  // Translate the bits from start to start+num_bits to a hex string.
  std::string ToHexString(int start, int num_bits) const;

  // The bits that make up this bit string. Some prefix might be unused, and the
  // actual data only starts at start_index_.
  std::vector<bool> bits_;
  int start_index_ = 0;
};

}  // namespace string_encodings

#endif  // PINS_P4_INFRA_STRING_ENCODINGS_BIT_STRING_H_
