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

#ifndef PINS_P4_INFRA_P4_PDPI_NETADDR_NETWORK_ADDRESS_H_
#define PINS_P4_INFRA_P4_PDPI_NETADDR_NETWORK_ADDRESS_H_

#include <bitset>
#include <cstddef>
#include <iosfwd>
#include <ostream>
#include <string>
#include <utility>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "gutil/gutil/status.h"
#include "p4_infra/string_encodings/byte_string.h"
#include "p4_infra/string_encodings/hex_string.h"

namespace netaddr {

// Base class for network addresses, e.g. IP and MAC addresses.
//
// Concrete network address classes must inherit from this base class using the
// "curiously recurring template pattern", must implement `OfString` and
// `ToString` functions, and must inherit the constructors:
// ```
//   class Ipv4Address : public NetworkAddress<32, Ipv4Address> {
//    public:
//     // The default constructor returns the address with all bits set to zero.
//     constexpr Ipv4Address() = default;
//     // Returns the address encoded by the given human readable string.
//     static absl::StatusOr<Ipv4Address> OfString(absl::string_view address);
//     // Returns address as a human readable string.
//     std::string ToString() const;
//
//    protected:
//      using NetworkAddress::NetworkAddress;
//   };
// ```
template <std::size_t num_bits, typename T>
class NetworkAddress {
 public:
  // -- Constructors --
  // Returns the address with all bits set to zero.
  static constexpr T AllZeros() { return T(std::bitset<num_bits>()); }
  // Returns the address with all bits set to one.
  static constexpr T AllOnes() { return T(~std::bitset<num_bits>()); }
  // Returns LPM mask for the given prefix length, or error if the prefix length
  // is not in the interval [0, num_bits].
  static absl::StatusOr<T> MaskForPrefixLength(int prefix_length);
  // Returns the address encoded by the given bitset.
  static constexpr T OfBitset(std::bitset<num_bits> bits) {
    return T(std::move(bits));
  }
  // Returns the address encoded by the given hex string.
  static absl::StatusOr<T> OfHexString(absl::string_view hex_str);
  // Returns the address encoded by the given big-endian, arbitrary-length,
  // nonempty byte string.
  // Missing bits are assumed to be zero.
  // Extra bits are checked to be zero, returning error status otherwise.
  static absl::StatusOr<T> OfByteString(absl::string_view byte_str);
  // Returns the address encoded by the given human readable string.
  // Note: Must be implemented by all subclasses.
  // (Not `virtual` because C++ does not have `static virtual`.)
  // static absl::StatusOr<T> OfString(absl::string_view address);

  // -- Checks --
  bool IsAllZeros() const { return bits_.none(); }
  bool IsAllOnes() const { return bits_.all(); }

  // -- Conversions --
  // Returns underlying bit representation.
  std::bitset<num_bits> ToBitset() const { return bits_; }
  // Returns hexadecimal representation of the address.
  std::string ToHexString() const {
    return string_encodings::BitsetToHexString(bits_);
  }
  // Returns big-endian byte string encoding of the address of length exactly
  // ceil(num_bits/8).
  std::string ToPaddedByteString() const;
  // Returns big-endian byte string encoding of the address in canonical
  // P4Runtime format (leading zeros omitted).
  std::string ToP4RuntimeByteString() const;
  // Returns address as a human readable string.
  // Note: Must be implemented by all subclasses.
  // (Not `virtual` only because that would prevent constexpr addresses.)
  // std::string ToString() const;

  // Returns prefix length if address is an LPM mask, i.e. is of the form
  // 1...10...0, or error otherwise.
  // More formally, returns `k` if `*this == *MaskForPrefixLength(k)` for some
  // `0 <= k <= num_bits`, or error status if no such `k` exists.
  absl::StatusOr<int> ToLpmPrefixLength() const;

  // -- Bit operations --
  void operator&=(const T& other) { bits_ &= other.bits_; }
  void operator|=(const T& other) { bits_ |= other.bits_; }
  void operator^=(const T& other) { bits_ ^= other.bits_; }
  void operator<<=(std::size_t pos) { bits_ <<= pos; }
  void operator>>=(std::size_t pos) { bits_ >>= pos; }
  T operator&(const T& other) { return T(bits_ & other.bits_); }
  T operator|(const T& other) { return T(bits_ | other.bits_); }
  T operator^(const T& other) { return T(bits_ ^ other.bits_); }
  T operator<<(std::size_t pos) { return T(bits_ << pos); }
  T operator>>(std::size_t pos) { return T(bits_ >> pos); }
  T operator~() const { return T(~bits_); }

  // -- Comparisons --
  bool operator==(const T& other) const { return bits_ == other.bits_; }
  bool operator!=(const T& other) const { return bits_ != other.bits_; }
  bool operator<(const T& other) const {
    return ToPaddedByteString() < other.ToPaddedByteString();
  }
  bool operator<=(const T& other) const {
    return ToPaddedByteString() <= other.ToPaddedByteString();
  }
  bool operator>(const T& other) const {
    return ToPaddedByteString() > other.ToPaddedByteString();
  }
  bool operator>=(const T& other) const {
    return ToPaddedByteString() >= other.ToPaddedByteString();
  }

  // Hashing (https://abseil.io/docs/cpp/guides/hash).
  template <typename H>
  friend H AbslHashValue(H h, const T& address) {
    return H::combine(std::move(h), address.bits_);
  }

 protected:
  std::bitset<num_bits> bits_;

  // -- Note --
  // Constructors must be inherited by all subclasses. They are protected so the
  // NetworkAddress class is never instantiated directly.

  // The default constructor returns the address with all bits set to zero.
  constexpr NetworkAddress() = default;
  explicit constexpr NetworkAddress(std::bitset<num_bits> bits)
      : bits_{std::move(bits)} {};
};

// Pretty printing.
template <std::size_t num_bits, typename T>
std::ostream& operator<<(std::ostream& os,
                         const NetworkAddress<num_bits, T>& address) {
  // As per the contract of the NetworkAddress class, any NetworkAddress<N,T>
  // object is castable to T and T has a ToString function.
  return os << static_cast<const T&>(address).ToString();
}

// == END OF PUBLIC INTERFACE ==================================================

template <std::size_t N, typename T>
absl::StatusOr<T> NetworkAddress<N, T>::MaskForPrefixLength(int prefix_length) {
  if (prefix_length < 0 || prefix_length > N) {
    return gutil::InvalidArgumentErrorBuilder()
           << "invalid prefix length " << prefix_length << " for address of "
           << N << " bits; must be in [0, " << N << "]";
  }
  return AllOnes() << (N - prefix_length);
}

template <std::size_t N, typename T>
absl::StatusOr<T> NetworkAddress<N, T>::OfHexString(absl::string_view hex_str) {
  ASSIGN_OR_RETURN(auto bits, string_encodings::HexStringToBitset<N>(hex_str));
  return T(std::move(bits));
}

template <std::size_t N, typename T>
absl::StatusOr<T> NetworkAddress<N, T>::OfByteString(
    absl::string_view byte_str) {
  ASSIGN_OR_RETURN(auto bits,
                   string_encodings::ByteStringToBitset<N>(byte_str));
  return T(bits);
}

template <std::size_t N, typename T>
std::string NetworkAddress<N, T>::ToPaddedByteString() const {
  return string_encodings::BitsetToPaddedByteString(bits_);
}

template <std::size_t N, typename T>
std::string NetworkAddress<N, T>::ToP4RuntimeByteString() const {
  return string_encodings::BitsetToP4RuntimeByteString(bits_);
}

template <std::size_t N, typename T>
absl::StatusOr<int> NetworkAddress<N, T>::ToLpmPrefixLength() const {
  for (int i = 0; i <= N; ++i) {
    if (*this == AllOnes() << (N - i)) return i;
  }
  return gutil::InvalidArgumentErrorBuilder() << "not an LPM mask: " << *this;
}

}  // namespace netaddr

#endif  // PINS_P4_INFRA_P4_PDPI_NETADDR_NETWORK_ADDRESS_H_
