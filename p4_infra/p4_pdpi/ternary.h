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

// This file declares structs for encoding ternary matches.

#ifndef PINS_P4_INFRA_P4_PDPI_TERNARY_H_
#define PINS_P4_INFRA_P4_PDPI_TERNARY_H_

#include <stddef.h>

#include <bitset>
#include <cstddef>
#include <optional>
#include <ostream>

#include "p4_infra/p4_pdpi/netaddr/ipv4_address.h"
#include "p4_infra/p4_pdpi/netaddr/ipv6_address.h"
#include "p4_infra/p4_pdpi/netaddr/mac_address.h"

namespace pdpi {

// A `Ternary<T>` encodes a ternary match on a value of type T. It makes sense
// only if Ts can be encoded using bitvectors.
template <typename T>
struct Ternary {
  // All masked off bits of `value` must be zero to ensure canonicity. Formally,
  // value must satisfy bits(value) & ~bits(mask) == 0 .
  // We don't enforce this restriction in general, but assume it throughout the
  // code base so that ternaries represent the same set iff they are equal.
  T value;
  T mask;
};

template <typename T>
std::ostream& operator<<(std::ostream& os, Ternary<T> ternary) {
  return os << "Ternary{.value = " << ternary.value
            << ", .mask = " << ternary.mask << "}";
}

// -- Template specializations providing more convenient constructors ----------

// Returns a bitset with all bits set to 1.
template <std::size_t N>
std::bitset<N> AllOnes() {
  std::bitset<N> all_zeros;
  all_zeros.flip();
  return all_zeros;
}

template <std::size_t N>
struct Ternary<std::bitset<N>> {
  std::bitset<N> value;
  std::bitset<N> mask;

  // Default constructor: wildcard match.
  Ternary() {}

  // Unary constructor: exact match.
  explicit Ternary(std::bitset<N> value) : value{value}, mask{AllOnes<N>()} {};

  // Constructs an exact match if the optional has a value or a wildcard match
  // otherwise.
  explicit Ternary(std::optional<std::bitset<N>> value) {
    *this = value.has_value() ? Ternary(*value) : Ternary();
  }

  // Binary constructor: arbitrary ternary match.
  Ternary(std::bitset<N> value, std::bitset<N> mask)
      : value{value}, mask{mask} {}

  bool IsWildcard() const { return !mask.any(); }
};

template <>
struct Ternary<netaddr::MacAddress> {
  netaddr::MacAddress value;
  netaddr::MacAddress mask;

  // Default constructor: wildcard match.
  Ternary() {}

  // Unary constructor: exact match.
  explicit Ternary(netaddr::MacAddress value)
      : value{value}, mask{netaddr::MacAddress::AllOnes()} {}

  // Constructs an exact match if the optional has a value or a wildcard match
  // otherwise.
  explicit Ternary(std::optional<netaddr::MacAddress> value) {
    *this = value.has_value() ? Ternary(*value) : Ternary();
  }

  // Binary constructor: arbitrary ternary match.
  Ternary(netaddr::MacAddress value, netaddr::MacAddress mask)
      : value{value}, mask{mask} {}
};

template <>
struct Ternary<netaddr::Ipv4Address> {
  netaddr::Ipv4Address value;
  netaddr::Ipv4Address mask;

  // Default constructor: wildcard match.
  Ternary() {}

  // Unary constructor: exact match.
  explicit Ternary(netaddr::Ipv4Address value)
      : value{value}, mask{netaddr::Ipv4Address::AllOnes()} {}

  // Constructs an exact match if the optional has a value or a wildcard match
  // otherwise.
  explicit Ternary(std::optional<netaddr::Ipv4Address> value) {
    *this = value.has_value() ? Ternary(*value) : Ternary();
  }

  // Binary constructor: arbitrary ternary match.
  Ternary(netaddr::Ipv4Address value, netaddr::Ipv4Address mask)
      : value{value}, mask{mask} {}
};

template <>
struct Ternary<netaddr::Ipv6Address> {
  netaddr::Ipv6Address value;
  netaddr::Ipv6Address mask;

  // Default constructor: wildcard match.
  Ternary() {}

  // Unary constructor: exact match.
  explicit Ternary(netaddr::Ipv6Address value)
      : value{value}, mask{netaddr::Ipv6Address::AllOnes()} {}

  // Constructs an exact match if the optional has a value or a wildcard match
  // otherwise.
  explicit Ternary(std::optional<netaddr::Ipv6Address> value) {
    *this = value.has_value() ? Ternary(*value) : Ternary();
  }

  // Binary constructor: arbitrary ternary match.
  Ternary(netaddr::Ipv6Address value, netaddr::Ipv6Address mask)
      : value{value}, mask{mask} {}
};

// -- Deduction guides ---------------------------------------------------------

template <typename T>
Ternary(std::optional<T>) -> Ternary<T>;

template <typename T>
Ternary(T) -> Ternary<T>;

template <typename T, typename U>
Ternary(T, U) -> Ternary<T>;

}  // namespace pdpi

#endif  // PINS_P4_INFRA_P4_PDPI_TERNARY_H_
