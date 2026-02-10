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
#ifndef PINS_P4_PDPI_PACKETLIB_READABLE_BIT_STRING_H_
#define PINS_P4_PDPI_PACKETLIB_READABLE_BIT_STRING_H_

#include "absl/status/statusor.h"

namespace pdpi {

// Library to write down byte strings in a readable manner. This is useful e.g.
// for writing down network packets in a readable manner.
//
// Example:
// R"PB(
//   # ethernet header
//   ethernet_source: 0x112233445566
//   ethernet_destination: 0xaabbccddeeff
//   ether_type: 0x0800
//   # IPv4 header:
//   version: 0x4
//   ihl: 0x5
//   dhcp: 0b011011)PB"
//   # Payload
//   payload: "This is an ASCII string."
//
// Supports comments (using #), annotations of what a group of bits represents
// (string before the colon), hex strings, base-2 strings, and ASCII strings.
absl::StatusOr<std::string>
ReadableByteStringToByteString(absl::string_view readable_byte_string);

} // namespace pdpi

#endif // PINS_P4_PDPI_PACKETLIB_READABLE_BIT_STRING_H_
