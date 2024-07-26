/*
 * Copyright 2024 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#ifndef PINS_LIB_P4RT_P4RT_PORT_H_
#define PINS_LIB_P4RT_P4RT_PORT_H_

#include <cstdint>
#include <string>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/types/span.h"

namespace pins_test {

// Class representing a P4Runtime port ID.
//
// For historical reasons, there exists two encodings of P4Runtime port IDs:
// - As an integer (uint32_t) `42`, e.g. in OpenConfig.
// - As a decimal string `"42"`, e.g. in P4Runtime messages such as table
// entries.
//
// This class represents a P4Runtime port ID, abstracting away the encoding.
// TODO: Agree on a single encoding so this class becomes obsolete.
class P4rtPortId {
 public:
  // Constructors.
  P4rtPortId() = default;

  // Expects a decimal string. Else returns InvalidArgumentError.
  static absl::StatusOr<P4rtPortId> MakeFromP4rtEncoding(
      absl::string_view p4rt_port_id);
  static absl::StatusOr<std::vector<P4rtPortId>> MakeVectorFromP4rtEncodings(
      absl::Span<const std::string> p4rt_port_id);

  // Constructs a P4rtPortId from an OpenConfig encoding, i.e. a uint32. Never
  // fails.
  static P4rtPortId MakeFromOpenConfigEncoding(uint32_t p4rt_port_id);
  static std::vector<P4rtPortId> MakeVectorFromOpenConfigEncodings(
      absl::Span<const uint32_t> p4rt_port_id);

  // Getters.
  // Returns OpenConfig encoding of the port ID, e.g. the uint32 `42`.
  uint32_t GetOpenConfigEncoding() const;

  // Returns P4Runtime encoding of the port ID, e.g. the string `"42"`.
  std::string GetP4rtEncoding() const;

  bool operator==(const P4rtPortId& other) const;
  bool operator<(const P4rtPortId& other) const;

  template <typename H>
  friend H AbslHashValue(H h, const P4rtPortId& port_id) {
    return H::combine(std::move(h), port_id.p4rt_port_id_);
  }

 private:
  explicit P4rtPortId(uint32_t p4rt_port_id) : p4rt_port_id_(p4rt_port_id) {}
  uint32_t p4rt_port_id_ = 0;
};

// TODO: Remove and update the class to use AbslStringify.
std::ostream& operator<<(std::ostream& os, const P4rtPortId& p4rt_port_id);

}  // namespace pins_test

#endif  // PINS_LIB_P4RT_P4RT_PORT_H_
