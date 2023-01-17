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
#include "lib/p4rt/p4rt_port.h"

#include <cstdint>

#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "gutil/status.h"
#include "p4_pdpi/string_encodings/decimal_string.h"

namespace pins_test {

absl::StatusOr<P4rtPortId> P4rtPortId::MakeFromP4rtEncoding(
    absl::string_view p4rt_port_id) {
  ASSIGN_OR_RETURN(uint32_t p4rt_port_id_int,
                   pdpi::DecimalStringToUint32(p4rt_port_id));
  return P4rtPortId(p4rt_port_id_int);
}

absl::StatusOr<std::vector<P4rtPortId>> P4rtPortId::MakeVectorFromP4rtEncodings(
    absl::Span<const std::string> p4rt_port_ids) {
  std::vector<P4rtPortId> result;
  for (absl::string_view p4rt_port_id_str : p4rt_port_ids) {
    ASSIGN_OR_RETURN(P4rtPortId port_id,
                     P4rtPortId::MakeFromP4rtEncoding(p4rt_port_id_str));
    result.push_back(port_id);
  }
  return result;
}

P4rtPortId P4rtPortId::MakeFromOpenConfigEncoding(uint32_t p4rt_port_id) {
  return P4rtPortId(p4rt_port_id);
}
std::vector<P4rtPortId> P4rtPortId::MakeVectorFromOpenConfigEncodings(
    absl::Span<const uint32_t> p4rt_port_ids) {
  std::vector<P4rtPortId> result;
  for (uint32_t p4rt_port_id : p4rt_port_ids) {
    result.push_back(P4rtPortId::MakeFromOpenConfigEncoding(p4rt_port_id));
  }
  return result;
}

uint32_t P4rtPortId::GetOpenConfigEncoding() const { return p4rt_port_id_; }

std::string P4rtPortId::GetP4rtEncoding() const {
  return absl::StrCat(p4rt_port_id_);
}

bool P4rtPortId::operator==(const P4rtPortId& other) const {
  return p4rt_port_id_ == other.p4rt_port_id_;
}

bool P4rtPortId::operator<(const P4rtPortId& other) const {
  return p4rt_port_id_ < other.p4rt_port_id_;
}

std::ostream& operator<<(std::ostream& os, const P4rtPortId& p4rt_port_id) {
  return os << absl::StrCat("(p4rt_port_id: ", p4rt_port_id.GetP4rtEncoding(),
                            ")");
}

}  // namespace pins_test
