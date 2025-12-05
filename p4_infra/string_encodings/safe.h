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

#ifndef PINS_INFRA_P4_INFRA_STRING_ENCODINGS_SAFE_H_
#define PINS_INFRA_P4_INFRA_STRING_ENCODINGS_SAFE_H_

#include <cstdint>
#include <cstring>
#include <string>
#include <vector>

namespace string_encodings {

// Safely constructs `char` from integer. Example: `SafeChar(0xFF)`.
//
// In C(++), it is implementation dependent whether char is signed or unsigned.
// This can lead to surprises/undefined behavior when relying on implicit
// conversions from integers types to char. This function avoids such surprises.
char SafeChar(uint8_t byte);

// Safely constructs a string from a vector of bytes specified as integers.
// For example: `SafeString({0xFF, 0x10})`.
std::string SafeString(std::vector<uint8_t> bytes);

}  // namespace string_encodings

#endif  // PINS_INFRA_P4_INFRA_STRING_ENCODINGS_SAFE_H_
