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

#include "p4_infra/string_encodings/byte_string.h"

#include <algorithm>
#include <string>

#include "absl/strings/string_view.h"

namespace string_encodings {

std::string ByteStringToP4runtimeByteString(std::string bytes) {
  // Remove leading zeros.
  bytes.erase(0, std::min(bytes.find_first_not_of('\x00'), bytes.size() - 1));
  return bytes;
}

int GetBitwidthOfByteString(absl::string_view byte_string) {
  for (int i = 0; i < byte_string.size(); ++i) {
    unsigned char c = static_cast<unsigned char>(byte_string[i]);
    if (c == 0) continue;
    int significant_bits = 0;
    do {
      significant_bits += 1;
      c >>= 1;
    } while (c != 0);
    return significant_bits + 8 * (byte_string.size() - i - 1);
  }
  return byte_string.empty() ? 0 : 1;
}

}  // namespace string_encodings
