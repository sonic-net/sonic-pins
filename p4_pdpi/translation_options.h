// Copyright 2024 Google LLC
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
#ifndef PINS_INFRA_P4_PDPI_PACKETLIB_PDPI_OPTIONS_H_
#define PINS_INFRA_P4_PDPI_PACKETLIB_PDPI_OPTIONS_H_

#include "absl/strings/str_format.h"

namespace pdpi {

// Common options shared by various PDPI translation functions.
struct TranslationOptions {
  // Translate only the key of a given table entry. Ignore non-key fields.
  // Useful for P4Runtime `DELETE` operations, which only require a key.
  bool key_only = false;

  // Allow translation of tables, match fields, and actions with an
  // `@unsupported` annotation. Useful during early-stage testing.
  bool allow_unsupported = false;

  template <typename Sink>
  friend void AbslStringify(Sink& sink, TranslationOptions options) {
    absl::Format(
        &sink,
        "pdpi::TranslationOptions{.key_only = %v, .allow_unsupported = %v}",
        options.key_only, options.allow_unsupported);
  }
};

}  // namespace pdpi

#endif  // PINS_INFRA_P4_PDPI_PACKETLIB_PDPI_OPTIONS_H_
