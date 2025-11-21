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

#ifndef PINS_P4_PDPI_PACKETLIB_PDPI_OPTIONS_H_
#define PINS_P4_PDPI_PACKETLIB_PDPI_OPTIONS_H_

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

  // During validation no error will be thrown
  // for nodes which have a @format annotation that specifies an other format
  // (for example, IPv4 or MAC).
  bool allow_arbitrary_format = false;

  template <typename Sink>
  friend void AbslStringify(Sink &sink, TranslationOptions options) {
    absl::Format(
        &sink,
        "pdpi::TranslationOptions{.key_only = %v, .allow_unsupported = %v}",
        options.key_only, options.allow_unsupported);
  }
};

// PDPI functions taking in `TranslationOptions` may wish to make that parameter
// optional for the convenience of external customers. At the same time, relying
// on that default inside the implementation of PDPI itself is extremely likely
// to be a bug where we forgot to pass on the options argument explicitly.
//
// To catch such bugs at compile time while still affording external users the
// convenience of a default argument, PDPI follows two conventions:
//
// 1. All PDPI `cc_library` targets that should not rely on the default
//    parameters specify the following attribute in their BUILD rule:
//    ```
//    local_defines = ["PDPI_DISABLE_TRANSLATION_OPTIONS_DEFAULT"],
//    ```
// 2. All functions taking `TranslationOptions` as an optional parameter are
//    declared as follows:
//    ```
//    T MyFunction(
//        ...,
//        TranslationOptions options PDPI_TRANSLATION_OPTIONS_DEFAULT);
//    ```
// ```
//
// Given the preprocessor directives below, this will disable the default
// argument internally but enable it externally.
#ifdef PDPI_DISABLE_TRANSLATION_OPTIONS_DEFAULT
#define PDPI_TRANSLATION_OPTIONS_DEFAULT
#else
#define PDPI_TRANSLATION_OPTIONS_DEFAULT = {}
#endif

} // namespace pdpi

#endif // PINS_P4_PDPI_PACKETLIB_PDPI_OPTIONS_H_
