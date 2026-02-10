// Copyright 2020 Google LLC
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
#ifndef PINS_P4RT_APP_UTILS_STATUS_UTILITY_H_
#define PINS_P4RT_APP_UTILS_STATUS_UTILITY_H_

#include "absl/status/status.h"
#include "absl/strings/cord.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "p4_infra/p4_pdpi/ir.pb.h"

namespace p4rt_app {
// Status payload url for tracking the library stack.
static constexpr absl::string_view kLibraryUrl = "p4rt_app_sublibrary";

inline std::string LibraryPrefix(const absl::Status &status) {
  auto payload = status.GetPayload(kLibraryUrl);
  if (payload.has_value()) {
    return absl::StrCat("[P4RT/", payload->Flatten(), "] ");
  }
  return "[P4RT] ";
}

// Translates absl::Status to pdpi::IrUpdateStatus
pdpi::IrUpdateStatus GetIrUpdateStatus(absl::StatusCode code,
                                       const std::string &message);
pdpi::IrUpdateStatus GetIrUpdateStatus(const absl::Status &status);

} // namespace p4rt_app

#endif // PINS_P4RT_APP_UTILS_STATUS_UTILITY_H_
