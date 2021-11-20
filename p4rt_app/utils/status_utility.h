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
#ifndef GOOGLE_P4RT_APP_UTILS_STATUS_UTILITY_H_
#define GOOGLE_P4RT_APP_UTILS_STATUS_UTILITY_H_

#include "absl/status/status.h"
#include "p4_pdpi/ir.pb.h"

namespace p4rt_app {

// Translates absl::Status to pdpi::IrUpdateStatus
pdpi::IrUpdateStatus GetIrUpdateStatus(absl::StatusCode code,
                                       const std::string& message);
pdpi::IrUpdateStatus GetIrUpdateStatus(const absl::Status& status);

}  // namespace p4rt_app

#endif  // GOOGLE_P4RT_APP_UTILS_STATUS_UTILITY_H_
