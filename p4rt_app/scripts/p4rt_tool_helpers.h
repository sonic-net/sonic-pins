// Copyright 2022 Google LLC
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
#ifndef GOOGLE_P4RT_APP_SCRIPTS_P4RT_TOOL_HELPERS_H_
#define GOOGLE_P4RT_APP_SCRIPTS_P4RT_TOOL_HELPERS_H_

#include <memory>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "gflags/gflags.h"
#include "p4_pdpi/p4_runtime_session.h"

// Flags to configure the P4RT connection.
DECLARE_string(p4rt_server_address);
DECLARE_uint64(p4rt_device_id);
DECLARE_bool(use_insecure_credentials);

namespace p4rt_app {

// P4RT tools are expected to be run from the commandline. These helper methods
// provide a uniform mechanism to report various information back to the user.
// They will print to either stdout or stderr, and can use different colors in
// the terminal.
void Info(absl::string_view message);     // default color to stdout
void Warning(absl::string_view message);  // yellow color to stderr
void Error(absl::string_view message);    // red color to stderr

absl::StatusOr<std::unique_ptr<pdpi::P4RuntimeSession>> CreateP4rtSession();

}  // namespace p4rt_app

#endif  // GOOGLE_P4RT_APP_SCRIPTS_P4RT_TOOL_HELPERS_H_
