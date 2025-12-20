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

#include "tests/integration/system/nsf/component_validators/platform_validator.h"

#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "gutil/gutil/status.h"
#include "lib/gnmi/gnmi_helper.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "tests/integration/system/nsf/util.h"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

namespace pins_test {

absl::Status PlatformValidator::OnImageCopy(absl::string_view version,
                                            const Testbed& testbed,
                                            thinkit::SSHClient& ssh_client) {
  return absl::OkStatus();
}

absl::Status PlatformValidator::OnNsfReboot(absl::string_view version,
                                            const Testbed& testbed,
                                            thinkit::SSHClient& ssh_client) {
  LOG(INFO) << "PlatformValidator OnNsfReboot";

  return absl::OkStatus();
}

}  // namespace pins_test
