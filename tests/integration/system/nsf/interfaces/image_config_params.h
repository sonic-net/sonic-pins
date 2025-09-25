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

#ifndef PINS_TESTS_INTEGRATION_SYSTEM_NSF_INTERFACES_IMAGE_CONFIG_PARAMS_H_
#define PINS_TESTS_INTEGRATION_SYSTEM_NSF_INTERFACES_IMAGE_CONFIG_PARAMS_H_

#include <string>

#include "absl/time/time.h"
#include "p4/config/v1/p4info.pb.h"

namespace pins_test {

// Struct to hold image label, image version, config label and config parameters
// to be injected in PINs NSF integration tests.
struct ImageConfigParams {
  std::string image_label;
  std::string image_version;
  std::string config_label;
  std::string gnmi_config;
  p4::config::v1::P4Info p4_info;
  absl::Duration max_acceptable_outage;
};

}  // namespace pins_test

#endif  // PINS_TESTS_INTEGRATION_SYSTEM_NSF_INTERFACES_IMAGE_CONFIG_PARAMS_H_
