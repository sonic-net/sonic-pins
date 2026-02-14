// Copyright (c) 2024, Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "lib/validator/pins_backend.h"

#include <iterator>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/time/time.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "lib/validator/validator_lib.h"
#include "thinkit/switch.h"

namespace pins_test {

PINSBackend::PINSBackend(std::vector<std::unique_ptr<thinkit::Switch>> switches)
    : ValidatorBackend({}), switches_map_() {
  devices_.reserve(switches.size());
  switches_map_.reserve(switches.size());
  for (auto it = switches.begin(); it != switches.end(); it++) {
    std::string chassis_name((*it)->ChassisName());
    switches_map_.insert({chassis_name, std::move(*it)});
    devices_.insert(std::move(chassis_name));
  }
}

absl::Status PINSBackend::P4rtAble(absl::string_view chassis,
                                   absl::Duration timeout) {
  auto sut = switches_map_.find(chassis);
  if (sut == switches_map_.end()) {
    return absl::InternalError(
        absl::StrCat("ValidatorBackend passed invalid chassis: ", chassis));
  }
  auto& [sut_name, sut_switch] = *sut;
  return pins_test::P4rtAble(*sut_switch);
}

absl::Status PINSBackend::GnmiAble(absl::string_view chassis,
                                   absl::Duration timeout) {
  auto sut = switches_map_.find(chassis);
  if (sut == switches_map_.end()) {
    return absl::InternalError(
        absl::StrCat("ValidatorBackend passed invalid chassis: ", chassis));
  }
  auto& [sut_name, sut_switch] = *sut;
  return pins_test::GnmiAble(*sut_switch, timeout);
}

absl::Status PINSBackend::GnoiAble(absl::string_view chassis,
                                   absl::Duration timeout) {
  auto sut = switches_map_.find(chassis);
  if (sut == switches_map_.end()) {
    return absl::InternalError(
        absl::StrCat("ValidatorBackend passed invalid chassis: ", chassis));
  }
  auto& [sut_name, sut_switch] = *sut;
  return pins_test::GnoiAble(*sut_switch, timeout);
}

absl::Status PINSBackend::PortsUp(absl::string_view chassis,
                                  absl::Duration timeout) {
  auto sut = switches_map_.find(chassis);
  if (sut == switches_map_.end()) {
    return absl::InternalError(
        absl::StrCat("ValidatorBackend passed invalid chassis: ", chassis));
  }
  auto& [sut_name, sut_switch] = *sut;
  return pins_test::PortsUp(*sut_switch, {}, /*with_healthz=*/true, timeout);
}

}  // namespace pins_test
