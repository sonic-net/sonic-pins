// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#ifndef PINS_TESTS_INTEGRATION_SYSTEM_RANDOM_BLACKBOX_EVENTS_TESTS_H_
#define PINS_TESTS_INTEGRATION_SYSTEM_RANDOM_BLACKBOX_EVENTS_TESTS_H_

#include <optional>

#include "p4/config/v1/p4info.pb.h"
#include "p4_fuzzer/fuzzer_config.h"
#include "thinkit/generic_testbed_fixture.h"

namespace pins_test {

struct RandomBlackboxEventsTestParams {
  thinkit::GenericTestbedInterface* testbed_interface;
  std::optional<p4::config::v1::P4Info> p4_info;
  p4_fuzzer::ConfigParams fuzzer_config_params;
};

class RandomBlackboxEventsTest
    : public thinkit::GenericTestbedFixture<RandomBlackboxEventsTestParams> {};

} // namespace pins_test

#endif // PINS_TESTS_INTEGRATION_SYSTEM_RANDOM_BLACKBOX_EVENTS_TESTS_H_
