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
#ifndef PINS_TESTS_INTEGRATION_SYSTEM_NSF_NSF_LINK_FLAP_TEST_H_
#define PINS_TESTS_INTEGRATION_SYSTEM_NSF_NSF_LINK_FLAP_TEST_H_
#include <functional>
#include <memory>
#include <vector>
#include "tests/integration/system/nsf/interfaces/flow_programmer.h"
#include "tests/integration/system/nsf/interfaces/image_config_params.h"
#include "thinkit/generic_testbed_fixture.h"
#include "thinkit/ssh_client.h"

namespace pins_test {

struct NsfLinkFlapTestParams {
  thinkit::GenericTestbedInterface* testbed_interface;
  std::shared_ptr<thinkit::SSHClient> ssh_client;
  std::vector<pins_test::ImageConfigParams> image_config_params;
};

class NsfLinkFlapTestFixture
    : public thinkit::GenericTestbedFixture<NsfLinkFlapTestParams> {
 protected:
  NsfLinkFlapTestFixture() { GetParam().testbed_interface->ExpectLinkFlaps(); }
};

}  // namespace pins_test

#endif  // PINS_TESTS_INTEGRATION_SYSTEM_NSF_NSF_LINK_FLAP_TEST_H_
