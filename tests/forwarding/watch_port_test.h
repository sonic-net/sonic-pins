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

#ifndef PINS_TESTS_FORWARDING_WATCH_PORT_TEST_H_
#define PINS_TESTS_FORWARDING_WATCH_PORT_TEST_H_

#include <thread>  // NOLINT: Need threads (instead of fiber) for upstream code.
#include <vector>

#include "p4_pdpi/p4_runtime_session.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "tests/forwarding/group_programming_util.h"
#include "tests/forwarding/packet_test_util.h"
#include "thinkit/mirror_testbed_fixture.h"

namespace pins {

// WatchPortTestFixture that holds member functions needed for testing watch
// port action.
// TODO: To be implemented.
class WatchPortTestFixture : public thinkit::MirrorTestbedFixture {};

}  // namespace pins

#endif  // PINS_TESTS_FORWARDING_WATCH_PORT_TEST_H_
