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
#ifndef PINS_TESTS_FORWARDING_L3_ADMIT_TEST_H_
#define PINS_TESTS_FORWARDING_L3_ADMIT_TEST_H_

#include <memory>

#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "tests/forwarding/mirror_blackbox_test_fixture.h"
#include "tests/lib/packet_in_helper.h"
#include "thinkit/mirror_testbed_fixture.h"

namespace pins {

class L3AdmitTestFixture : public pins_test::MirrorBlackboxTestFixture {
 protected:
  void TearDown() override {
    // MirrorBlackboxTestFixture unnecessarily clears tables at TearDown. This
    // is not harmful for other tests but is problematic for l3_admit_tests
    // since the P4RT session to the controller is closed during the tests (see
    // lib/packet_in_helper.h). Therefore, We bypass table clearance in
    // TearDown.
    MirrorTestbedFixture::TearDown();
  }
};

}  // namespace pins

#endif  // PINS_TESTS_FORWARDING_L3_ADMIT_TEST_H_
