// Copyright 2025 Google LLC
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

#ifndef PINS_TESTS_FORWARDING_HASH_MULTISTAGE_TEST_H_
#define PINS_TESTS_FORWARDING_HASH_MULTISTAGE_TEST_H_

#include "tests/forwarding/hash_testfixture.h"
#include "gtest/gtest.h"

namespace pins_test {

struct HashMultiStageParameters {
  thinkit::MirrorTestbedInterface *mirror_testbed;
  p4::config::v1::P4Info p4_info;
};

// Multistage hash test.
class HashMultiStage
    : public HashTest,
      public testing::WithParamInterface<HashMultiStageParameters> {
public:
  HashMultiStage()
      : HashTest(GetParam().mirror_testbed, std::move(GetParam().p4_info)) {}
};

}  // namespace pins_test

#endif  // PINS_TESTS_FORWARDING_HASH_MULTISTAGE_TEST_H_
