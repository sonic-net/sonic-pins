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

#ifndef THINKIT_MOCK_MIRROR_TESTBED_H_
#define THINKIT_MOCK_MIRROR_TESTBED_H_

#include "gmock/gmock.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/switch.h"
#include "thinkit/test_environment.h"

namespace thinkit {

class MockMirrorTestbed : public MirrorTestbed {
 public:
  MOCK_METHOD(Switch&, ControlSwitch, (), (override));
  MOCK_METHOD(Switch&, Sut, (), (override));
  MOCK_METHOD(TestEnvironment&, Environment, (), (override));
};

}  // namespace thinkit

#endif  //  THINKIT_MOCK_MIRROR_TESTBED_H_
