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

#ifndef PINS_THINKIT_MOCK_GENERIC_TESTBED_H_
#define PINS_THINKIT_MOCK_GENERIC_TESTBED_H_

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "thinkit/control_device.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/switch.h"
#include "thinkit/test_environment.h"
#include "gmock/gmock.h"

namespace thinkit {

class MockGenericTestbed : public GenericTestbed {
public:
  MOCK_METHOD(Switch &, Sut, (), (override));
  MOCK_METHOD(class ControlDevice &, ControlDevice, (), (override));
  MOCK_METHOD(class ControlDevice &, ControlDevice, (int index), (override));
  MOCK_METHOD(TestEnvironment &, Environment, (), (override));
  MOCK_METHOD((absl::flat_hash_map<std::string, InterfaceInfo>),
              GetSutInterfaceInfo, (), (override));
  MOCK_METHOD(otg::Openapi::StubInterface *, GetTrafficClient, (), (override));
  MOCK_METHOD(absl::StatusOr<HttpResponse>, SendRestRequestToIxia,
              (RequestType type, absl::string_view url,
               absl::string_view payload),
              (override));
};

} // namespace thinkit

#endif // PINS_THINKIT_MOCK_GENERIC_TESTBED_H_
