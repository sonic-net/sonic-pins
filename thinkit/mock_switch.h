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

#ifndef THINKIT_MOCK_SWITCH_H_
#define THINKIT_MOCK_SWITCH_H_

#include <memory>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "thinkit/switch.h"

namespace thinkit {

class MockSwitch : public Switch {
 public:
  MOCK_METHOD(absl::string_view, ChassisName, (), (override));
  MOCK_METHOD(uint32_t, DeviceId, (), (override));
  MOCK_METHOD(absl::StatusOr<std::unique_ptr<p4::v1::P4Runtime::Stub>>,
              CreateP4RuntimeStub, (), (override));
  MOCK_METHOD(absl::StatusOr<std::unique_ptr<gnmi::gNMI::Stub>>, CreateGnmiStub,
              (), (override));
};

}  // namespace thinkit

#endif  // THINKIT_MOCK_SWITCH_H_
