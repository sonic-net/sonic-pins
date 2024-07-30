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

#include "thinkit/switch.h"

#include <cstdint>
#include <string>

#include "absl/status/status.h"
#include "cert/cert.grpc.pb.h"
#include "diag/diag.grpc.pb.h"
#include "factory_reset/factory_reset.grpc.pb.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "os/os.grpc.pb.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "system/system.grpc.pb.h"

namespace thinkit {
namespace {

using ::gutil::StatusIs;

class TestSwitch : public Switch {
  const std::string& ChassisName() override { return chassis_name_; }
  uint32_t DeviceId() override { return 0; }
  std::string chassis_name_;
};

TEST(Switch, FunctionsReturnUnimplemented) {
  TestSwitch sut;
  EXPECT_THAT(sut.CreateP4RuntimeStub(),
              StatusIs(absl::StatusCode::kUnimplemented));
  EXPECT_THAT(sut.CreateGnmiStub(), StatusIs(absl::StatusCode::kUnimplemented));
  EXPECT_THAT(sut.CreateGnoiFactoryResetStub(),
              StatusIs(absl::StatusCode::kUnimplemented));
  EXPECT_THAT(sut.CreateGnoiSystemStub(),
              StatusIs(absl::StatusCode::kUnimplemented));
  EXPECT_THAT(sut.CreateGnoiDiagStub(),
              StatusIs(absl::StatusCode::kUnimplemented));
  EXPECT_THAT(sut.CreateGnoiCertificateStub(),
              StatusIs(absl::StatusCode::kUnimplemented));
  EXPECT_THAT(sut.CreateGnoiOsStub(),
              StatusIs(absl::StatusCode::kUnimplemented));
}

}  // namespace
}  // namespace thinkit
