// Copyright 2026 Google LLC
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

#include "fourward/fourward_mirror_testbed.h"

#include <memory>

#include "github.com/openconfig/gnmi/proto/gnmi/gnmi.grpc.pb.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "p4/v1/p4runtime.grpc.pb.h"

namespace dvaas {
namespace {

TEST(FourwardMirrorTestbedTest, CreateSucceeds) {
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<FourwardMirrorTestbed> testbed,
                        FourwardMirrorTestbed::Create());
  EXPECT_FALSE(testbed->Sut().ChassisName().empty());
  EXPECT_FALSE(testbed->ControlSwitch().ChassisName().empty());
  EXPECT_EQ(testbed->Sut().DeviceId(), 1);
  EXPECT_EQ(testbed->ControlSwitch().DeviceId(), 2);
}

TEST(FourwardMirrorTestbedTest, P4RuntimeStubsConnect) {
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<FourwardMirrorTestbed> testbed,
                        FourwardMirrorTestbed::Create());
  EXPECT_OK(testbed->Sut().CreateP4RuntimeStub());
  EXPECT_OK(testbed->ControlSwitch().CreateP4RuntimeStub());
}

TEST(FourwardMirrorTestbedTest, GnmiStubsConnect) {
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<FourwardMirrorTestbed> testbed,
                        FourwardMirrorTestbed::Create());
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<gnmi::gNMI::StubInterface> sut_gnmi,
      testbed->Sut().CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<gnmi::gNMI::StubInterface> control_gnmi,
      testbed->ControlSwitch().CreateGnmiStub());
  EXPECT_NE(sut_gnmi, nullptr);
  EXPECT_NE(control_gnmi, nullptr);
}

TEST(FourwardMirrorTestbedTest, CustomDeviceIds) {
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<FourwardMirrorTestbed> testbed,
                        FourwardMirrorTestbed::Create(
                            /*sut_device_id=*/10, /*control_device_id=*/20));
  EXPECT_EQ(testbed->Sut().DeviceId(), 10);
  EXPECT_EQ(testbed->ControlSwitch().DeviceId(), 20);
}

}  // namespace
}  // namespace dvaas
