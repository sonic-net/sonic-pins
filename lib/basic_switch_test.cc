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

#include "lib/basic_switch.h"

#include <functional>
#include <memory>
#include <string_view>
#include <utility>

#include "cert/cert.grpc.pb.h"
#include "diag/diag.grpc.pb.h"
#include "factory_reset/factory_reset.grpc.pb.h"
#include "gmock/gmock.h"
#include "grpcpp/support/channel_arguments.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "os/os.grpc.pb.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "system/system.grpc.pb.h"

namespace pins_test {
namespace {

using ::gutil::IsOkAndHolds;
using ::testing::AtLeast;
using ::testing::IsNull;
using ::testing::MockFunction;

// Calls the mock function on `Create` and returns nullptr.
class MockCreateGrpcStub {
 public:
  explicit MockCreateGrpcStub(
      std::function<void(std::string_view, std::string_view)> mock)
      : mock_(std::move(mock)) {}

  template <class NewStubFunction>
  auto Create(NewStubFunction&& new_stub, std::string_view address,
              std::string_view chassis, std::string_view stub_type,
              const grpc::ChannelArguments& channel_arguments = {}) {
    mock_(address, chassis);
    return nullptr;
  }

 private:
  std::function<void(std::string_view, std::string_view)> mock_;
};

TEST(BasicSwitch, Works) {
  static constexpr char kChassis[] = "my.switch";
  SwitchServices services{.p4runtime_address = "p4rt",
                          .gnmi_address = "gnmi",
                          .gnoi_address = "gnoi"};
  MockFunction<void(std::string_view, std::string_view)> mock_function;
  EXPECT_CALL(mock_function, Call(services.p4runtime_address, kChassis))
      .Times(AtLeast(1));
  EXPECT_CALL(mock_function, Call(services.gnmi_address, kChassis))
      .Times(AtLeast(1));
  EXPECT_CALL(mock_function, Call(services.gnoi_address, kChassis))
      .Times(AtLeast(1));

  BasicSwitch<MockCreateGrpcStub> my_switch(kChassis, /*device_id=*/0,
                                            std::move(services),
                                            mock_function.AsStdFunction());
  EXPECT_EQ(my_switch.ChassisName(), kChassis);
  EXPECT_EQ(my_switch.DeviceId(), 0);
  EXPECT_THAT(my_switch.CreateP4RuntimeStub(), IsOkAndHolds(IsNull()));
  EXPECT_THAT(my_switch.CreateGnmiStub(), IsOkAndHolds(IsNull()));
  EXPECT_THAT(my_switch.CreateGnoiSystemStub(), IsOkAndHolds(IsNull()));
  EXPECT_THAT(my_switch.CreateGnoiDiagStub(), IsOkAndHolds(IsNull()));
  EXPECT_THAT(my_switch.CreateGnoiCertificateStub(), IsOkAndHolds(IsNull()));
  EXPECT_THAT(my_switch.CreateGnoiOsStub(), IsOkAndHolds(IsNull()));
  EXPECT_THAT(my_switch.CreateGnoiFactoryResetStub(), IsOkAndHolds(IsNull()));
}

TEST(BasicSwitch, MakeUniqueCompiles) {
  auto my_switch = std::make_unique<BasicSwitch<MockCreateGrpcStub>>(
      "my.switch", /*device_id=*/0, SwitchServices(),
      [](std::string_view, std::string_view) {});
}

}  // namespace
}  // namespace pins_test
