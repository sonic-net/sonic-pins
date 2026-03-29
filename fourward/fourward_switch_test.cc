#include "fourward/fourward_switch.h"

#include <memory>

#include "github.com/openconfig/gnmi/proto/gnmi/gnmi.grpc.pb.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"

namespace dvaas {
namespace {

TEST(FourwardSwitchTest, CreateSucceeds) {
  ASSERT_OK_AND_ASSIGN(FourwardSwitch fourward_switch, FourwardSwitch::Create());
  EXPECT_FALSE(fourward_switch.ChassisName().empty());
  EXPECT_EQ(fourward_switch.DeviceId(), 1);
}

TEST(FourwardSwitchTest, CreateWithCustomDeviceId) {
  ASSERT_OK_AND_ASSIGN(FourwardSwitch fourward_switch,
                       FourwardSwitch::Create(42));
  EXPECT_EQ(fourward_switch.DeviceId(), 42);
}

TEST(FourwardSwitchTest, CreateP4RuntimeStubSucceeds) {
  ASSERT_OK_AND_ASSIGN(FourwardSwitch fourward_switch, FourwardSwitch::Create());
  EXPECT_OK(fourward_switch.CreateP4RuntimeStub());
}

TEST(FourwardSwitchTest, CreateGnmiStubSucceeds) {
  ASSERT_OK_AND_ASSIGN(FourwardSwitch fourward_switch, FourwardSwitch::Create());
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<gnmi::gNMI::StubInterface> gnmi_stub,
      fourward_switch.CreateGnmiStub());
  EXPECT_NE(gnmi_stub, nullptr);
}

}  // namespace
}  // namespace dvaas
