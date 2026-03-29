#include "fourward/fourward_switch.h"

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

}  // namespace
}  // namespace dvaas
