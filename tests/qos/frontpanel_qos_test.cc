#include "tests/qos/frontpanel_qos_test.h"

#include <memory>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "tests/lib/switch_test_setup_helpers.h"

namespace pins_test {

TEST_P(FrontpanelQosTest, PacketsGetMappedToCorrectQueuesBasedOnDscp) {
  // Pick a testbed with SUT connected to an Ixia on 2 ports, so we can
  // oversubscribe switch egress port.
  auto requirements = gutil::ParseProtoOrDie<thinkit::TestRequirements>(
      R"pb(
        interface_requirements { count: 2 interface_mode: TRAFFIC_GENERATOR }
      )pb");
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<thinkit::GenericTestbed> testbed,
      GetParam().testbed_interface->GetTestbedWithRequirements(requirements));

  // Switch set up.
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt,
      ConfigureSwitchAndReturnP4RuntimeSession(
          testbed->Sut(), GetParam().gnmi_config, GetParam().p4info));

  // TODO: actual testing.
}

}  // namespace pins_test
