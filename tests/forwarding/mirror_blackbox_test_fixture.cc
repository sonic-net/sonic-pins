#include "tests/forwarding/mirror_blackbox_test_fixture.h"

#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"
#include "proto/gnmi/gnmi.pb.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "thinkit/mirror_testbed_fixture.h"

namespace pins_test {

void MirrorBlackboxTestFixture::SetUp() {
  thinkit::MirrorTestbedFixture::SetUp();

  // Initialize the connection, clear table entries, and push GNMI
  // configuration for the SUT and Control switch.
  std::string sut_gnmi_config;
  ASSERT_OK_AND_ASSIGN(
      std::tie(sut_p4rt_session_, control_switch_p4rt_session_),
      pins_test::ConfigureSwitchPairAndReturnP4RuntimeSessionPair(
          GetMirrorTestbed().Sut(), GetMirrorTestbed().ControlSwitch(),
	  gnmi_config(), p4_info()));

}

void MirrorBlackboxTestFixture::TearDown() {
  // Clear all table entries to leave the sut and control switch in a clean
  // state.
  EXPECT_OK(pdpi::ClearTableEntries(&GetSutP4RuntimeSession()));
  EXPECT_OK(pdpi::ClearTableEntries(&GetControlP4RuntimeSession()));

}

}  // namespace pins_test
