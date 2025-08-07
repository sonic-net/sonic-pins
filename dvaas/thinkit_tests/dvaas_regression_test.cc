#include "dvaas/thinkit_tests/dvaas_regression_test.h"

#include <memory>
#include <optional>

#include "dvaas/dataplane_validation.h"
#include "dvaas/mirror_testbed_config.h"
#include "dvaas/switch_api.h"
#include "dvaas/test_vector.pb.h"
#include "dvaas/validation_result.h"
#include "gutil/status_matchers.h" 
#include "p4_pdpi/p4_runtime_session_extras.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"  
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/p4_runtime_session_extras.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "thinkit/mirror_testbed.h"

namespace dvaas {
namespace {

TEST_P(DvaasRegressionTest, DvaasRegressionTest) {
  thinkit::MirrorTestbed& testbed =
      GetParam().mirror_testbed->GetMirrorTestbed();
  if (GetParam().dvaas_regression_test_proto.has_p4info()) {
    ASSERT_OK_AND_ASSIGN(
        std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session,
        pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
            testbed.Sut(), /*gnmi_config=*/std::nullopt,
            GetParam().dvaas_regression_test_proto.p4info()));
    ASSERT_OK_AND_ASSIGN(
        std::unique_ptr<pdpi::P4RuntimeSession> control_switch_p4rt_session,
        pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
            testbed.ControlSwitch(), /*gnmi_config=*/std::nullopt,
            /*p4info=*/GetParam().dvaas_regression_test_proto.p4info()));
  }
  ASSERT_OK_AND_ASSIGN(MirrorTestbedConfigurator configured_testbed,
                       MirrorTestbedConfigurator::Create(&testbed));

  // In PINs, since the only supported non-table entry entities are
  // `multicast_group_entry`s, and each of those has a corresponding
  // `multicast_router_interface_table_entry` that uses the same port, we can be
  // certain that all the ports used in the full set of entities are also used
  // in the subset that is the table entries.
  //
  // TODO: Directly pass in IR entities instead of extracting IR
  // table entries once support for IR entities has been added to
  // `ConfigureForForwardingTest`.
  pdpi::IrTableEntries ir_table_entries;
  for (const pdpi::IrEntity& ir_entity :
       GetParam()
           .dvaas_regression_test_proto.minimal_set_of_entities()
           .entities()) {
    if (ir_entity.has_table_entry()) {
      *ir_table_entries.add_entries() = ir_entity.table_entry();
    }
  }
  ASSERT_OK(configured_testbed.ConfigureForForwardingTest({
      .configure_sut_port_ids_for_expected_entries = true,
      .sut_entries_to_expect_after_configuration = ir_table_entries,
      .mirror_sut_ports_ids_to_control_switch = true,
  }));
  // Install the entities on the switch.
  ASSERT_OK(pdpi::InstallIrEntities(
      *configured_testbed.SutApi().p4rt,
      GetParam().dvaas_regression_test_proto.minimal_set_of_entities()));
  dvaas::DataplaneValidationParams params = GetParam().dvaas_params;
  params.packet_test_vector_override = {
      GetParam().dvaas_regression_test_proto.test_vector(),
  };
  ASSERT_OK_AND_ASSIGN(
      dvaas::ValidationResult validation_result,
      GetParam().validator->ValidateDataplaneUsingExistingSwitchApis(
          configured_testbed.SutApi(), configured_testbed.ControlSwitchApi(),
          params));
  bool currently_failing =
      GetParam().dvaas_regression_test_proto.currently_failing();
  if (currently_failing) {
    EXPECT_EQ(validation_result.GetSuccessRate(), 0.0)
        << "Expected test to be failing based on `currently_failing = true`, "
           "but success rate was above 0.0.";
  } else {
    EXPECT_OK(validation_result.HasSuccessRateOfAtLeast(1.0));
  }
  ASSERT_OK(configured_testbed.RestoreToOriginalConfiguration());
}

} // namespace
} // namespace dvaas
