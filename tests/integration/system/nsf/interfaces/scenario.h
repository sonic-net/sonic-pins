#ifndef PINS_TESTS_INTEGRATION_SYSTEM_NSF_INTERFACES_SCENARIO_H_
#define PINS_TESTS_INTEGRATION_SYSTEM_NSF_INTERFACES_SCENARIO_H_

namespace pins_test {

// NSF Upgrade test scenarios related to gNMI config push and P4 flow
// programming.
enum class NsfUpgradeScenario {
  kNoConfigPush,
  kOnlyConfigPush,
  kConfigPushBeforeAclFlowProgram,
  kConfigPushAfterAclFlowProgram,
  kNumNsfUpgradeScenarios,
};

} // namespace pins_test

#endif // PINS_TESTS_INTEGRATION_SYSTEM_NSF_INTERFACES_SCENARIO_H_
