#ifndef PINS_TESTS_FORWARDING_MATCH_ACTION_COVERAGE_TEST_H_
#define PINS_TESTS_FORWARDING_MATCH_ACTION_COVERAGE_TEST_H_

#include <string>
#include <vector>

#include "p4_fuzzer/fuzzer_config.h"
#include "thinkit/mirror_testbed_fixture.h"

namespace p4_fuzzer {

struct MatchActionCoverageTestParams {
  thinkit::MirrorTestbedInterface* testbed_interface;
  p4::config::v1::P4Info p4info;
  FuzzerConfig config;
  // Entities that are installed on the switch before the test starts. These
  // entities are required to mask known bugs.
  std::vector<p4::v1::Entity> initial_entities_to_prevent_bugs;
};

// This test installs at least one table entry using (or not using if possible)
// each match field and each action in each possible table.
// Pushes the input `p4info` to the switch. Assumes that the switch is already
// configured with a gNMI config.
class MatchActionCoverageTestFixture
    : public testing::TestWithParam<MatchActionCoverageTestParams> {
 protected:
  void SetUp() override { GetParam().testbed_interface->SetUp(); }
  void TearDown() override { GetParam().testbed_interface->TearDown(); }
  ~MatchActionCoverageTestFixture() override {
    delete GetParam().testbed_interface;
  }
};

}  // namespace p4_fuzzer

#endif  // PINS_TESTS_FORWARDING_MATCH_ACTION_COVERAGE_TEST_H_
