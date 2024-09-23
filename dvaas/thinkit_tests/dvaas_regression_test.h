#ifndef PINS_DVAAS_DVAAS_REGRESSION_TEST_H_
#define PINS_DVAAS_DVAAS_REGRESSION_TEST_H_

#include <memory>

#include "dvaas/dataplane_validation.h"
#include "dvaas/test_vector.pb.h"
#include "dvaas/thinkit_tests/dvaas_regression.pb.h"
#include "gtest/gtest.h"
#include "thinkit/mirror_testbed_fixture.h"
#include "gtest/gtest.h"

namespace dvaas {

struct DvaasRegressionTestParams {
  // The testbed to be validated against the test vector.
  // Using a shared_ptr because parameterized tests require objects to be
  // copyable.
  std::shared_ptr<thinkit::MirrorTestbedInterface> mirror_testbed;

  // Validates the dataplane behavior. Uses a shared_ptr because test parameters
  // must be copyable and DataplaneValidator is not.
  std::shared_ptr<dvaas::DataplaneValidator> validator;

  // Specifies user-facing parameters of DVaaS. See
  // dvaas::DataplaneValidationParams documentation for more details.
  dvaas::DataplaneValidationParams dvaas_params;

  // Contains the test vector that is used for the validation of the forwarding
  // behavior of the SUT in the given testbed, the minimal set of entities
  // that can be used to reproduce the failure of the test vector, the P4Info,
  // and a boolean indicating whether the test is currently failing.
  DvaasRegressionTestProto dvaas_regression_test_proto;
};

// TODO: Combine all the information required for a
// DVaasRegressionTest run into a single proto.
// DvaasRegressionTest validates the given testbed against the given
// proto. It installs the entries in the test vector on the switch,
// injects the input packets, collects the output packets, and compares the
// results against the expected outputs in the test vector.
class DvaasRegressionTest
    : public testing::TestWithParam<DvaasRegressionTestParams> {
protected:
  void SetUp() override { GetParam().mirror_testbed->SetUp(); }
  void TearDown() override { GetParam().mirror_testbed->TearDown(); }
};

} // namespace dvaas

#endif // PINS_DVAAS_DVAAS_REGRESSION_TEST_H_
