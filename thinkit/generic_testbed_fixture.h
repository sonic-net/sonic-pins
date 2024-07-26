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

#ifndef PINS_THINKIT_GENERIC_TESTBED_TEST_FIXTURE_H_
#define PINS_THINKIT_GENERIC_TESTBED_TEST_FIXTURE_H_

#include <memory>
#include <optional>
#include <string>
#include <vector>

#include "absl/memory/memory.h"
#include "absl/status/statusor.h"
#include "gtest/gtest.h"
#include "p4/config/v1/p4info.pb.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/proto/generic_testbed.pb.h"

namespace thinkit {

// The ThinKit `GenericTestbedInterface` defines an interface every test
// platform should implement. The expectations are such that the GenericTestbed
// should only be accessed after SetUp() is called and before TearDown() is
// called.
class GenericTestbedInterface {
 public:
  virtual ~GenericTestbedInterface() = default;

  virtual void SetUp() = 0;
  virtual void TearDown() = 0;

  // Declares the test requirements for this test and returns a testbed that can
  // support them.
  virtual absl::StatusOr<std::unique_ptr<GenericTestbed>>
  GetTestbedWithRequirements(const thinkit::TestRequirements& requirements) = 0;

  // Calling this function indicates that the test is expected to produce link
  // flaps.
  virtual void ExpectLinkFlaps() = 0;
};

// The Thinkit `GenericTestbedFixtureParams` defines default test parameters to
// the `GenericTestbedFixture` class.
struct GenericTestbedFixtureParams {
  // Ownership transferred in GenericTestbedFixture class.
  GenericTestbedInterface* testbed_interface;
  std::string gnmi_config;
  p4::config::v1::P4Info p4_info;
};

// The ThinKit `GenericTestbedFixture` class acts as a base test fixture for
// platform independent PINS tests. Any platform specific SetUp or TearDown
// requirements are abstracted through the ThinKit GenericTestbedInterface which
// is passed as a parameter.
//
// New PINS tests should extend this fixture, and if needed can extend the
// SetUp() and/or TearDown() methods:
//    class MyPinsTest : public thinkit::GenericTestbedFixture<> {
//      void SetUp() override {
//        GenericTestbedFixture<>::SetUp();  // called first.
//
//        // custom setup steps ...
//      }
//
//      void TearDown() override {
//        // custom tear down steps ...
//
//        GenericTestbedFixture<>::TearDown();  // called last.
//      }
//    };
//
//  Individual tests should use the new suite name:
//    TEST_P(MyPinsTest, MyTestName) {}
//
// For those wanting to pass their own custom parameters, as long as it has a
// member 'GenericTestbedInterface* testbed_interface', it can be passed as the
// template parameter:
//    struct MyParams { GenericTestbedInterface* testbed_interface; ...};
//    class MyPinsTest : public thinkit::GenericTestbedFixture<MyParams> {...};
template <class Params = GenericTestbedFixtureParams>
class GenericTestbedFixture : public testing::TestWithParam<Params> {
 protected:
  // A derived class that needs/wants to do its own setup can override this
  // method. However, it should take care to call this base setup first. That
  // will ensure the platform is ready, and in a healthy state.
  void SetUp() override { generic_testbed_interface_->SetUp(); }

  // A derived class that needs/wants to do its own teardown can override this
  // method. However, it should take care to call this base teardown last. Once
  // this method is called accessing the platform can result in unexpected
  // behaviors.
  void TearDown() override { generic_testbed_interface_->TearDown(); }

  // Accessor for the Generic testbed. This is only safe to be called after the
  // SetUp has completed.
  absl::StatusOr<std::unique_ptr<GenericTestbed>> GetTestbedWithRequirements(
      const thinkit::TestRequirements& requirements) {
    return generic_testbed_interface_->GetTestbedWithRequirements(requirements);
  }

 private:
  // Takes ownership of the GenericTestbedInterface parameter.
  std::unique_ptr<GenericTestbedInterface> generic_testbed_interface_ =
      absl::WrapUnique<GenericTestbedInterface>(
          this->GetParam().testbed_interface);
};

}  // namespace thinkit

#endif  // PINS_THINKIT_GENERIC_TESTBED_TEST_FIXTURE_H_
