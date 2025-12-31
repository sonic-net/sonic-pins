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

#ifndef PINS_THINKIT_MIRROR_TESTBED_TEST_FIXTURE_H_
#define PINS_THINKIT_MIRROR_TESTBED_TEST_FIXTURE_H_

#include <memory>
#include <string>

#include "absl/memory/memory.h"
#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "p4/config/v1/p4info.pb.h"
#include "thinkit/mirror_testbed.h"
#include "gtest/gtest.h"

namespace thinkit {

// The ThinKit `MirrorTestbedInterface` defines an interface every test platform
// should implement. The expectations are such that the MirrorTestbed should
// only be accessed after SetUp() is called and before TearDown() is called.
class MirrorTestbedInterface {
public:
  virtual ~MirrorTestbedInterface() = default;

  virtual void SetUp() = 0;
  virtual void TearDown() = 0;

  virtual MirrorTestbed &GetMirrorTestbed() = 0;

  // TODO: Move to TestEnvironment.
  virtual absl::Status SaveSwitchLogs(absl::string_view save_prefix) = 0;

  // Calling this function indicates that the test is expected to produce link
  // flaps. Call this function before SetUp().
  virtual void ExpectLinkFlaps() = 0;
};

// The Thinkit `MirrorTestbedFixtureParams` defines test parameters to
// `MirrorTestbedFixture` class.
struct MirrorTestbedFixtureParams {
  // Ownership of the MirrorTestbedInterface will be transferred to the
  // MirrorTestbedFixture class.
  MirrorTestbedInterface *mirror_testbed;

  // To enable testing of different platforms we pass the gNMI config and P4Info
  // as arguments to the MirrorTestbedFixture.
  std::string gnmi_config;
  p4::config::v1::P4Info p4_info;
};

// The ThinKit `MirrorTestbedFixture` class acts as a base test fixture for
// platform independent PINS tests. Any platform specific SetUp or TearDown
// requirements are abstracted through the ThinKit MirrorTestbedInterface which
// is passed as a parameter.
//
// New PINS tests should extend this fixture, and if needed can extend the
// SetUp() and/or TearDown() methods:
//    class MyPinsTest : public thinkit::MirrorTestbedFixture {
//      void SetUp() override {
//        MirrorTestbedFixture::SetUp();  // called first.
//
//        // custom setup steps ...
//      }
//
//      void TearDown() override {
//        // custom tear down steps ...
//
//        MirrorTestbedFixture::TearDown();  // called last.
//      }
//    };
//
//  Individual tests should use the new suite name:
//    TEST_P(MyPinsTest, MyTestName) {}
//
// For those wanting to pass their own custom parameters, as long as it has a
// member 'MirrorTestbedInterface* mirror_testbed', it can be passed as the
// template parameter:
//    struct MyParams { MirrorTestbedInterface* mirror_testbed; ...};
//    class MyPinsTest :
//      public thinkit::MirrorTestbedFixtureWithParams<MyParams> {...};
template <class Params>
class MirrorTestbedFixtureWithParams : public testing::TestWithParam<Params> {
protected:
  // A derived class that needs/wants to do its own setup can override this
  // method. However, it should take care to call this base setup first. That
  // will ensure the platform is ready, and in a healthy state.
  void SetUp() override { mirror_testbed_interface_->SetUp(); }

  // A derived class that needs/wants to do its own teardown can override this
  // method. However, it should take care to call this base teardown last. Once
  // this method is called accessing the platform can result in unexpected
  // behaviors.
  void TearDown() override { mirror_testbed_interface_->TearDown(); }

  // Accessor for the mirror testbed. This is only safe to be called after the
  // SetUp has completed.
  MirrorTestbed &GetMirrorTestbed() {
    return mirror_testbed_interface_->GetMirrorTestbed();
  }

  // TODO: This should be moved to the TestEnvironment.
  absl::Status SaveSwitchLogs(absl::string_view save_prefix) {
    return mirror_testbed_interface_->SaveSwitchLogs(save_prefix);
  }

  const std::string& gnmi_config() const {
    return this->GetParam().gnmi_config;
  }

  const p4::config::v1::P4Info& p4_info() const {
    return this->GetParam().p4_info;
  }

private:
  // Takes ownership of the MirrorTestbedInterface parameter.
  std::unique_ptr<MirrorTestbedInterface> mirror_testbed_interface_ =
      absl::WrapUnique<MirrorTestbedInterface>(this->GetParam().mirror_testbed);
};

using MirrorTestbedFixture =
    MirrorTestbedFixtureWithParams<MirrorTestbedFixtureParams>;

} // namespace thinkit

#endif // PINS_THINKIT_MIRROR_TESTBED_TEST_FIXTURE_H_
