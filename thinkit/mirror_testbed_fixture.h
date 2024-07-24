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

#ifndef GOOGLE_THINKIT_MIRROR_TESTBED_TEST_FIXTURE_H_
#define GOOGLE_THINKIT_MIRROR_TESTBED_TEST_FIXTURE_H_

#include <memory>
#include <optional>

#include "absl/memory/memory.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "glog/logging.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "thinkit/mirror_testbed.h"

namespace thinkit {

// The ThinKit `MirrorTestbedInterface` defines an interface every test platform
// should implement. The expectations are such that the MirrorTestbed should
// only be accessed after SetUp() is called and before TearDown() is called.
class MirrorTestbedInterface {
 public:
  virtual ~MirrorTestbedInterface() = default;

  virtual void SetUp() = 0;
  virtual void TearDown() = 0;

  virtual MirrorTestbed& GetMirrorTestbed() = 0;

  // TODO: Move to TestEnvironment.
  virtual absl::Status SaveSwitchLogs(absl::string_view save_prefix) = 0;
};

// The Thinkit `MirrorTestbedFixtureParams` defines test parameters to
// `MirrorTestbedFixture` class.
struct MirrorTestbedFixtureParams {
  // Ownership of the MirrorTestbedInterface will be transferred to the
  // MirrorTestbedFixture class.
  MirrorTestbedInterface* mirror_testbed;

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
// Individual tests should use the googletest TEST_P macro:
//    TEST_P(MirrorTestbedFixture, MyTestName) {}
//
// PINS tests needing special SetUp or TearDown can inherit from this test
// fixture similar to:
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
//        MirrorTestbedFixture::SetUp();  // called last.
//      }
//    };
//
//  Individual tests should use the new suite name to take advantage of the
//  custom setup/teardown:
//    TEST_P(MyPinsTest, MyTestName) {}
class MirrorTestbedFixture
    : public testing::TestWithParam<MirrorTestbedFixtureParams> {
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
  MirrorTestbed& GetMirrorTestbed() {
    return mirror_testbed_interface_->GetMirrorTestbed();
  }

  // TODO: This should be moved to the TestEnvironment.
  absl::Status SaveSwitchLogs(absl::string_view save_prefix) {
    return mirror_testbed_interface_->SaveSwitchLogs(save_prefix);
  }

  const std::string& GetGnmiConfig() const { return GetParam().gnmi_config; }

  const p4::config::v1::P4Info& GetP4Info() const { return GetParam().p4_info; }

  const pdpi::IrP4Info& GetIrP4Info() const {
    // WARNING: the pdpi::IrP4Info will only be created once, and therefore it
    // will be created against the current P4Info in this test fixture. It is
    // unlikely that the P4Info will change because we do not open up the
    // P4Info to the derived test fixtures. However, we also do not
    // guarantee that the P4Info cannot be changed.
    static const pdpi::IrP4Info* const kIrP4Info = [] {
      absl::StatusOr<pdpi::IrP4Info> ir_p4_info =
          pdpi::CreateIrP4Info(GetParam().p4_info);
      CHECK(ir_p4_info.ok())  // Crash OK: Tests would be hard to debug without.
          << "Failed to translate the P4Info parameter into an IrP4Info.";
      return new pdpi::IrP4Info(std::move(ir_p4_info.value()));
    }();
    return *kIrP4Info;
  }

 private:
  // Takes ownership of the MirrorTestbedInterface parameter.
  std::unique_ptr<MirrorTestbedInterface> mirror_testbed_interface_ =
      absl::WrapUnique<MirrorTestbedInterface>(GetParam().mirror_testbed);
};

}  // namespace thinkit

#endif  // GOOGLE_THINKIT_MIRROR_TESTBED_TEST_FIXTURE_H_
