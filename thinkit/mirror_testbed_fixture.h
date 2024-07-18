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

#include "absl/memory/memory.h"
#include "gtest/gtest.h"
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
    : public testing::TestWithParam<MirrorTestbedInterface*> {
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

 private:
  // Takes ownership of the MirrorTestbedInterface parameter.
  std::unique_ptr<MirrorTestbedInterface> mirror_testbed_interface_ =
      absl::WrapUnique<MirrorTestbedInterface>(GetParam());
};

}  // namespace thinkit

#endif  // GOOGLE_THINKIT_MIRROR_TESTBED_TEST_FIXTURE_H_
