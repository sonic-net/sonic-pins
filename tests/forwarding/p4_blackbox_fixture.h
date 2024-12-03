// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#ifndef PINS_TESTS_FORWARDING_P4_BLACKBOX_FIXTURE_H_
#define PINS_TESTS_FORWARDING_P4_BLACKBOX_FIXTURE_H_

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "lib/gnmi/gnmi_helper.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/pd.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/mirror_testbed_fixture.h"

namespace pins {

// Fixture for P4 blackbox testing. It performs test specific setup and
// teardown: Creates an initializes a P4RT channel, to get the switch ready to
// accept programming operations. Clears the switch of all table entries before
// every test.
class P4BlackboxFixture : public thinkit::MirrorTestbedFixture {
 public:
  void SetUp() override {
    MirrorTestbedFixture::SetUp();
    
    thinkit::MirrorTestbed& testbed =
      GetParam().mirror_testbed->GetMirrorTestbed();
    
    // Get a gNMI config from the switch to use for testing.
    ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, testbed.Sut().CreateGnmiStub());
    ASSERT_OK_AND_ASSIGN(std::string sut_gnmi_config,
                       pins_test::GetGnmiConfig(*sut_gnmi_stub));
    // Push the gnmi configuration.
    ASSERT_OK(
        pins_test::PushGnmiConfig(GetMirrorTestbed().Sut(), sut_gnmi_config));
    ASSERT_OK(pins_test::PushGnmiConfig(GetMirrorTestbed().ControlSwitch(),
                                        sut_gnmi_config));

    // Initialize the connection and clear table entries.
    ASSERT_OK_AND_ASSIGN(sut_p4rt_session_,
                         pdpi::P4RuntimeSession::CreateWithP4InfoAndClearTables(
                             GetMirrorTestbed().Sut(), p4info_));  
  }

  void TearDown() override {
    if (SutP4RuntimeSession() != nullptr) {
      // Clear all table entries to leave the switch in a clean state.
      EXPECT_OK(pdpi::ClearTableEntries(SutP4RuntimeSession()));
    }

    MirrorTestbedFixture::TearDown();
  }

  pdpi::P4RuntimeSession* SutP4RuntimeSession() const {
    return sut_p4rt_session_.get();
  }

  const pdpi::IrP4Info& IrP4Info() const { return ir_p4info_; }
  const p4::config::v1::P4Info& P4Info() const { return p4info_; }

 private:
  std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session_;
  pdpi::IrP4Info ir_p4info_ = 
      sai::GetIrP4Info(sai::Instantiation::kMiddleblock);
  p4::config::v1::P4Info p4info_ =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);
};

}  // namespace pins

#endif  // PINS_TESTS_FORWARDING_P4_BLACKBOX_FIXTURE_H_
