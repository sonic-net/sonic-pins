// Copyright 2025 Google LLC
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

#include "tests/forwarding/p4info_push_test.h"

#include <memory>

#include "absl/log/log.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "lib/gnmi/gnmi_helper.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "thinkit/switch.h"

// Note: "gutil/status_matchers.h" is needed for GitHub builds to succeed.

namespace pins {
namespace {

// Sends P4Info to the switch and makes sure it works.
TEST_P(P4InfoPushTestFixture, P4InfoPushTest) {
  LOG(INFO) << "Test started";
  ASSERT_OK(GetParam()
                .mirror_testbed->GetMirrorTestbed()
                .Environment()
                .StoreTestArtifact("pushed_p4info.pb.txt", GetParam().p4info));

  // Push the gNMI configuration and P4Info to the SUT.
  thinkit::Switch& thinkit_switch =
      GetParam().mirror_testbed->GetMirrorTestbed().Sut();
  LOG(INFO) << "Pushing gNMI config & P4info to "
            << thinkit_switch.ChassisName();
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<pdpi::P4RuntimeSession> sut_p4rt_session,
      pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
          thinkit_switch, GetParam().gnmi_config, GetParam().p4info));

  // Pull P4Info, make sure it is the same as the pushed one.
  LOG(INFO) << "Pulling P4Info";
  ASSERT_OK_AND_ASSIGN(const auto response,
                       pdpi::GetForwardingPipelineConfig(
                           sut_p4rt_session.get(),
                           p4::v1::GetForwardingPipelineConfigRequest::ALL));
  ASSERT_THAT(response.config().p4info(),
              gutil::EqualsProto(GetParam().p4info));

  LOG(INFO) << "Test finished successfully";
}

// TODO: implement a negative test.
}  // namespace
}  // namespace pins
