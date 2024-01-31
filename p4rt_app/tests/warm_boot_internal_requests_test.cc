// Copyright 2025 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "p4rt_app/p4runtime/queue_translator.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/tests/lib/p4runtime_component_test_fixture.h"
#include "p4rt_app/tests/lib/p4runtime_grpc_service.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "swss/warm_restart.h"

namespace p4rt_app {
namespace {

class WarmBootInternalRequestsTest
    : public test_lib::P4RuntimeComponentTestFixture {
 protected:
  WarmBootInternalRequestsTest()
      : test_lib::P4RuntimeComponentTestFixture(sai::Instantiation::kTor) {}
};

TEST_F(WarmBootInternalRequestsTest,
       AddRemovePacketIoPortRequestsAreHandledDuringNsfFreeze) {
  // Send freeze notification.
  EXPECT_OK(p4rt_service_.GetP4rtServer().HandleWarmBootNotification(
      swss::WarmStart::WarmBootNotification::kFreeze));
  // Verify the warm boot state is QUIESCENT.
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  EXPECT_OK(p4rt_service_.GetP4rtServer().AddPacketIoPort("Ethernet0"));
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  EXPECT_OK(p4rt_service_.GetP4rtServer().RemovePacketIoPort("Ethernet0"));
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  // Set warm boot state as FAILED.
  p4rt_service_.GetWarmBootStateAdapter()->SetWarmBootState(
      swss::WarmStart::WarmStartState::FAILED);
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::FAILED);

  EXPECT_OK(p4rt_service_.GetP4rtServer().AddPacketIoPort("Ethernet0"));
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::FAILED);

  EXPECT_OK(p4rt_service_.GetP4rtServer().RemovePacketIoPort("Ethernet0"));
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::FAILED);
}

TEST_F(WarmBootInternalRequestsTest,
       UpdateDeviceIdRequestsAreHandledDuringNsfFreeze) {
  // Send freeze notification.
  EXPECT_OK(p4rt_service_.GetP4rtServer().HandleWarmBootNotification(
      swss::WarmStart::WarmBootNotification::kFreeze));
  // Verify the warm boot state is QUIESCENT.
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  EXPECT_OK(p4rt_service_.GetP4rtServer().UpdateDeviceId(11223344));
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  // Set warm boot state as FAILED.
  p4rt_service_.GetWarmBootStateAdapter()->SetWarmBootState(
      swss::WarmStart::WarmStartState::FAILED);
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::FAILED);

  EXPECT_OK(p4rt_service_.GetP4rtServer().UpdateDeviceId(11223344));
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::FAILED);
}

TEST_F(WarmBootInternalRequestsTest,
       AddRemovePortTranslationRequestsAreHandledDuringNsfFreeze) {
  // Send freeze notification.
  EXPECT_OK(p4rt_service_.GetP4rtServer().HandleWarmBootNotification(
      swss::WarmStart::WarmBootNotification::kFreeze));
  // Verify the warm boot state is QUIESCENT.
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  EXPECT_OK(
      p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet1/1/0", "0"));
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  EXPECT_OK(
      p4rt_service_.GetP4rtServer().RemovePortTranslation("Ethernet1/1/0"));
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  // Set warm boot state as FAILED.
  p4rt_service_.GetWarmBootStateAdapter()->SetWarmBootState(
      swss::WarmStart::WarmStartState::FAILED);
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::FAILED);

  EXPECT_OK(
      p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet1/1/0", "0"));
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::FAILED);

  EXPECT_OK(
      p4rt_service_.GetP4rtServer().RemovePortTranslation("Ethernet1/1/0"));
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::FAILED);
}

TEST_F(WarmBootInternalRequestsTest,
       SetCpuQueueTranslatorRequestsAreHandledDuringNsfFreeze) {
  // Send freeze notification.
  EXPECT_OK(p4rt_service_.GetP4rtServer().HandleWarmBootNotification(
      swss::WarmStart::WarmBootNotification::kFreeze));
  // Verify the warm boot state is QUIESCENT.
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  p4rt_service_.GetP4rtServer().SetQueueTranslator(
      QueueTranslator::Empty(), "CPU");
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  // Set warm boot state as FAILED.
  p4rt_service_.GetWarmBootStateAdapter()->SetWarmBootState(
      swss::WarmStart::WarmStartState::FAILED);
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::FAILED);

  p4rt_service_.GetP4rtServer().SetQueueTranslator(
      QueueTranslator::Empty(), "CPU");
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::FAILED);
}

TEST_F(WarmBootInternalRequestsTest,
       VerifyStateRequestsAreHandledDuringNsfFreeze) {
  // Send freeze notification.
  EXPECT_OK(p4rt_service_.GetP4rtServer().HandleWarmBootNotification(
      swss::WarmStart::WarmBootNotification::kFreeze));
  // Verify the warm boot state is QUIESCENT.
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  EXPECT_OK(p4rt_service_.GetP4rtServer().VerifyState());
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  // Set warm boot state as FAILED.
  p4rt_service_.GetWarmBootStateAdapter()->SetWarmBootState(
      swss::WarmStart::WarmStartState::FAILED);
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::FAILED);

  EXPECT_OK(p4rt_service_.GetP4rtServer().VerifyState());
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::FAILED);
}

TEST_F(WarmBootInternalRequestsTest,
       DumpDebugDataRequestsAreHandledDuringNsfFreeze) {
  // Send freeze notification.
  EXPECT_OK(p4rt_service_.GetP4rtServer().HandleWarmBootNotification(
      swss::WarmStart::WarmBootNotification::kFreeze));
  // Verify the warm boot state is QUIESCENT.
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  EXPECT_OK(
      p4rt_service_.GetP4rtServer().DumpDebugData(testing::TempDir(), "alert"));
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  // Set warm boot state as FAILED.
  p4rt_service_.GetWarmBootStateAdapter()->SetWarmBootState(
      swss::WarmStart::WarmStartState::FAILED);
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::FAILED);

  EXPECT_OK(
      p4rt_service_.GetP4rtServer().DumpDebugData(testing::TempDir(), "alert"));
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::FAILED);
}

}  // namespace
}  // namespace p4rt_app
