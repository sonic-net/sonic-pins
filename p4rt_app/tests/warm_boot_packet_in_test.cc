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
#include <cstdint>
#include <memory>
#include <string>
#include <utility>

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "gmock/gmock.h"
#include "grpcpp/security/credentials.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/sonic/packetio_interface.h"
#include "p4rt_app/tests/lib/p4runtime_grpc_service.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "swss/warm_restart.h"

namespace p4rt_app {
namespace {

class WarmBootPacketInTest : public testing::Test {
 protected:
  void SetUp() override {
    ASSERT_OK(p4rt_service_.GetP4rtServer().UpdateDeviceId(device_id_));
    const std::string address =
        absl::StrCat("localhost:", p4rt_service_.GrpcPort());
    auto stub =
        pdpi::CreateP4RuntimeStub(address, grpc::InsecureChannelCredentials());
    ASSERT_OK_AND_ASSIGN(p4rt_session_, pdpi::P4RuntimeSession::Create(
                                            std::move(stub), device_id_));
  }

  // For PacketIO to work correctly it requires both creating a port, and adding
  // a port translation.
  absl::Status AddPacketIoPort(const std::string& port_name,
                               const std::string& port_id) {
    RETURN_IF_ERROR(p4rt_service_.GetP4rtServer().AddPacketIoPort(port_name));
    RETURN_IF_ERROR(
        p4rt_service_.GetP4rtServer().AddPortTranslation(port_name, port_id));
    return absl::OkStatus();
  }

  absl::Status RemovePacketIoPort(const std::string& port_name) {
    RETURN_IF_ERROR(
        p4rt_service_.GetP4rtServer().RemovePortTranslation(port_name));
    RETURN_IF_ERROR(
        p4rt_service_.GetP4rtServer().RemovePacketIoPort(port_name));
    return absl::OkStatus();
  }

  test_lib::P4RuntimeGrpcService p4rt_service_ =
      test_lib::P4RuntimeGrpcService(P4RuntimeImplOptions{});
  std::unique_ptr<pdpi::P4RuntimeSession> p4rt_session_;
  uint64_t device_id_ = 100406;
};

TEST_F(WarmBootPacketInTest, PacketInEventsDroppedDuringNsfFreeze) {
  ASSERT_OK(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      p4rt_session_.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      sai::GetP4Info(sai::Instantiation::kMiddleblock)));
  ASSERT_OK(AddPacketIoPort("Ethernet1/1/0", "0"));
  ASSERT_OK(AddPacketIoPort("Ethernet1/1/1", "1"));

  // Send freeze notification.
  ASSERT_OK(p4rt_service_.GetP4rtServer().HandleWarmBootNotification(
      swss::WarmStart::WarmBootNotification::kFreeze));
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  // Push the expected PacketIn.
  EXPECT_OK(p4rt_service_.GetFakePacketIoInterface().PushPacketIn(
      "Ethernet1_1_0", "Ethernet1_1_1", "test packet1"));
  EXPECT_OK(p4rt_service_.GetFakePacketIoInterface().PushPacketIn(
      "Ethernet1_1_1", "Ethernet1_1_0", "test packet2"));

  sonic::PacketIoCounters counters =
      p4rt_service_.GetP4rtServer().GetPacketIoCounters();
  EXPECT_EQ(counters.packet_in_received, 0);
  EXPECT_EQ(counters.packet_in_errors, 0);

  // Set warm boot state as FAILED.
  p4rt_service_.GetWarmBootStateAdapter()->SetWarmBootState(
      swss::WarmStart::WarmStartState::FAILED);
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::FAILED);

  // Push the expected PacketIn.
  EXPECT_OK(p4rt_service_.GetFakePacketIoInterface().PushPacketIn(
      "Ethernet1/1/0", "Ethernet1/1/1", "test packet1"));
  EXPECT_OK(p4rt_service_.GetFakePacketIoInterface().PushPacketIn(
      "Ethernet1/1/1", "Ethernet1/1/0", "test packet2"));

  counters = p4rt_service_.GetP4rtServer().GetPacketIoCounters();
  EXPECT_EQ(counters.packet_in_received, 0);
  EXPECT_EQ(counters.packet_in_errors, 0);
}

TEST_F(WarmBootPacketInTest, PacketInAfterUnfreezeIsSent) {
  // Send freeze notification.
  ASSERT_OK(p4rt_service_.GetP4rtServer().HandleWarmBootNotification(
      swss::WarmStart::WarmBootNotification::kFreeze));
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::QUIESCENT);

  p4rt_service_.GetWarmBootStateAdapter()->SetWarmBootState(
      swss::WarmStart::WarmStartState::RECONCILED);
  EXPECT_EQ(p4rt_service_.GetWarmBootStateAdapter()->GetWarmBootState(),
            swss::WarmStart::WarmStartState::RECONCILED);

  // Unfreeze P4RT
  EXPECT_OK(p4rt_service_.GetP4rtServer().HandleWarmBootNotification(
      swss::WarmStart::WarmBootNotification::kUnfreeze));

  const std::string address =
      absl::StrCat("localhost:", p4rt_service_.GrpcPort());
  auto stub =
      pdpi::CreateP4RuntimeStub(address, grpc::InsecureChannelCredentials());
  std::unique_ptr<pdpi::P4RuntimeSession> p4rt_session;
  ASSERT_OK_AND_ASSIGN(p4rt_session, pdpi::P4RuntimeSession::Create(
                                         std::move(stub), device_id_));

  ASSERT_OK(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      p4rt_session.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      sai::GetP4Info(sai::Instantiation::kMiddleblock)));
  ASSERT_OK(AddPacketIoPort("Ethernet1/1/0", "0"));
  ASSERT_OK(AddPacketIoPort("Ethernet1/1/1", "1"));

  // Push the expected PacketIn.
  EXPECT_OK(p4rt_service_.GetFakePacketIoInterface().PushPacketIn(
      "Ethernet1/1/0", "Ethernet1/1/1", "test packet1"));
  EXPECT_OK(p4rt_service_.GetFakePacketIoInterface().PushPacketIn(
      "Ethernet1/1/1", "Ethernet1/1/0", "test packet2"));

  sonic::PacketIoCounters counters =
      p4rt_service_.GetP4rtServer().GetPacketIoCounters();
  EXPECT_EQ(counters.packet_in_received, 2);
  EXPECT_EQ(counters.packet_in_errors, 0);
}

}  // namespace
}  // namespace p4rt_app
