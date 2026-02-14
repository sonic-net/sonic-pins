// Copyright 2020 Google LLC
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
#include "p4rt_app/p4runtime/p4runtime_impl.h"

#include "absl/strings/string_view.h"
#include "boost/bimap.hpp"
#include "gmock/gmock.h"
#include "google/protobuf/text_format.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "p4_infra/p4_pdpi/utils/ir.h"
#include "p4rt_app/p4runtime/p4info_verification.h"
#include "p4rt_app/sonic/adapters/mock_system_call_adapter.h"
#include "p4rt_app/sonic/packetio_impl.h"
#include "p4rt_app/sonic/packetio_port.h"
#include "sai_p4/fixed/ids.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace p4rt_app {
namespace {

using ::gutil::EqualsProto;
using ::gutil::StatusIs;
using ::testing::DoAll;
using ::testing::Return;
using ::testing::SetArgPointee;

void SetupPacketInMetadata(const std::string& ingress_port,
                           const std::string& target_egress,
                           p4::v1::PacketIn& packet) {
  auto metadata = packet.add_metadata();
  metadata->set_metadata_id(
      PACKET_IN_INGRESS_PORT_ID);  // metadata id for egress_port.
  metadata->set_value(ingress_port);

  metadata = packet.add_metadata();
  metadata->set_metadata_id(
      PACKET_IN_TARGET_EGRESS_PORT_ID);  // metadata id for inject into ingress
                                         // stage, unused.
  metadata->set_value(target_egress);
}

void SetupPacketOutMetadata(const std::string& egress_port, int egress_bitwidth,
                            int submit_to_ingress, int ingress_bitwidth,
                            p4::v1::PacketOut& packet) {
  auto metadata = packet.add_metadata();
  metadata->set_metadata_id(
      PACKET_OUT_EGRESS_PORT_ID);  // metadata id for egress_port.
  metadata->set_value(egress_port);

  metadata = packet.add_metadata();
  metadata->set_metadata_id(
      PACKET_OUT_SUBMIT_TO_INGRESS_ID);  // metadata id for inject into ingress
                                         // stage, unused.
  ASSERT_OK_AND_ASSIGN(
      auto ingress,
      pdpi::UintToNormalizedByteString(static_cast<uint64_t>(submit_to_ingress),
                                       ingress_bitwidth));
  metadata->set_value(ingress);

  metadata = packet.add_metadata();
  metadata->set_metadata_id(
      PACKET_OUT_UNUSED_PAD_ID);  // metadata id for unused_pad, unused..
  ASSERT_OK_AND_ASSIGN(
      auto pad, pdpi::UintToNormalizedByteString(static_cast<uint64_t>(0), 7));
  metadata->set_value(pad);
}

TEST(P4RuntimeImplTest, SendPacketOutEgressPortUsingPortIdOk) {
  p4::v1::PacketOut packet;
  SetupPacketOutMetadata(/*egress_port*/ "1", /*egress_bitwidth*/ 9,
                         /*submit_to_ingress*/ 0,
                         /*ingress_bitwidth*/ 1, packet);
  pdpi::IrP4Info ir_p4_info =
      sai::GetIrP4Info(sai::Instantiation::kMiddleblock);
  int fd[2];
  EXPECT_GE(pipe(fd), 0);
  std::vector<std::unique_ptr<p4rt_app::sonic::PacketIoPortSockets>>
      port_sockets;
  port_sockets.push_back(
      absl::make_unique<p4rt_app::sonic::PacketIoPortSockets>("Ethernet1",
                                                              fd[1]));

  boost::bimap<std::string, std::string> port_maps;
  port_maps.insert({"Ethernet1", "1"});

  auto mock_call_adapter = absl::make_unique<sonic::MockSystemCallAdapter>();
  struct ifreq if_resp { /*ifr_name=*/
    {""}, /*ifr_flags=*/{
      { IFF_UP | IFF_RUNNING }
    }
  };
  EXPECT_CALL(*mock_call_adapter, ioctl)
      .WillOnce(DoAll(SetArgPointee<2>(if_resp), Return(0)));
  EXPECT_CALL(*mock_call_adapter, write).Times(1);
  auto packetio_impl = absl::make_unique<sonic::PacketIoImpl>(
      std::move(mock_call_adapter), std::move(port_sockets));
  EXPECT_OK(SendPacketOut(ir_p4_info, /*translate_port_ids=*/true, port_maps,
                          packetio_impl.get(), packet));
}

TEST(P4RuntimeImplTest, SendPacketOutEgressPortUsingPortNameOk) {
  p4::v1::PacketOut packet;
  SetupPacketOutMetadata(/*egress_port*/ "Ethernet1", /*egress_bitwidth*/ 9,
                         /*submit_to_ingress*/ 0,
                         /*ingress_bitwidth*/ 1, packet);
  pdpi::IrP4Info ir_p4_info =
      sai::GetIrP4Info(sai::Instantiation::kMiddleblock);
  int fd[2];
  EXPECT_GE(pipe(fd), 0);
  std::vector<std::unique_ptr<p4rt_app::sonic::PacketIoPortSockets>>
      port_sockets;
  port_sockets.push_back(
      absl::make_unique<p4rt_app::sonic::PacketIoPortSockets>("Ethernet1",
                                                              fd[1]));

  boost::bimap<std::string, std::string> port_maps;
  port_maps.insert({"Ethernet1", "1"});

  auto mock_call_adapter = absl::make_unique<sonic::MockSystemCallAdapter>();
  struct ifreq if_resp { /*ifr_name=*/
    {""}, /*ifr_flags=*/{
      { IFF_UP | IFF_RUNNING }
    }
  };
  EXPECT_CALL(*mock_call_adapter, ioctl)
      .WillOnce(DoAll(SetArgPointee<2>(if_resp), Return(0)));
  EXPECT_CALL(*mock_call_adapter, write).Times(1);
  auto packetio_impl = absl::make_unique<sonic::PacketIoImpl>(
      std::move(mock_call_adapter), std::move(port_sockets));
  EXPECT_OK(SendPacketOut(ir_p4_info, /*translate_port_ids=*/false, port_maps,
                          packetio_impl.get(), packet));
}

TEST(P4RuntimeImplTest, SendPacketOutIngressInjectOk) {
  p4::v1::PacketOut packet;
  SetupPacketOutMetadata(/*egress_port*/ "0", /*egress_bitwidth*/ 9,
                         /*submit_to_ingress*/ 1,
                         /*ingress_bitwidth*/ 1, packet);
  pdpi::IrP4Info ir_p4_info =
      sai::GetIrP4Info(sai::Instantiation::kMiddleblock);
  int fd[2];
  EXPECT_GE(pipe(fd), 0);
  std::vector<std::unique_ptr<p4rt_app::sonic::PacketIoPortSockets>>
      port_sockets;
  port_sockets.push_back(
      absl::make_unique<p4rt_app::sonic::PacketIoPortSockets>("send_to_ingress",
                                                              fd[1]));

  auto mock_call_adapter = absl::make_unique<sonic::MockSystemCallAdapter>();
  struct ifreq if_resp { /*ifr_name=*/
    {""}, /*ifr_flags=*/{
      { IFF_UP | IFF_RUNNING }
    }
  };
  EXPECT_CALL(*mock_call_adapter, ioctl)
      .WillOnce(DoAll(SetArgPointee<2>(if_resp), Return(0)));
  EXPECT_CALL(*mock_call_adapter, write).Times(1);
  auto packetio_impl = absl::make_unique<sonic::PacketIoImpl>(
      std::move(mock_call_adapter), std::move(port_sockets));

  boost::bimap<std::string, std::string> port_maps;
  EXPECT_OK(SendPacketOut(ir_p4_info, /*translate_port_ids=*/true, port_maps,
                          packetio_impl.get(), packet));
}

TEST(P4RuntimeImplTest, SendPacketOutDuplicateId) {
  p4::v1::PacketOut packet;
  // Create default and then modify to make duplcate metadata id.
  SetupPacketOutMetadata(/*egress_port*/ "1", /*egress_bitwidth*/ 9,
                         /*submit_to_ingress*/ 0,
                         /*ingress_bitwidth*/ 1, packet);
  for (auto iter = packet.mutable_metadata()->begin();
       iter != packet.mutable_metadata()->end(); iter++) {
    iter->set_metadata_id(PACKET_OUT_EGRESS_PORT_ID);
  }

  pdpi::IrP4Info ir_p4_info =
      sai::GetIrP4Info(sai::Instantiation::kMiddleblock);
  int fd[2];
  EXPECT_GE(pipe(fd), 0);
  std::vector<std::unique_ptr<p4rt_app::sonic::PacketIoPortSockets>>
      port_sockets;
  port_sockets.push_back(
      absl::make_unique<p4rt_app::sonic::PacketIoPortSockets>("Ethernet0",
                                                              fd[1]));

  auto mock_call_adapter = absl::make_unique<sonic::MockSystemCallAdapter>();
  auto packetio_impl = absl::make_unique<sonic::PacketIoImpl>(
      std::move(mock_call_adapter), std::move(port_sockets));
  boost::bimap<std::string, std::string> port_maps;
  ASSERT_THAT(SendPacketOut(ir_p4_info, /*translate_port_ids=*/true, port_maps,
                            packetio_impl.get(), packet),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(P4RuntimeImplTest, SendPacketOutIdMismatch) {
  p4::v1::PacketOut packet;
  // Make metadata id mismatch with what is in P4Info.
  SetupPacketOutMetadata(/*egress_port*/ "1", /*egress_bitwidth*/ 9,
                         /*submit_to_ingress*/ 0,
                         /*ingress_bitwidth*/ 1, packet);
  for (auto iter = packet.mutable_metadata()->begin();
       iter != packet.mutable_metadata()->end(); iter++) {
    auto prev_id = iter->metadata_id();
    iter->set_metadata_id(prev_id + 100);
  }

  pdpi::IrP4Info ir_p4_info =
      sai::GetIrP4Info(sai::Instantiation::kMiddleblock);
  int fd[2];
  EXPECT_GE(pipe(fd), 0);
  std::vector<std::unique_ptr<p4rt_app::sonic::PacketIoPortSockets>>
      port_sockets;
  port_sockets.push_back(
      absl::make_unique<p4rt_app::sonic::PacketIoPortSockets>("Ethernet0",
                                                              fd[1]));

  auto mock_call_adapter = absl::make_unique<sonic::MockSystemCallAdapter>();
  auto packetio_impl = absl::make_unique<sonic::PacketIoImpl>(
      std::move(mock_call_adapter), std::move(port_sockets));
  boost::bimap<std::string, std::string> port_maps;
  ASSERT_THAT(SendPacketOut(ir_p4_info, /*translate_port_ids=*/true, port_maps,
                            packetio_impl.get(), packet),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(P4RuntimeImplTest, SendPacketOutMultipleValidValues) {
  p4::v1::PacketOut packet;
  // Make multiple values valid.
  SetupPacketOutMetadata(/*egress_port*/ "1", /*egress_bitwidth*/ 9,
                         /*submit_to_ingress*/ 1,
                         /*ingress_bitwidth*/ 1, packet);

  pdpi::IrP4Info ir_p4_info =
      sai::GetIrP4Info(sai::Instantiation::kMiddleblock);
  int fd[2];
  EXPECT_GE(pipe(fd), 0);
  std::vector<std::unique_ptr<p4rt_app::sonic::PacketIoPortSockets>>
      port_sockets;
  port_sockets.push_back(
      absl::make_unique<p4rt_app::sonic::PacketIoPortSockets>("send_to_ingress",
                                                              fd[1]));

  auto mock_call_adapter = absl::make_unique<sonic::MockSystemCallAdapter>();
  struct ifreq if_resp { /*ifr_name=*/
    {""}, /*ifr_flags=*/{
      { IFF_UP | IFF_RUNNING }
    }
  };
  EXPECT_CALL(*mock_call_adapter, ioctl)
      .WillOnce(DoAll(SetArgPointee<2>(if_resp), Return(0)));
  EXPECT_CALL(*mock_call_adapter, write).Times(1);
  auto packetio_impl = absl::make_unique<sonic::PacketIoImpl>(
      std::move(mock_call_adapter), std::move(port_sockets));
  boost::bimap<std::string, std::string> port_maps;
  ASSERT_OK(SendPacketOut(ir_p4_info, /*translate_port_ids=*/true, port_maps,
                          packetio_impl.get(), packet));
}

TEST(P4RuntimeImplTest, SendPacketOutPortZero) {
  p4::v1::PacketOut packet;
  SetupPacketOutMetadata(/*egress_port*/ "0", /*egress_bitwidth*/ 9,
                         /*submit_to_ingress*/ 0,
                         /*ingress_bitwidth*/ 1, packet);

  pdpi::IrP4Info ir_p4_info =
      sai::GetIrP4Info(sai::Instantiation::kMiddleblock);
  int fd[2];
  EXPECT_GE(pipe(fd), 0);
  std::vector<std::unique_ptr<p4rt_app::sonic::PacketIoPortSockets>>
      port_sockets;
  port_sockets.push_back(
      absl::make_unique<p4rt_app::sonic::PacketIoPortSockets>("Ethernet0",
                                                              fd[1]));
  boost::bimap<std::string, std::string> port_maps;
  port_maps.insert({"Ethernet0", "0"});

  auto mock_call_adapter = absl::make_unique<sonic::MockSystemCallAdapter>();
  struct ifreq if_resp { /*ifr_name=*/
    {""}, /*ifr_flags=*/{
      { IFF_UP | IFF_RUNNING }
    }
  };
  EXPECT_CALL(*mock_call_adapter, ioctl)
      .WillOnce(DoAll(SetArgPointee<2>(if_resp), Return(0)));
  EXPECT_CALL(*mock_call_adapter, write).Times(1);
  auto packetio_impl = absl::make_unique<sonic::PacketIoImpl>(
      std::move(mock_call_adapter), std::move(port_sockets));
  ASSERT_OK(SendPacketOut(ir_p4_info, /*translate_port_ids=*/true, port_maps,
                          packetio_impl.get(), packet));
}

TEST(P4RuntimeImplTest, AddPacketInMetadataOk) {
  pdpi::IrP4Info ir_p4_info =
      sai::GetIrP4Info(sai::Instantiation::kMiddleblock);
  std::string ingress_port = "1";
  std::string target_port = "1";
  ASSERT_OK_AND_ASSIGN(auto actual_packet,
                       CreatePacketInMessage(ingress_port, target_port));
  p4::v1::PacketIn expected_packet;
  SetupPacketInMetadata(ingress_port, target_port, expected_packet);
  EXPECT_THAT(actual_packet, EqualsProto(expected_packet));
}

}  // namespace
}  // namespace p4rt_app
