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
#include "p4rt_app/p4runtime/packetio_helpers.h"

#include <memory>
#include <utility>

#include "absl/strings/string_view.h"
#include "boost/bimap.hpp"
#include "gmock/gmock.h"
#include "google/protobuf/text_format.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"
#include "p4_infra/p4_pdpi/utils/ir.h"
#include "p4rt_app/p4runtime/p4info_verification.h"
#include "p4rt_app/sonic/adapters/mock_system_call_adapter.h"
#include "p4rt_app/sonic/packetio_impl.h"
#include "p4rt_app/sonic/packetio_port.h"
#include "sai_p4/fixed/ids.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "swss/schema.h"

namespace p4rt_app {
namespace {

using ::gutil::EqualsProto;
using ::gutil::StatusIs;
using ::testing::_;
using ::testing::DoAll;
using ::testing::Return;
using ::testing::SetArgPointee;

constexpr absl::string_view kSubmitToIngress = SEND_TO_INGRESS_PORT_NAME;

MATCHER_P(IfrNameEq, name, "") {
  if (arg != nullptr) {
    *result_listener << "(ifr_name: " << arg->ifr_name << ")";
  }
  return arg != nullptr && strcmp(arg->ifr_name, name) == 0;
}

// Use in place of argument literal to make the test's intent clearer.
constexpr bool kTranslatePortId = true;

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

class PacketIoHelpersTest : public testing::Test {
 protected:
  PacketIoHelpersTest() {
    auto mock_call_adapter = std::make_unique<sonic::MockSystemCallAdapter>();
    mock_call_adapter_ = mock_call_adapter.get();

    packetio_impl_ = std::make_unique<sonic::PacketIoImpl>(
        std::move(mock_call_adapter), sonic::PacketIoOptions{});
  }

  pdpi::IrP4Info ir_p4_info_ =
      sai::GetIrP4Info(sai::Instantiation::kMiddleblock);

  // Owneship gets transfered to the packetio_impl_ object.
  sonic::MockSystemCallAdapter* mock_call_adapter_;

  std::unique_ptr<sonic::PacketIoImpl> packetio_impl_;
};

TEST_F(PacketIoHelpersTest, SendPacketOutEgressPortUsingPortIdOk) {
  p4::v1::PacketOut packet;
  SetupPacketOutMetadata(/*egress_port*/ "1", /*egress_bitwidth*/ 9,
                         /*submit_to_ingress*/ 0,
                         /*ingress_bitwidth*/ 1, packet);

  int fd[2];
  EXPECT_GE(pipe(fd), 0);

  struct ifreq if_resp {
    /*ifr_name=*/{""},
    /*ifr_flags=*/{
      { IFF_UP | IFF_RUNNING }
    }
  };
  EXPECT_CALL(*mock_call_adapter_, ioctl(_, _, IfrNameEq("Ethernet1/2")))
      .WillOnce(DoAll(SetArgPointee<2>(if_resp), Return(0)));
  EXPECT_CALL(*mock_call_adapter_, write).Times(1);
  EXPECT_CALL(*mock_call_adapter_, socket).WillOnce(Return(fd[1]));
  EXPECT_CALL(*mock_call_adapter_, if_nametoindex).WillOnce(Return(1));

  boost::bimap<std::string, std::string> port_maps;
  port_maps.insert({"Ethernet1/2", "1"});
  ASSERT_OK(packetio_impl_->AddPacketIoPort("Ethernet1/2"));
  EXPECT_OK(SendPacketOut(ir_p4_info_, kTranslatePortId, port_maps,
                          packetio_impl_.get(), packet));
}

TEST_F(PacketIoHelpersTest, SendPacketOutEgressPortUsingPortNameOk) {
  p4::v1::PacketOut packet;
  SetupPacketOutMetadata(/*egress_port*/ "Ethernet1/2", /*egress_bitwidth*/ 9,
                         /*submit_to_ingress*/ 0,
                         /*ingress_bitwidth*/ 1, packet);
  int fd[2];
  EXPECT_GE(pipe(fd), 0);

  struct ifreq if_resp {
    /*ifr_name=*/{""},
    /*ifr_flags=*/{
      { IFF_UP | IFF_RUNNING }
    }
  };
  EXPECT_CALL(*mock_call_adapter_, ioctl(_, _, IfrNameEq("Ethernet1/2")))
      .WillOnce(DoAll(SetArgPointee<2>(if_resp), Return(0)));
  EXPECT_CALL(*mock_call_adapter_, write).Times(1);
  EXPECT_CALL(*mock_call_adapter_, socket).WillOnce(Return(fd[1]));
  EXPECT_CALL(*mock_call_adapter_, if_nametoindex).WillOnce(Return(1));

  boost::bimap<std::string, std::string> port_maps;
  port_maps.insert({"Ethernet1/2", "1"});
  ASSERT_OK(packetio_impl_->AddPacketIoPort("Ethernet1/2"));
  EXPECT_OK(SendPacketOut(ir_p4_info_, !kTranslatePortId, port_maps,
                          packetio_impl_.get(), packet));
}

TEST_F(PacketIoHelpersTest, SendPacketOutIngressInjectOk) {
  p4::v1::PacketOut packet;
  SetupPacketOutMetadata(/*egress_port*/ "0", /*egress_bitwidth*/ 9,
                         /*submit_to_ingress*/ 1,
                         /*ingress_bitwidth*/ 1, packet);

  int fd[2];
  EXPECT_GE(pipe(fd), 0);

  struct ifreq if_resp {
    /*ifr_name=*/{""},
    /*ifr_flags=*/{
      { IFF_UP | IFF_RUNNING }
    }
  };
  EXPECT_CALL(*mock_call_adapter_, ioctl)
      .WillOnce(DoAll(SetArgPointee<2>(if_resp), Return(0)));
  EXPECT_CALL(*mock_call_adapter_, write).Times(1);
  EXPECT_CALL(*mock_call_adapter_, socket).WillOnce(Return(fd[1]));
  EXPECT_CALL(*mock_call_adapter_, if_nametoindex).WillOnce(Return(1));

  boost::bimap<std::string, std::string> port_maps;
  ASSERT_OK(packetio_impl_->AddPacketIoPort(kSubmitToIngress));
  EXPECT_OK(SendPacketOut(ir_p4_info_, kTranslatePortId, port_maps,
                          packetio_impl_.get(), packet));
}

TEST_F(PacketIoHelpersTest, SendPacketOutDuplicateId) {
  // Create default and then modify to make duplcate metadata id.
  p4::v1::PacketOut packet;
  SetupPacketOutMetadata(/*egress_port*/ "1", /*egress_bitwidth*/ 9,
                         /*submit_to_ingress*/ 0,
                         /*ingress_bitwidth*/ 1, packet);
  for (auto iter = packet.mutable_metadata()->begin();
       iter != packet.mutable_metadata()->end(); iter++) {
    iter->set_metadata_id(PACKET_OUT_EGRESS_PORT_ID);
  }

  boost::bimap<std::string, std::string> port_maps;
  ASSERT_THAT(SendPacketOut(ir_p4_info_, kTranslatePortId, port_maps,
                            packetio_impl_.get(), packet),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(PacketIoHelpersTest, SendPacketOutIdMismatch) {
  // Make metadata id mismatch with what is in P4Info.
  p4::v1::PacketOut packet;
  SetupPacketOutMetadata(/*egress_port*/ "1", /*egress_bitwidth*/ 9,
                         /*submit_to_ingress*/ 0,
                         /*ingress_bitwidth*/ 1, packet);
  for (auto iter = packet.mutable_metadata()->begin();
       iter != packet.mutable_metadata()->end(); iter++) {
    auto prev_id = iter->metadata_id();
    iter->set_metadata_id(prev_id + 100);
  }

  boost::bimap<std::string, std::string> port_maps;
  ASSERT_THAT(SendPacketOut(ir_p4_info_, kTranslatePortId, port_maps,
                            packetio_impl_.get(), packet),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(PacketIoHelpersTest, SendPacketOutMultipleValidValues) {
  // Make multiple values valid.
  p4::v1::PacketOut packet;
  SetupPacketOutMetadata(/*egress_port*/ "1", /*egress_bitwidth*/ 9,
                         /*submit_to_ingress*/ 1,
                         /*ingress_bitwidth*/ 1, packet);

  int fd[2];
  EXPECT_GE(pipe(fd), 0);

  struct ifreq if_resp {
    /*ifr_name=*/{""},
    /*ifr_flags=*/{
      { IFF_UP | IFF_RUNNING }
    }
  };
  EXPECT_CALL(*mock_call_adapter_, ioctl)
      .WillOnce(DoAll(SetArgPointee<2>(if_resp), Return(0)));
  EXPECT_CALL(*mock_call_adapter_, write).Times(1);
  EXPECT_CALL(*mock_call_adapter_, socket).WillOnce(Return(fd[1]));
  EXPECT_CALL(*mock_call_adapter_, if_nametoindex).WillOnce(Return(1));

  boost::bimap<std::string, std::string> port_maps;
  ASSERT_OK(packetio_impl_->AddPacketIoPort(kSubmitToIngress));
  ASSERT_OK(SendPacketOut(ir_p4_info_, kTranslatePortId, port_maps,
                          packetio_impl_.get(), packet));
}

TEST_F(PacketIoHelpersTest, SendPacketOutPortZero) {
  p4::v1::PacketOut packet;
  SetupPacketOutMetadata(/*egress_port*/ "0", /*egress_bitwidth*/ 9,
                         /*submit_to_ingress*/ 0,
                         /*ingress_bitwidth*/ 1, packet);

  int fd[2];
  EXPECT_GE(pipe(fd), 0);

  struct ifreq if_resp {
    /*ifr_name=*/{""},
    /*ifr_flags=*/{
      { IFF_UP | IFF_RUNNING }
    }
  };
  EXPECT_CALL(*mock_call_adapter_, ioctl(_, _, IfrNameEq("Ethernet1/1")))
      .WillOnce(DoAll(SetArgPointee<2>(if_resp), Return(0)));
  EXPECT_CALL(*mock_call_adapter_, write).Times(1);
  EXPECT_CALL(*mock_call_adapter_, socket).WillOnce(Return(fd[1]));
  EXPECT_CALL(*mock_call_adapter_, if_nametoindex).WillOnce(Return(1));

  boost::bimap<std::string, std::string> port_maps;
  port_maps.insert({"Ethernet1/1", "0"});
  ASSERT_OK(packetio_impl_->AddPacketIoPort("Ethernet1/1"));
  ASSERT_OK(SendPacketOut(ir_p4_info_, kTranslatePortId, port_maps,
                          packetio_impl_.get(), packet));
}

TEST_F(PacketIoHelpersTest, AddPacketInMetadataOk) {
  std::string ingress_port = "1";
  std::string target_port = "1";
  auto actual_packet = CreatePacketInMessage(ingress_port, target_port);
  p4::v1::PacketIn expected_packet;
  SetupPacketInMetadata(ingress_port, target_port, expected_packet);
  EXPECT_THAT(actual_packet, EqualsProto(expected_packet));
}

}  // namespace
}  // namespace p4rt_app
