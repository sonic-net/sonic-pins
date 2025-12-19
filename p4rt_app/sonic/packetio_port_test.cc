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
#include "p4rt_app/sonic/packetio_port.h"

#include <cstddef>
#include <memory>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "p4rt_app/sonic/adapters/mock_system_call_adapter.h"

namespace p4rt_app {
namespace sonic {
namespace {

// Test packet used for Receive/Transmit.
static constexpr char kTestPacket[] =
    "\x03\x32\x00\x00\x00\x01\x00\x00\x00\x00\x00\x01\x81\x00\x00\x01\x08\x00"
    "\x45\x00\x00\x2d\x00\x01\x00\x00\x40\xfe\x62\xd1\x0a\x00\x01\x01\x0a\x00"
    "\x02\x01\x54\x65\x73\x74\x2c\x20\x54\x65\x73\x74\x2c\x20\x54\x65\x73\x74"
    "\x2c\x20\x54\x65\x73\x74\x21\x21\x21";

static constexpr char kEthernet0[] = "Ethernet0";
// Pipe fd receive/transmit descriptors.
static constexpr int kTransmit = 1;
// Valid/invalid minimum return value for socket/bind calls.
static constexpr int kSocketCallsValidValue = 0;
static constexpr int kSocketCallsInvalidValue = -1;
// Valid/invalid minimum return value for ifIndex.
static constexpr int kifIndexValidValue = 1;
static constexpr int kifIndexInvalidValue = 0;

using ::gutil::StatusIs;
using ::testing::_;
using ::testing::DoAll;
using ::testing::HasSubstr;
using ::testing::Return;
using ::testing::SetArgPointee;
using ::testing::Test;

TEST(PacketIoTest, SendPacketOutOk) {
  MockSystemCallAdapter mock_call_adapter;
  struct ifreq if_resp{/*ifr_name=*/
                       {""},
                       /*ifr_flags=*/{{IFF_UP | IFF_RUNNING}}};
  EXPECT_CALL(mock_call_adapter, ioctl)
      .WillOnce(DoAll(SetArgPointee<2>(if_resp), Return(0)));
  EXPECT_CALL(mock_call_adapter, write).WillOnce(Return(sizeof(kTestPacket)));

  int fd[2];
  EXPECT_GE(pipe(fd), 0);
  EXPECT_OK(SendPacketOut(mock_call_adapter, fd[kTransmit], kEthernet0,
                          std::string(kTestPacket, sizeof(kTestPacket))));
}

TEST(PacketIoTest, SendPacketOutIoctlError) {
  MockSystemCallAdapter mock_call_adapter;
  EXPECT_CALL(mock_call_adapter, ioctl).WillOnce(Return(-1));

  int fd[2];
  EXPECT_GE(pipe(fd), 0);
  EXPECT_THAT(SendPacketOut(mock_call_adapter, fd[kTransmit], kEthernet0,
                            std::string(kTestPacket, sizeof(kTestPacket))),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr("Ioctl for get interface flags failed")));
}

TEST(PacketIoTest, SendPacketOutLinkDown) {
  MockSystemCallAdapter mock_call_adapter;
  struct ifreq if_resp{/*ifr_name=*/
                       {""},
                       /*ifr_flags=*/{{IFF_UP}}};
  EXPECT_CALL(mock_call_adapter, ioctl)
      .WillOnce(DoAll(SetArgPointee<2>(if_resp), Return(0)));

  int fd[2];
  EXPECT_GE(pipe(fd), 0);
  EXPECT_THAT(SendPacketOut(mock_call_adapter, fd[kTransmit], kEthernet0,
                            std::string(kTestPacket, sizeof(kTestPacket))),
              StatusIs(absl::StatusCode::kInternal, HasSubstr("Link not up")));
}

TEST(PacketIoTest, SendPacketOutWriteError) {
  MockSystemCallAdapter mock_call_adapter;
  struct ifreq if_resp{/*ifr_name=*/
                       {""},
                       /*ifr_flags=*/{{IFF_UP | IFF_RUNNING}}};
  EXPECT_CALL(mock_call_adapter, ioctl)
      .WillOnce(DoAll(SetArgPointee<2>(if_resp), Return(0)));
  EXPECT_CALL(mock_call_adapter, write).WillOnce(Return(-1));

  int fd[2];
  EXPECT_GE(pipe(fd), 0);
  EXPECT_THAT(SendPacketOut(mock_call_adapter, fd[kTransmit], kEthernet0,
                            std::string(kTestPacket, sizeof(kTestPacket))),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr("Failed to send packet")));
}

TEST(PacketIoTest, SendPacketOutFailsOnGetSockOptError) {
  MockSystemCallAdapter mock_call_adapter;
  struct ifreq if_resp{/*ifr_name=*/
                       {""},
                       /*ifr_flags=*/{{IFF_UP | IFF_RUNNING}}};
  EXPECT_CALL(mock_call_adapter, ioctl)
      .WillOnce(DoAll(SetArgPointee<2>(if_resp), Return(0)));
  EXPECT_CALL(mock_call_adapter, getsockopt).WillOnce(Return(-1));

  int fd[2];
  EXPECT_GE(pipe(fd), 0);
  EXPECT_THAT(SendPacketOut(mock_call_adapter, fd[kTransmit], kEthernet0,
                            std::string(kTestPacket, sizeof(kTestPacket))),
              StatusIs(absl::StatusCode::kInternal,
                       HasSubstr("Unable to read socket pending error")));
}

TEST(PacketIoTest, SendPacketOutOkWithClearPendingError) {
  MockSystemCallAdapter mock_call_adapter;
  struct ifreq if_resp{/*ifr_name=*/
                       {""},
                       /*ifr_flags=*/{{IFF_UP | IFF_RUNNING}}};
  EXPECT_CALL(mock_call_adapter, ioctl)
      .WillOnce(DoAll(SetArgPointee<2>(if_resp), Return(0)));
  int optval = 100;
  // void *val = &optval;
  EXPECT_CALL(mock_call_adapter, getsockopt(_, _, SO_ERROR, _, _))
      .WillOnce(DoAll(SetArgPointee<3>(optval), Return(0)));
  EXPECT_CALL(mock_call_adapter, write).WillOnce(Return(sizeof(kTestPacket)));

  int fd[2];
  EXPECT_GE(pipe(fd), 0);
  EXPECT_OK(SendPacketOut(mock_call_adapter, fd[kTransmit], kEthernet0,
                          std::string(kTestPacket, sizeof(kTestPacket))));
}

TEST(PacketIoTest, SendPacketOutSplitWrite) {
  MockSystemCallAdapter mock_call_adapter;
  struct ifreq if_resp{/*ifr_name=*/
                       {""},
                       /*ifr_flags=*/{{IFF_UP | IFF_RUNNING}}};
  EXPECT_CALL(mock_call_adapter, ioctl)
      .WillOnce(DoAll(SetArgPointee<2>(if_resp), Return(0)));
  EXPECT_CALL(mock_call_adapter, write)
      .Times(2)
      .WillOnce(Return(/*random lenth=*/10))
      .WillOnce(Return(sizeof(kTestPacket) - 10));

  int fd[2];
  EXPECT_GE(pipe(fd), 0);
  EXPECT_OK(SendPacketOut(mock_call_adapter, fd[kTransmit], kEthernet0,
                          std::string(kTestPacket, sizeof(kTestPacket))));
}

TEST(PacketIoTest, AddPacketIoPortOK) {
  // Prepare mocks for CreateAndBindSocket.
  MockSystemCallAdapter mock_call_adapter;
  EXPECT_CALL(mock_call_adapter, socket)
      .Times(1)
      .WillOnce(Return(kSocketCallsValidValue));

  EXPECT_CALL(mock_call_adapter, setsockopt)
      .Times(1)
      .WillOnce(Return(kSocketCallsValidValue));
  EXPECT_CALL(mock_call_adapter, if_nametoindex)
      .Times(1)
      .WillOnce(Return(kifIndexValidValue));
  EXPECT_CALL(mock_call_adapter, bind)
      .Times(1)
      .WillOnce(Return(kSocketCallsValidValue));

  ASSERT_OK_AND_ASSIGN(auto port_params,
                       AddPacketIoPort(mock_call_adapter, kEthernet0,
                                       /*callback_function=*/nullptr));
  EXPECT_GE(port_params->socket, 0);
  EXPECT_NE(port_params->packet_in_selectable, nullptr);
}

TEST(PacketIoTest, CreateAndBindSocketFail) {
  MockSystemCallAdapter mock_call_adapter;
  // Set expectations for the CreateAndBindSockets.
  EXPECT_CALL(mock_call_adapter, socket)
      .Times(1)
      .WillOnce(Return(kSocketCallsInvalidValue));  // error in socket call.

  EXPECT_THAT(AddPacketIoPort(mock_call_adapter, kEthernet0,
                              /*callbacl_function=*/nullptr),
              StatusIs(absl::StatusCode::kInternal));
}

TEST(PacketIoTest, CreateAndBindSetSockOptFail) {
  MockSystemCallAdapter mock_call_adapter;
  // Set expectations for the CreateAndBindSockets.
  EXPECT_CALL(mock_call_adapter, socket)
      .Times(1)
      .WillOnce(Return(kSocketCallsValidValue));
  EXPECT_CALL(mock_call_adapter, setsockopt)
      .Times(1)
      .WillOnce(Return(kSocketCallsInvalidValue));  // error in setsockopt call.
  EXPECT_CALL(mock_call_adapter, close).Times(1);

  EXPECT_THAT(AddPacketIoPort(mock_call_adapter, kEthernet0,
                              /*callback_function=*/nullptr),
              StatusIs(absl::StatusCode::kInternal));
}

TEST(PacketIoTest, CreateAndBindifIndexFail) {
  // Set expectations for the CreateAndBindSockets.
  MockSystemCallAdapter mock_call_adapter;
  EXPECT_CALL(mock_call_adapter, socket)
      .Times(1)
      .WillOnce(Return(kSocketCallsValidValue));
  EXPECT_CALL(mock_call_adapter, setsockopt)
      .Times(1)
      .WillOnce(Return(kSocketCallsValidValue));
  EXPECT_CALL(mock_call_adapter, if_nametoindex)
      .Times(1)
      .WillOnce(Return(kifIndexInvalidValue));  // error in ifindex value.
  EXPECT_CALL(mock_call_adapter, close).Times(1);

  EXPECT_THAT(AddPacketIoPort(mock_call_adapter, kEthernet0,
                              /*callback_function=*/nullptr),
              StatusIs(absl::StatusCode::kInternal));
}

TEST(PacketIoTest, CreateAndBindFail) {
  MockSystemCallAdapter mock_call_adapter;
  // Set expectations for the CreateAndBindSockets.
  EXPECT_CALL(mock_call_adapter, socket)
      .Times(1)
      .WillOnce(Return(kSocketCallsValidValue));
  EXPECT_CALL(mock_call_adapter, setsockopt)
      .Times(1)
      .WillOnce(Return(kSocketCallsValidValue));
  EXPECT_CALL(mock_call_adapter, if_nametoindex)
      .Times(1)
      .WillOnce(Return(kifIndexValidValue));
  EXPECT_CALL(mock_call_adapter, bind)
      .Times(1)
      .WillOnce(Return(kSocketCallsInvalidValue));  // error in bind call.
  EXPECT_CALL(mock_call_adapter, close).Times(1);

  EXPECT_THAT(AddPacketIoPort(mock_call_adapter, kEthernet0,
                              /*callback_function=*/nullptr),
              StatusIs(absl::StatusCode::kInternal));
}

}  // namespace
}  // namespace sonic
}  // namespace p4rt_app
