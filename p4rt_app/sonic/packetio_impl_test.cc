// Copyright 2021 Google LLC
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
#include "p4rt_app/sonic/packetio_impl.h"

#include <linux/if.h>
#include <netpacket/packet.h>
#include <unistd.h>

#include <string>
#include <utility>

#include "absl/cleanup/cleanup.h"
#include "absl/memory/memory.h"
#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "p4rt_app/sonic/adapters/mock_system_call_adapter.h"

namespace p4rt_app {
namespace sonic {
namespace {

using ::gutil::StatusIs;
using ::testing::_;
using ::testing::Eq;
using ::testing::Return;
using ::testing::StrEq;

absl::Status EmptyPacketInCallback(std::string source_port,
                                   std::string tartget_port,
                                   std::string payload) {
  return absl::OkStatus();
}

// PipeFd is a wrapper around a linux pipe. It will open the pipe on
// construction, and close it on destruction .
class PipeFd {
 public:
  PipeFd() {
    int err = pipe(fd_);
    LOG_IF(FATAL, err < 0) << "Failed to open linux pipe: " << err;
  }

  ~PipeFd() {
    close(fd_[0]);
    close(fd_[1]);
  }

  int ReadEnd() const { return fd_[0]; }
  int WriteEnd() const { return fd_[1]; }

 private:
  int fd_[2];
};

TEST(PacketIoImplTest, AddAndRemovePacketIoPortWithoutNetdevTranslation) {
  auto mock_call_adapter = absl::make_unique<sonic::MockSystemCallAdapter>();
  PipeFd fd;

  // Because we are not doing a netdev translation we expect the interface name
  // to match the packetio port.
  EXPECT_CALL(*mock_call_adapter, socket).WillOnce(Return(fd.WriteEnd()));
  EXPECT_CALL(*mock_call_adapter, setsockopt).WillOnce(Return(0));
  EXPECT_CALL(*mock_call_adapter, if_nametoindex(StrEq("Ethernet1/1")))
      .WillOnce(Return(1));
  EXPECT_CALL(*mock_call_adapter, bind).WillOnce(Return(0));
  EXPECT_CALL(*mock_call_adapter, close).WillOnce(Return(0));

  PacketIoImpl packetio_impl(std::move(mock_call_adapter),
                             PacketIoOptions{
                                 .callback_function = EmptyPacketInCallback,
                             });

  // After adding check that ports are valid for transmit and receive.
  ASSERT_OK(packetio_impl.AddPacketIoPort("Ethernet1/1"));
  EXPECT_TRUE(packetio_impl.IsValidPortForTransmit("Ethernet1/1"));
  EXPECT_TRUE(packetio_impl.IsValidPortForReceive("Ethernet1/1"));

  // After removing check that ports are not valid for transmit and receive.
  ASSERT_OK(packetio_impl.RemovePacketIoPort("Ethernet1/1"));
  EXPECT_FALSE(packetio_impl.IsValidPortForTransmit("Ethernet1/1"));
  EXPECT_FALSE(packetio_impl.IsValidPortForReceive("Ethernet1/1"));
}

TEST(PacketIoImplTest, AddAndRemoveSubmitToIngressPortWithNetdevTranslation) {
  constexpr absl::string_view kSubmitToIngress = "send_to_ingress";

  auto mock_call_adapter = absl::make_unique<sonic::MockSystemCallAdapter>();
  PipeFd fd;

  // We should be able to create the submit to ingress port even if the netdev
  // translation is enabled.
  EXPECT_CALL(*mock_call_adapter, socket).WillOnce(Return(fd.WriteEnd()));
  EXPECT_CALL(*mock_call_adapter, setsockopt).WillOnce(Return(0));
  EXPECT_CALL(*mock_call_adapter, if_nametoindex(StrEq("send_to_ingress")))
      .WillOnce(Return(1));
  EXPECT_CALL(*mock_call_adapter, bind).WillOnce(Return(0));
  EXPECT_CALL(*mock_call_adapter, close).WillOnce(Return(0));

  PacketIoImpl packetio_impl(std::move(mock_call_adapter),
                             PacketIoOptions{
                                 .callback_function = EmptyPacketInCallback,
                             });

  // After adding check that ports are valid for transmit and receive.
  ASSERT_OK(packetio_impl.AddPacketIoPort(kSubmitToIngress));
  EXPECT_TRUE(packetio_impl.IsValidPortForTransmit(kSubmitToIngress));
  EXPECT_TRUE(packetio_impl.IsValidPortForReceive(kSubmitToIngress));

  // After removing check that ports are not valid for transmit and receive.
  ASSERT_OK(packetio_impl.RemovePacketIoPort(kSubmitToIngress));
  EXPECT_FALSE(packetio_impl.IsValidPortForTransmit(kSubmitToIngress));
  EXPECT_FALSE(packetio_impl.IsValidPortForReceive(kSubmitToIngress));
}

TEST(PacketIoImplTest, AddingDuplicatePacketIoPortsIsANoop) {
  auto mock_call_adapter = absl::make_unique<sonic::MockSystemCallAdapter>();
  PipeFd fd;

  // Expect only one socket to be created because we are sending a duplicate
  // port name.
  EXPECT_CALL(*mock_call_adapter, socket).WillOnce(Return(fd.WriteEnd()));
  EXPECT_CALL(*mock_call_adapter, setsockopt).WillOnce(Return(0));
  EXPECT_CALL(*mock_call_adapter, if_nametoindex).WillOnce(Return(1));
  EXPECT_CALL(*mock_call_adapter, bind).WillOnce(Return(0));

  PacketIoImpl packetio_impl(std::move(mock_call_adapter),
                             PacketIoOptions{
                                 .callback_function = EmptyPacketInCallback,
                             });

  // Add the same PacketIO port twice.
  ASSERT_OK(packetio_impl.AddPacketIoPort("Ethernet1/1"));
  ASSERT_OK(packetio_impl.AddPacketIoPort("Ethernet1/1"));

  EXPECT_TRUE(packetio_impl.IsValidPortForTransmit("Ethernet1/1"));
  EXPECT_TRUE(packetio_impl.IsValidPortForReceive("Ethernet1/1"));
}

TEST(PacketIoImplTest, AddAndRemoveMultiplePacketIoPorts) {
  constexpr absl::string_view kSubmitToIngress = "send_to_ingress";

  auto mock_call_adapter = absl::make_unique<sonic::MockSystemCallAdapter>();

  // Open 2 different sockets. One for each PacketIO port.
  PipeFd fd0, fd1;
  EXPECT_CALL(*mock_call_adapter, socket)
      .WillOnce(Return(fd0.WriteEnd()))
      .WillOnce(Return(fd1.WriteEnd()));
  EXPECT_CALL(*mock_call_adapter, setsockopt)
      .WillOnce(Return(0))
      .WillOnce(Return(0));
  EXPECT_CALL(*mock_call_adapter, if_nametoindex)
      .WillOnce(Return(1))
      .WillOnce(Return(1));

  // Expect each port to bind (on add) & close (on remove) on the correct
  // socket.
  EXPECT_CALL(*mock_call_adapter, bind(fd0.WriteEnd(), _, _))
      .WillOnce(Return(0));
  EXPECT_CALL(*mock_call_adapter, close(Eq(fd0.WriteEnd()))).Times(1);

  EXPECT_CALL(*mock_call_adapter, bind(fd1.WriteEnd(), _, _))
      .WillOnce(Return(0));
  EXPECT_CALL(*mock_call_adapter, close(Eq(fd1.WriteEnd()))).Times(1);

  PacketIoImpl packetio_impl(std::move(mock_call_adapter),
                             PacketIoOptions{
                                 .callback_function = EmptyPacketInCallback,
                             });

  // Add an SDN port.
  ASSERT_OK(packetio_impl.AddPacketIoPort("Ethernet1/1"));
  EXPECT_TRUE(packetio_impl.IsValidPortForTransmit("Ethernet1/1"));
  EXPECT_TRUE(packetio_impl.IsValidPortForReceive("Ethernet1/1"));

  // Add the submit to ingress port.
  ASSERT_OK(packetio_impl.AddPacketIoPort(kSubmitToIngress));
  EXPECT_TRUE(packetio_impl.IsValidPortForTransmit(kSubmitToIngress));
  EXPECT_TRUE(packetio_impl.IsValidPortForReceive(kSubmitToIngress));

  // Remove the SDN port
  ASSERT_OK(packetio_impl.RemovePacketIoPort("Ethernet1/1"));
  EXPECT_FALSE(packetio_impl.IsValidPortForTransmit("Ethernet1/1"));
  EXPECT_FALSE(packetio_impl.IsValidPortForReceive("Ethernet1/1"));

  // Remove the submit to ingress port.
  ASSERT_OK(packetio_impl.RemovePacketIoPort(kSubmitToIngress));
  EXPECT_FALSE(packetio_impl.IsValidPortForTransmit(kSubmitToIngress));
  EXPECT_FALSE(packetio_impl.IsValidPortForReceive(kSubmitToIngress));
}

TEST(PacketIoImplTest, FailOnNonExistentRemovePacketIoPort) {
  auto mock_call_adapter = absl::make_unique<sonic::MockSystemCallAdapter>();

  EXPECT_CALL(*mock_call_adapter, close).Times(0);
  PacketIoImpl packetio_impl(std::move(mock_call_adapter),
                             PacketIoOptions{
                                 .callback_function = EmptyPacketInCallback,
                             });
  EXPECT_THAT(packetio_impl.RemovePacketIoPort("Ethernet1/1"),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(PacketIoImplTest, FailOnRemoveDuplicatePacketIoPort) {
  auto mock_call_adapter = absl::make_unique<sonic::MockSystemCallAdapter>();
  PipeFd fd;

  EXPECT_CALL(*mock_call_adapter, socket).WillOnce(Return(fd.WriteEnd()));
  EXPECT_CALL(*mock_call_adapter, setsockopt).WillOnce(Return(0));
  EXPECT_CALL(*mock_call_adapter, if_nametoindex).WillOnce(Return(1));
  EXPECT_CALL(*mock_call_adapter, bind).WillOnce(Return(0));
  EXPECT_CALL(*mock_call_adapter, close(Eq(fd.WriteEnd()))).Times(1);

  PacketIoImpl packetio_impl(std::move(mock_call_adapter),
                             PacketIoOptions{
                                 .callback_function = EmptyPacketInCallback,
                             });

  ASSERT_OK(packetio_impl.AddPacketIoPort("Ethernet1/1"));
  ASSERT_OK(packetio_impl.RemovePacketIoPort("Ethernet1/1"));
  EXPECT_THAT(packetio_impl.RemovePacketIoPort("Ethernet1/1"),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(PacketIoImplTest, AddAndRemovePacketIoPortWithGenetlink) {
  constexpr absl::string_view kSubmitToIngress = "send_to_ingress";

  auto mock_call_adapter = absl::make_unique<sonic::MockSystemCallAdapter>();
  PipeFd fd;

  EXPECT_CALL(*mock_call_adapter, socket)
      .Times(2)
      .WillRepeatedly(Return(fd.WriteEnd()));
  EXPECT_CALL(*mock_call_adapter, setsockopt)
      .Times(2)
      .WillRepeatedly(Return(0));
  EXPECT_CALL(*mock_call_adapter, if_nametoindex)
      .Times(2)
      .WillRepeatedly(Return(1));
  EXPECT_CALL(*mock_call_adapter, bind).Times(2).WillRepeatedly(Return(0));
  EXPECT_CALL(*mock_call_adapter, close).Times(2).WillRepeatedly(Return(0));

  PacketIoImpl packetio_impl(std::move(mock_call_adapter),
                             PacketIoOptions{
                                 .callback_function = EmptyPacketInCallback,
                                 .use_genetlink = true,
                             });

  // Add SDN port.
  ASSERT_OK(packetio_impl.AddPacketIoPort("Ethernet1/1"));
  EXPECT_TRUE(packetio_impl.IsValidPortForTransmit("Ethernet1/1"));

  // Add submit to ingress port.
  ASSERT_OK(packetio_impl.AddPacketIoPort(kSubmitToIngress));
  EXPECT_TRUE(packetio_impl.IsValidPortForTransmit(kSubmitToIngress));

  // Remove SDN port.
  ASSERT_OK(packetio_impl.RemovePacketIoPort("Ethernet1/1"));
  EXPECT_FALSE(packetio_impl.IsValidPortForTransmit("Ethernet1/1"));

  // Remove submit to ingress port.
  ASSERT_OK(packetio_impl.RemovePacketIoPort(kSubmitToIngress));
  EXPECT_FALSE(packetio_impl.IsValidPortForTransmit(kSubmitToIngress));
}

}  // namespace
}  // namespace sonic
}  // namespace p4rt_app
