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

#include <arpa/inet.h>
#include <linux/filter.h>
#include <net/ethernet.h>
#include <netpacket/packet.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <unistd.h>

#include <iomanip>
#include <iostream>
#include <memory>
#include <sstream>
#include <string>
#include <vector>

#include "absl/memory/memory.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "p4rt_app/sonic/adapters/system_call_adapter.h"

namespace p4rt_app {
namespace sonic {
constexpr absl::string_view kSubmitToIngress = "send_to_ingress";

namespace {

absl::Status CreateAndBindSockets(const SystemCallAdapter &system_call_adapter,
                                  absl::string_view port_name,
                                  int &port_socket) {
  port_socket =
      system_call_adapter.socket(AF_PACKET, SOCK_RAW, htons(ETH_P_ALL));
  RET_CHECK(port_socket != -1)
      << "Failed to create socket for " << port_name << " errno: " << errno;

  // Attach socket filters to drop LACP & LLDP packets.
  // The below is obtained directly from tcpdump using,
  // tcpdump not ether proto 0x8809 and not ether dst 33:33:00:00:00:16 -dd
  const struct sock_filter socket_filters[] = {
      // 1. Load packet ethertype.
      {0x28, 0, 0, 0x0000000c},
      // 2. If ethertype == 0x8809, skip 4 instr (goto 4), else goto 3.
      {0x15, 4, 0, 0x00008809},
      // 3. Check for destination mac address.
      {0x20, 0, 0, 0x00000002},
      {0x15, 0, 3, 0x00000016},
      {0x28, 0, 0, 0x00000000},
      {0x15, 0, 1, 0x00003333},
      // 4. Drop the packet.
      {0x6, 0, 0, 0x00000000},
      // 5. Allow the packet.
      {0x6, 0, 0, 0x00040000},
  };
  const struct sock_fprog not_lacp_lldp_program = {
      sizeof(socket_filters) / sizeof(socket_filters[0]),
      const_cast<struct sock_filter *>(socket_filters),
  };
  RET_CHECK(system_call_adapter.setsockopt(
                port_socket, SOL_SOCKET, SO_ATTACH_FILTER,
                &not_lacp_lldp_program, sizeof(not_lacp_lldp_program)) >= 0)
      << "Failed to apply socket filters for " << port_name;

  struct sockaddr_ll addr;
  memset(&addr, 0, sizeof(struct sockaddr_ll));
  addr.sll_family = AF_PACKET;
  addr.sll_protocol = htons(ETH_P_ALL);
  addr.sll_ifindex =
      system_call_adapter.if_nametoindex(std::string(port_name).c_str());
  RET_CHECK(addr.sll_ifindex != 0) << "Failed to get ifindex for " << port_name;

  RET_CHECK(system_call_adapter.bind(port_socket,
                                     reinterpret_cast<struct sockaddr *>(&addr),
                                     sizeof(addr)) >= 0)
      << "Failed to bind socket for " << port_name;
  LOG(INFO) << "Successfully bound socket for " << port_name;

  return absl::OkStatus();
}

// Create Receive, Transmit sockets for a particular port identified by its
// ifname.
absl::StatusOr<int> CreatePacketIoSocket(
    const SystemCallAdapter &system_call_adapter, absl::string_view port_name) {
  int port_socket = -1;
  auto status =
      CreateAndBindSockets(system_call_adapter, port_name, port_socket);
  if (!status.ok()) {
    if (port_socket >= 0) system_call_adapter.close(port_socket);
    return gutil::InternalErrorBuilder() << status.ToString();
  }

  return port_socket;
}

}  // namespace

absl::StatusOr<std::unique_ptr<PacketIoPortParams>> AddPacketIoPort(
    const SystemCallAdapter &system_call_adapter, absl::string_view port_name,
    packet_metadata::ReceiveCallbackFunction callback_function) {
  ASSIGN_OR_RETURN(int port_socket,
                   CreatePacketIoSocket(system_call_adapter, port_name));
  auto in_selectable = absl::make_unique<PacketInSelectable>(
      port_name, port_socket, callback_function);

  return absl::make_unique<PacketIoPortParams>(PacketIoPortParams{
      .socket = port_socket,
      .packet_in_selectable = std::move(in_selectable),
  });
}

absl::Status SendPacketOut(const SystemCallAdapter &system_call_adapter,
                           int transmit_socket,
                           absl::string_view interface_name,
                           const std::string &packet) {
  int msg_len = packet.length();
  const char *ptr = packet.data();

  struct ifreq if_req;
  memset(&if_req, 0, sizeof(if_req));
  strncpy(if_req.ifr_name, std::string(interface_name).c_str(),
          sizeof(if_req.ifr_name));
  int result =
      system_call_adapter.ioctl(transmit_socket, SIOCGIFFLAGS, &if_req);
  RET_CHECK(result != -1) << "Ioctl for get interface flags failed, interface: "
                          << interface_name << " errno: " << errno;
  // IFF_UP is admin status & IFF_RUNNING is operational status.
  bool link_up =
      (if_req.ifr_flags & IFF_UP) && (if_req.ifr_flags & IFF_RUNNING);
  RET_CHECK(link_up == true) << "Link not up for interface: " << interface_name;

  // Read and clear any pending error before the write call on the socket.
  int optval = 0;
  socklen_t optlen = sizeof(optval);
  if (system_call_adapter.getsockopt(transmit_socket, SOL_SOCKET, SO_ERROR,
                                     &optval, &optlen) < 0) {
    return gutil::InternalErrorBuilder()
           << "Unable to read socket pending error code for " << interface_name
           << ", errno " << errno;
  }
  if (optval != 0) {
    LOG(WARNING) << "getsockopt for " << interface_name
                 << " returned pending errno " << optval;
  }

  do {
    int res = system_call_adapter.write(transmit_socket, ptr, msg_len);
    if (res < 0) {
      if (errno == EINTR) {
        // interrupted before transmit could start, retry
      } else {
        return gutil::InternalErrorBuilder()
               << "Failed to send packet out of " << interface_name
               << ", errno " << errno;
      }
    } else {
      msg_len -= res;
      ptr += res;
    }
  } while (msg_len > 0);
  return absl::OkStatus();
}

}  // namespace sonic
}  // namespace p4rt_app
