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
#include "absl/strings/substitute.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "p4rt_app/sonic/adapters/db_connector_adapter.h"
#include "p4rt_app/sonic/adapters/system_call_adapter.h"

namespace p4rt_app {
namespace sonic {
constexpr absl::string_view kSubmitToIngress = "send_to_ingress";

namespace {

// Max buffer size for Receive packets.
static constexpr int kPacketIoPortMaxBufferSize = 1024;

// Prefix of valid receive interfaces.
static constexpr absl::string_view kValidReceivePrefixes[] = {"Ethernet"};

// Prefix of valid transmit interfaces.
static constexpr absl::string_view kValidTransmitPrefixes[] = {
    "Ethernet", kSubmitToIngress};

// Check if the given port starts with one of the valid prefixes.
template <typename T>
bool IsValidPort(absl::string_view port_name, const T &prefix_list) {
  for (const auto &prefix : prefix_list) {
    if (absl::StartsWith(port_name, prefix)) {
      return true;
    }
  }
  return false;
}

// A class derived from Selectable base class only to re-use the EPOLL wait
// mechanism. Operates on receive socket that was created for each netdev port
// and the virtual funcs will read the buffers when packet in arrives.
class PacketInSelectable : public swss::Selectable {
 public:
  PacketInSelectable(const std::string port_name, int receive_socket,
                     packet_metadata::ReceiveCallbackFunction callback_function)
      : port_name_(port_name),
        receive_socket_(receive_socket),
        callback_function_(callback_function) {}
  ~PacketInSelectable() override{};

  // Override functions.
  int getFd() override { return receive_socket_; }
  // Reads data from socket and invokes callback function to pass back the In
  // packet.
  uint64_t readData() override {
    ssize_t msg_len = 0;
    do {
      msg_len = read(receive_socket_, read_buffer_, kPacketIoPortMaxBufferSize);
    } while (errno == EINTR);
    if (msg_len < 0) {
      LOG(ERROR) << "Error " << errno << " in reading buffer from socket for "
                 << port_name_;
    } else if (msg_len == 0) {
      LOG(ERROR) << "Unexpected socket shutdown during read for " << port_name_;
    } else {
      std::string packet(read_buffer_, msg_len);
      // Just pass empty string for target egress port since this support is not
      // available in netdev model.
      auto status = callback_function_(port_name_, "", packet);
      if (!status.ok()) {
        LOG(WARNING) << "Unable to send packet to the controller"
                     << status.ToString();
      }
    }

    return 0;
  }

 private:
  PacketInSelectable(const PacketInSelectable &) = delete;
  PacketInSelectable &operator=(const PacketInSelectable &) = delete;

  // Sonic port name.
  std::string port_name_;

  // Receive socket.
  int receive_socket_;

  // Buffer to hold data read from socket.
  char read_buffer_[kPacketIoPortMaxBufferSize];

  // Callback function to be invoked.
  packet_metadata::ReceiveCallbackFunction callback_function_;
};

absl::Status CreateAndBindSockets(const SystemCallAdapter &system_call_adapter,
                                  const std::string &port_name,
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
  addr.sll_ifindex = system_call_adapter.if_nametoindex(port_name.c_str());
  RET_CHECK(addr.sll_ifindex != 0) << "Failed to get ifindex for " << port_name;

  RET_CHECK(system_call_adapter.bind(port_socket,
                                     reinterpret_cast<struct sockaddr *>(&addr),
                                     sizeof(addr)) >= 0)
      << "Failed to bind socket for " << port_name;
  LOG(INFO) << "Successfully bound socket for " << port_name;

  return absl::OkStatus();
}

// Receiver thread that adds each socket FD of netdev Linux port into
// swss::Selectable port and goes into EPOLL blocking wait state.
// readData virutal function of swss reads the buffer from socket and invokes
// the callback function for every packet in activity on each port.
static void ReceiveThread(
    packet_metadata::ReceiveCallbackFunction callback_function,
    const absl::flat_hash_map<std::string, int> &socket_map) {
  swss::Select port_select;
  std::vector<std::unique_ptr<PacketInSelectable>> selectables;

  for (const auto &port_params : socket_map) {
    // Pull out the tuple elements.
    std::string port_name;
    int receive_socket;
    std::tie(port_name, receive_socket) = port_params;
    // Check if this port is valid for Receive.
    if (!IsValidPort(port_name, kValidReceivePrefixes)) continue;

    std::unique_ptr<PacketInSelectable> in_selectable =
        absl::make_unique<PacketInSelectable>(port_name, receive_socket,
                                              callback_function);
    // Add the port object into the EPOLL via Select.addSelectable().
    port_select.addSelectable(in_selectable.get());
    // Move this to the receive thread scope so that it does not get freed after
    // the for loop.
    selectables.push_back(std::move(in_selectable));
  }

  LOG(INFO) << "Successfully created Receive thread";
  while (true) {
    swss::Selectable *sel;
    port_select.select(&sel);
  }
  // Never expected to be here.
}

// Create Receive, Transmit sockets for a particular port identified by its
// ifname.
absl::StatusOr<std::unique_ptr<PacketIoPortSockets>> CreatePacketIoSockets(
    const SystemCallAdapter &system_call_adapter,
    const std::string &port_name) {
  int port_socket;
  auto status =
      CreateAndBindSockets(system_call_adapter, port_name, port_socket);
  if (!status.ok()) {
    if (port_socket >= 0) system_call_adapter.close(port_socket);
    return gutil::InternalErrorBuilder() << status.ToString();
  }

  return absl::make_unique<PacketIoPortSockets>(port_name, port_socket);
}

}  // namespace

void WaitForPortInitDone(DBConnectorAdapter &app_db_client) {
  while (true) {
    auto port_init_map = app_db_client.hgetall("PORT_TABLE:PortInitDone");
    if (!port_init_map.empty()) {
      LOG(INFO) << "PortInitDone is set, P4RT init starts";
      break;
    }

    LOG_EVERY_N(WARNING, 120)
        << "Waiting for PortInitDone to be set before P4RT can start";
    absl::SleepFor(absl::Seconds(5));
  }
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

absl::StatusOr<std::vector<std::unique_ptr<sonic::PacketIoPortSockets>>>
DiscoverPacketIoPorts(const SystemCallAdapter &system_call_adapter) {
  std::vector<std::unique_ptr<sonic::PacketIoPortSockets>> port_sockets;
  struct ifaddrs *head, *intf;
  RET_CHECK(system_call_adapter.getifaddrs(&head) != -1)
      << "Failed to get interface list from system";

  // Form the valid set of interface prefixes to discover.
  std::set<absl::string_view> valid_prefixes;
  valid_prefixes.insert(std::begin(kValidReceivePrefixes),
                        std::end(kValidReceivePrefixes));
  valid_prefixes.insert(std::begin(kValidTransmitPrefixes),
                        std::end(kValidTransmitPrefixes));

  for (intf = head; intf != nullptr; intf = intf->ifa_next) {
    // Interfaces repeat for every address type - AF_INET, AF_INET6 &
    // AF_PACKET, so use just one family type for iterating.
    if (intf->ifa_addr == NULL || intf->ifa_addr->sa_family != AF_PACKET)
      continue;
    // Find if this interface starts with one of the valid prefixes.
    if (!IsValidPort(intf->ifa_name, valid_prefixes)) continue;

    const std::string port_name(intf->ifa_name);
    absl::StatusOr<std::unique_ptr<PacketIoPortSockets>> port_object =
        CreatePacketIoSockets(system_call_adapter, port_name);
    if (port_object.ok()) {
      port_sockets.push_back(std::move(port_object.value()));
    } else {
      LOG(INFO) << port_object.status();
    }
  }
  system_call_adapter.freeifaddrs(head);

  return port_sockets;
}

std::thread StartReceive(
    packet_metadata::ReceiveCallbackFunction callback_function,
    const absl::flat_hash_map<std::string, int> &socket_map) {
  // Create Receive thread to receive packets from the socket.
  return std::thread(ReceiveThread, callback_function, socket_map);
}

}  // namespace sonic
}  // namespace p4rt_app
