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
#ifndef GOOGLE_P4RT_APP_SONIC_PACKETIO_PORT_H_
#define GOOGLE_P4RT_APP_SONIC_PACKETIO_PORT_H_

#include <memory>
#include <string>

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "glog/logging.h"
#include "p4_pdpi/utils/ir.h"
#include "p4rt_app/sonic/adapters/system_call_adapter.h"
#include "p4rt_app/sonic/receive_genetlink.h"
#include "swss/dbconnectorinterface.h"
#include "swss/select.h"
#include "swss/selectable.h"

namespace p4rt_app {

namespace sonic {

// Prefix for submit to ingress.
ABSL_CONST_INIT extern const absl::string_view kSubmitToIngress;

// A structure to hold port name, receive and transmit socket for a particular
// netdev port.
struct PacketIoPortSockets {
  PacketIoPortSockets(const std::string port_name, int port_socket)
      : port_name(port_name), port_socket(port_socket) {}
  ~PacketIoPortSockets() {
    if (port_socket >= 0) {
      close(port_socket);
    }
  }
  std::string port_name;
  int port_socket;
};

// Blocking wait until port init is done.
void WaitForPortInitDone(swss::DBConnectorInterface& app_db_client);

// Discover all netdev ports in Linux that corresponds to each physical port on
// the switch. CPU punted/generated packets originate/egress on a physical port
// map to the netdev port. Returns a vector of the PacketIoPortSockets for all
// the netdev ports in the system.
absl::StatusOr<std::vector<std::unique_ptr<sonic::PacketIoPortSockets>>>
DiscoverPacketIoPorts(const SystemCallAdapter& system_call_adapter);

// Spawns the Receive thread for all the receive sockets passed in, this will
// enable all punted packets to be received via the socket interface.
// Invokes the callback function with the corresponding port on which the packet
// arrived.
// receive_sockets is an input vector of <port_name, receive_socket>.
ABSL_MUST_USE_RESULT std::thread StartReceive(
    packet_metadata::ReceiveCallbackFunction callback_function,
    const absl::flat_hash_map<std::string, int>& socket_map);

// Send a packet out on the specified egress socket.
absl::Status SendPacketOut(const SystemCallAdapter& system_call_adapter,
                           int transmit_socket,
                           absl::string_view interface_name,
                           const std::string& packet);

}  // namespace sonic
}  // namespace p4rt_app

#endif  // GOOGLE_P4RT_APP_SONIC_PACKETIO_PORT_H_
