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
#include "p4rt_app/sonic/packetio_impl.h"

#include "gutil/collections.h"

namespace p4rt_app {
namespace sonic {
namespace {

// Helper function to set socket map.
absl::flat_hash_map<std::string, int> CreateSocketMap(
    const std::vector<std::unique_ptr<sonic::PacketIoPortSockets>>&
        port_sockets) {
  absl::flat_hash_map<std::string, int> socket_map;
  // Populate the socket map.
  for (const auto& port : port_sockets) {
    socket_map[port->port_name] = port->port_socket;
  }
  return socket_map;
}

}  // namespace

PacketIoImpl::PacketIoImpl(
    std::unique_ptr<SystemCallAdapter> system_call_adapter,
    std::vector<std::unique_ptr<sonic::PacketIoPortSockets>> port_sockets)
    : system_call_adapter_(std::move(system_call_adapter)),
      port_sockets_(std::move(port_sockets)),
      socket_map_(CreateSocketMap(port_sockets_)) {}

absl::StatusOr<std::unique_ptr<PacketIoInterface>>
PacketIoImpl::CreatePacketIoImpl() {
  auto system_call_adapter = absl::make_unique<SystemCallAdapter>();
  auto port_sockets_or =
      p4rt_app::sonic::DiscoverPacketIoPorts(*system_call_adapter);
  if (!port_sockets_or.ok()) {
    return gutil::InternalErrorBuilder() << port_sockets_or.status();
  }
  auto packetio_impl = absl::make_unique<PacketIoImpl>(
      std::move(system_call_adapter), std::move(*port_sockets_or));
  return packetio_impl;
}

absl::Status PacketIoImpl::SendPacketOut(absl::string_view port_name,
                                         const std::string& packet) {
  // Retrieve the transmit socket for this egress port.
  ASSIGN_OR_RETURN(
      auto socket, gutil::FindOrStatus(socket_map_, std::string(port_name)),
      _ << "Unable to find transmit socket for destination: " << port_name);
  return sonic::SendPacketOut(*system_call_adapter_, socket, port_name, packet);
}

absl::StatusOr<std::thread> PacketIoImpl::StartReceive(
    packet_metadata::ReceiveCallbackFunction callback_function,
    bool use_genetlink) {
  LOG(INFO) << "Spawning Rx thread";
  if (use_genetlink) {
    return packet_metadata::StartReceive(callback_function);
  } else {
    return sonic::StartReceive(callback_function, socket_map_);
  }
}

}  // namespace sonic
}  // namespace p4rt_app
