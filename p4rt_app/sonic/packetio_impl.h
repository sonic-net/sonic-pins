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
#ifndef PINS_P4RT_APP_SONIC_PACKETIO_IMPL_H_
#define PINS_P4RT_APP_SONIC_PACKETIO_IMPL_H_

#include <memory>
#include <string>
#include <thread> //NOLINT

#include "absl/container/flat_hash_map.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "p4rt_app/sonic/adapters/system_call_adapter.h"
#include "p4rt_app/sonic/packetio_interface.h"
#include "p4rt_app/sonic/packetio_port.h"
#include "swss/selectable.h"

namespace p4rt_app {
namespace sonic {

struct PacketIoOptions {
  packet_metadata::ReceiveCallbackFunction callback_function = nullptr;
  bool use_genetlink = false;
};

// Implementation class for PacketIoInterface.
class PacketIoImpl : public PacketIoInterface {
public:
  explicit PacketIoImpl(std::unique_ptr<SystemCallAdapter> system_call_adapter,
                        const PacketIoOptions &options)
      : system_call_adapter_(std::move(system_call_adapter)),
        callback_function_(options.callback_function),
        use_genetlink_(options.use_genetlink) {}

  // Not copyable or moveable.
  PacketIoImpl(const PacketIoImpl &) = delete;
  PacketIoImpl &operator=(const PacketIoImpl &) = delete;

  // Start the receive thread for the packet-io interfaces that invokes callback
  // function for every packet in.
  ABSL_MUST_USE_RESULT absl::StatusOr<std::thread>
  StartReceive(packet_metadata::ReceiveCallbackFunction callback_function,
               bool use_genetlink) override;

  // Add a new port to Packet I/O.
  absl::Status AddPacketIoPort(absl::string_view port_name) override;

  // Remove an existing port from Packet I/O.
  absl::Status RemovePacketIoPort(absl::string_view port_name) override;

  // Send the given packet out on the specified interface.
  absl::Status SendPacketOut(absl::string_view port_name,
                             const std::string &packet) override;

  // Checks if a transmit socket exists for the specified port.
  bool IsValidPortForTransmit(absl::string_view port_name) const;

  // Checks if a receive socket (netdev model) exists for the specified port.
  bool IsValidPortForReceive(absl::string_view port_name) const;

private:
  // System call adapter object to call into the utility functions.
  const std::unique_ptr<SystemCallAdapter> system_call_adapter_;

  // Map of Transmit port names and the sockets.
  absl::flat_hash_map<std::string, int> port_to_socket_;

  // Callback function used in receive callbacks.
  packet_metadata::ReceiveCallbackFunction callback_function_;

  // Uses genetlink or netdev model for receive.
  bool use_genetlink_ = false;

  // Map of port to PacketInSelectables.
  absl::flat_hash_map<std::string, std::unique_ptr<PacketInSelectable>>
      port_to_selectables_;

  // Stores the 'Select' object used in the receive thread.
  swss::Select port_select_;
};

} // namespace sonic
} // namespace p4rt_app

#endif // PINS_P4RT_APP_SONIC_PACKETIO_IMPL_H_
