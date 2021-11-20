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
#ifndef GOOGLE_P4RT_APP_SONIC_PACKETIO_IMPL_H_
#define GOOGLE_P4RT_APP_SONIC_PACKETIO_IMPL_H_

#include <memory>
#include <string>
#include <thread>  //NOLINT

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "glog/logging.h"
#include "p4rt_app/sonic/adapters/system_call_adapter.h"
#include "p4rt_app/sonic/packetio_interface.h"
#include "p4rt_app/sonic/packetio_port.h"

namespace p4rt_app {
namespace sonic {

// Implementation class for PacketIoInterface.
class PacketIoImpl final : public PacketIoInterface {
 public:
  // Factory method to discover and create sockets for packetio interfaces.
  static absl::StatusOr<std::unique_ptr<PacketIoInterface>>
  CreatePacketIoImpl();
  // Start the receive thread for the packet-io interfaces that invokes callback
  // function for every packet in.
  ABSL_MUST_USE_RESULT absl::StatusOr<std::thread> StartReceive(
      packet_metadata::ReceiveCallbackFunction callback_function,
      bool use_genetlink);
  // Send the given packet out on the specified interface.
  absl::Status SendPacketOut(absl::string_view port_name,
                             const std::string& packet);
  PacketIoImpl(const PacketIoImpl&) = delete;
  PacketIoImpl& operator=(const PacketIoImpl&) = delete;
  PacketIoImpl() = delete;
  // Use only in unit tests, use factory method otherwise.
  PacketIoImpl(
      std::unique_ptr<SystemCallAdapter> system_call_adapter,
      std::vector<std::unique_ptr<sonic::PacketIoPortSockets>> port_sockets);

 private:
  // System call adapter object to call into the utility functions.
  const std::unique_ptr<SystemCallAdapter> system_call_adapter_;
  // Vector of PacketIoPortSockets;
  const std::vector<std::unique_ptr<sonic::PacketIoPortSockets>> port_sockets_;
  // Map of Transmit port names and the sockets.
  const absl::flat_hash_map<std::string, int> socket_map_;
};

}  // namespace sonic
}  // namespace p4rt_app

#endif  // GOOGLE_P4RT_APP_SONIC_PACKETIO_IMPL_H_
