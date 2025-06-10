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
#ifndef PINS_P4RT_APP_SONIC_PACKETIO_PORT_H_
#define PINS_P4RT_APP_SONIC_PACKETIO_PORT_H_

#include <memory>
#include <string>

#include "absl/container/flat_hash_map.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "glog/logging.h"
#include "p4_infra/p4_pdpi/ir_utils.h"
#include "p4rt_app/sonic/adapters/system_call_adapter.h"
#include "p4rt_app/sonic/packetio_selectables.h"
#include "p4rt_app/sonic/receive_genetlink.h"
#include "swss/select.h"
#include "swss/selectable.h"

namespace p4rt_app {
namespace sonic {

// A structure to hold port parameters related to packet I/O.
struct PacketIoPortParams {
  int socket;
  std::unique_ptr<PacketInSelectable> packet_in_selectable;
};

// Adds a port to packet I/O by creating the receive & transmit sockets.
absl::StatusOr<std::unique_ptr<PacketIoPortParams>>
AddPacketIoPort(const SystemCallAdapter &system_call_adapter,
                absl::string_view port_name,
                packet_metadata::ReceiveCallbackFunction callback_function);

// Send a packet out on the specified egress socket.
absl::Status SendPacketOut(const SystemCallAdapter &system_call_adapter,
                           int transmit_socket,
                           absl::string_view interface_name,
                           const std::string &packet);

} // namespace sonic
} // namespace p4rt_app

#endif // PINS_P4RT_APP_SONIC_PACKETIO_PORT_H_
