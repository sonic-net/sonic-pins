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
#ifndef GOOGLE_P4RT_APP_SONIC_PACKETIO_INTERFACE_H_
#define GOOGLE_P4RT_APP_SONIC_PACKETIO_INTERFACE_H_

#include <memory>
#include <string>
#include <thread>  //NOLINT

#include "absl/status/status.h"
#include "p4rt_app/sonic/receive_genetlink.h"

namespace p4rt_app {
namespace sonic {

// Base class for PacketIoInterface.
class PacketIoInterface {
 public:
  virtual ~PacketIoInterface() = default;
  // Add a new port to Packet I/O.
  virtual absl::Status AddPacketIoPort(absl::string_view port_name) = 0;
  // Remove an existing port from Packet I/O.
  virtual absl::Status RemovePacketIoPort(absl::string_view port_name) = 0;
  ABSL_MUST_USE_RESULT virtual absl::StatusOr<std::thread> StartReceive(
      packet_metadata::ReceiveCallbackFunction callback_function,
      bool use_genetlink) = 0;
  // Send the given packet out on the specified interface.
  virtual absl::Status SendPacketOut(absl::string_view port_name,
                                     const std::string& packet) = 0;
};

}  // namespace sonic
}  // namespace p4rt_app

#endif  // GOOGLE_P4RT_APP_SONIC_PACKETIO_INTERFACE_H_
