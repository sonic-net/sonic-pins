/*
 * Copyright 2020 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#ifndef GOOGLE_P4RT_APP_SONIC_FAKE_PACKETIO_INTERFACE_H_
#define GOOGLE_P4RT_APP_SONIC_FAKE_PACKETIO_INTERFACE_H_

#include <thread>  //NOLINT

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "p4rt_app/sonic/packetio_interface.h"

namespace p4rt_app {
namespace sonic {

// FakePacketIo derived class to mimic packet in/out for component tests.
// PacketIn (receive) is faked by having a helper method to invoke the callback
// function (saved when StartReceive was called) with the specified packets.
// PacketOut (transmit) is faked by saving all packets that are sent out and
// having a helper method to return the set of sent packets for a particular
// port.
class FakePacketIoInterface final : public PacketIoInterface {
 public:
  FakePacketIoInterface() = default;
  // Push the receive packets by invoking the callback method.
  absl::Status PushPacketIn(absl::string_view source_port,
                            absl::string_view target_port,
                            absl::string_view packet) const;

  // Return the packets sent for the specified port.
  absl::StatusOr<std::vector<std::string>> VerifyPacketOut(
      absl::string_view port_name);

  // Faked methods.
  absl::StatusOr<std::thread> StartReceive(
      packet_metadata::ReceiveCallbackFunction callback_function,
      bool use_genetlink = false);
  absl::Status SendPacketOut(absl::string_view port_name,
                             const std::string& packet);

 private:
  // Used for fake implementation.
  packet_metadata::ReceiveCallbackFunction callback_function_;
  absl::flat_hash_map<std::string, std::vector<std::string>> transmit_packets_;
};

}  // namespace sonic
}  // namespace p4rt_app

#endif  // GOOGLE_P4RT_APP_SONIC_FAKE_PACKETIO_INTERFACE_H_
