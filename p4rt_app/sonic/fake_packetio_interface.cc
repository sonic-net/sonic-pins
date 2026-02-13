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
#include "p4rt_app/sonic/fake_packetio_interface.h"

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/synchronization/mutex.h"
#include "gutil/collections.h"

namespace p4rt_app {
namespace sonic {

absl::Status FakePacketIoInterface::PushPacketIn(
    absl::string_view source_port, absl::string_view target_port,
    absl::string_view packet) const {
  VLOG(1) << "Pushing packet in: " << source_port << ", " << target_port << ", "
          << packet;

  // Invoke the callback function for the passed in packets.
  return callback_function_(std::string(source_port), std::string(target_port),
                            std::string(packet));
}

absl::StatusOr<std::vector<std::string>> FakePacketIoInterface::VerifyPacketOut(
    absl::string_view port_name) {
  VLOG(1) << "Verify packet out: " << port_name;
  absl::MutexLock p(&packet_lock_);
  ASSIGN_OR_RETURN(
      const auto packets,
      gutil::FindOrStatus(transmit_packets_, std::string(port_name)),
      _ << "Unable to find transmit packets for " << port_name);
  return packets;
}

// Faked methods.
absl::StatusOr<std::thread> FakePacketIoInterface::StartReceive(
    const packet_metadata::ReceiveCallbackFunction callback_function,
    bool use_genetlink) {
  VLOG(1) << "Start Receive.";
  if (callback_function == nullptr) {
    return absl::InvalidArgumentError("Callback function cannot be null");
  }
  callback_function_ = callback_function;
  return std::thread();
}

absl::Status FakePacketIoInterface::SendPacketOut(absl::string_view port_name,
                                                  const std::string& packet) {
  VLOG(1) << "Sending packet out: " << port_name << ", " << packet;
  if (!valid_ports_.contains(port_name)) {
    return absl::InvalidArgumentError(
        absl::StrCat("Unable to find port for PacketOut: ", port_name));
  }
  absl::MutexLock p(&packet_lock_);
  transmit_packets_[port_name].push_back(packet);
  return absl::OkStatus();
}

absl::Status FakePacketIoInterface::AddPacketIoPort(
    absl::string_view port_name) {
  valid_ports_.emplace(port_name);
  return absl::OkStatus();
}

absl::Status FakePacketIoInterface::RemovePacketIoPort(
    absl::string_view port_name) {
  const auto it = valid_ports_.find(port_name);
  if (it == valid_ports_.end()) {
    return absl::InvalidArgumentError(
        absl::StrCat("Unable to find port for removal: ", port_name));
  }
  valid_ports_.erase(it);
  return absl::OkStatus();
}

}  // namespace sonic
}  // namespace p4rt_app
