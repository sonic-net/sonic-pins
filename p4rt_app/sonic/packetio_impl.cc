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

#include <memory>
#include <thread>  //NOLINT
#include <utility>

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "p4rt_app/sonic/receive_genetlink.h"
#include "swss/selectable.h"

namespace p4rt_app {
namespace sonic {

absl::Status PacketIoImpl::SendPacketOut(absl::string_view port_name,
                                         const std::string& packet) {
  // Retrieve the transmit socket for this egress port.
  int* socket = gutil::FindOrNull(port_to_socket_, std::string(port_name));
  if (socket == nullptr) {
    return gutil::NotFoundErrorBuilder() << absl::StreamFormat(
               "Could not find socket '%s' to send packet out.", port_name);
  }

  std::string netdev_name(port_name);
  return sonic::SendPacketOut(*system_call_adapter_, *socket, netdev_name,
                              packet);
}

absl::Status PacketIoImpl::AddPacketIoPort(absl::string_view port_name) {
  // Nothing to do if this port or already exists.
  if (port_to_socket_.contains(port_name)) {
    return absl::OkStatus();
  }
  LOG(INFO) << "Adding PacketIO port '" << port_name << "'.";

  std::string netdev_name(port_name);
  ASSIGN_OR_RETURN(auto port_params,
                   sonic::AddPacketIoPort(*system_call_adapter_, netdev_name,
                                          callback_function_));

  // Add the socket to transmit socket map.
  port_to_socket_[port_name] = port_params->socket;

  // Nothing more to do, if in genetlink receive mode.
  // PacketInSelectables is needed only for Netdev receive model.
  if (use_genetlink_) return absl::OkStatus();

  // Add the port object into the port select so that receive thread can start
  // monitoring for receive packets.
  port_select_.addSelectable(port_params->packet_in_selectable.get());
  if (bool success = port_to_selectables_
                         .insert({std::string(port_name),
                                  std::move(port_params->packet_in_selectable)})
                         .second;
      !success) {
    return gutil::InternalErrorBuilder()
           << "Packet In selectable already exists for this port: "
           << port_name;
  }
  return absl::OkStatus();
}

absl::Status PacketIoImpl::RemovePacketIoPort(absl::string_view port_name) {
  LOG(INFO) << "Removing PacketIO port '" << port_name << "'.";

  // Cleanup PacketInSelectable, if in Netdev mode.
  if (!use_genetlink_) {
    auto it = port_to_selectables_.find(port_name);
    if (it == port_to_selectables_.end()) {
      return absl::InvalidArgumentError(absl::StrCat(
          "Unable to find selectables for port remove: ", port_name));
    }

    // Remove the port selectable from the selectables object.
    std::unique_ptr<sonic::PacketInSelectable>& port_selectable = it->second;
    port_select_.removeSelectable(port_selectable.get());
    if (port_to_selectables_.erase(port_name) != 1) {
      return gutil::InternalErrorBuilder()
             << "Unable to remove selectable for this port: " << port_name;
    }
  }

  auto socket_iter = port_to_socket_.find(port_name);
  if (socket_iter == port_to_socket_.end()) {
    return gutil::NotFoundErrorBuilder() << absl::StreamFormat(
               "Could not find port '%s' to remove from PacketIo port to "
               "socket map.",
               port_name);
  }
  if (socket_iter->second >= 0) {
    system_call_adapter_->close(socket_iter->second);
  }
  port_to_socket_.erase(socket_iter);

  return absl::OkStatus();
}

bool PacketIoImpl::IsValidPortForTransmit(absl::string_view port_name) const {
  return port_to_socket_.contains(port_name);
}

bool PacketIoImpl::IsValidPortForReceive(absl::string_view port_name) const {
  // Receive valid only if there is a callback function.
  if (callback_function_ == nullptr) return false;

  // For netdev model, additionally check that the receive socket exists.
  if (!use_genetlink_) {
    return port_to_selectables_.contains(port_name);
  }

  return true;
}

absl::StatusOr<std::thread> PacketIoImpl::StartReceive(
    packet_metadata::ReceiveCallbackFunction callback_function,
    const bool use_genetlink) {
  if (callback_function == nullptr) {
    return absl::InvalidArgumentError("Callback function cannot be null");
  }
  callback_function_ = std::move(callback_function);
  use_genetlink_ = use_genetlink;

  if (use_genetlink_) {
    return packet_metadata::StartReceive(callback_function_);
  } else {
    return std::thread([this] {
      LOG(INFO) << "Successfully created Receive thread";
      while (true) {
        swss::Selectable* sel;
        port_select_.select(&sel);
      }
      // Never expected to be here.
    });
  }
}

}  // namespace sonic
}  // namespace p4rt_app
