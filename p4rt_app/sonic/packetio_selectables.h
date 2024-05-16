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
#ifndef PINS_P4RT_APP_SONIC_PACKETIO_SELECTABLES_H_
#define PINS_P4RT_APP_SONIC_PACKETIO_SELECTABLES_H_

#include <memory>
#include <string>

#include "p4rt_app/sonic/receive_genetlink.h"
#include "swss/selectable.h"

namespace p4rt_app {
namespace sonic {

// A class derived from Selectable base class only to re-use the EPOLL wait
// mechanism. Operates on receive socket that was created for each netdev port
// and the virtual funcs will read the buffers when packet in arrives.
class PacketInSelectable : public swss::Selectable {
 public:
  PacketInSelectable(absl::string_view port_name, int receive_socket,
                     packet_metadata::ReceiveCallbackFunction callback_function)
      : port_name_(port_name),
        receive_socket_(receive_socket),
        callback_function_(callback_function) {}
  ~PacketInSelectable() override{};

  // Override functions.
  int getFd() override;
  // Reads data from socket and invokes callback function to pass back the In
  // packet.
  uint64_t readData() override;

 private:
  PacketInSelectable(const PacketInSelectable&) = delete;
  PacketInSelectable& operator=(const PacketInSelectable&) = delete;

  // Sonic port name.
  std::string port_name_;
  // Receive socket.
  int receive_socket_;
  // Buffer to hold data read from socket.
  char read_buffer_[1024];
  // Callback function to be invoked.
  packet_metadata::ReceiveCallbackFunction callback_function_;
};

}  // namespace sonic
}  // namespace p4rt_app

#endif  // PINS_P4RT_APP_SONIC_PACKETIO_SELECTABLES_H_
