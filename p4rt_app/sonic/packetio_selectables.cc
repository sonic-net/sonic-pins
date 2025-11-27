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
#include "p4rt_app/sonic/packetio_selectables.h"

#include <sys/socket.h>
#include <unistd.h>

#include <iomanip>
#include <iostream>
#include <memory>
#include <sstream>
#include <string>
#include <vector>

#include "absl/log/log.h"

namespace p4rt_app {
namespace sonic {

// Max buffer size for Receive packets.
static constexpr int kPacketIoPortMaxBufferSize = 1024;

// Return the receive socket used for this port.
int PacketInSelectable::getFd() { return receive_socket_; }

// Reads data from socket and invokes callback function to pass back the In
// packet.
uint64_t PacketInSelectable::readData() {
  ssize_t msg_len = 0;
  do {
    msg_len = read(receive_socket_, read_buffer_, kPacketIoPortMaxBufferSize);
  } while (errno == EINTR);
  if (msg_len < 0) {
    LOG(ERROR) << "Error " << errno << " in reading buffer from socket for "
               << port_name_;
  } else if (msg_len == 0) {
    LOG(ERROR) << "Unexpected socket shutdown during read for " << port_name_;
  } else {
    std::string packet(read_buffer_, msg_len);
    // Just pass empty string for target egress port since this support is not
    // available in netdev model.
    auto status = callback_function_(port_name_, "", packet);
    if (!status.ok()) {
      LOG(WARNING) << "Unable to send packet to the controller"
                   << status.ToString();
    }
  }

  return 0;
}

}  // namespace sonic
}  // namespace p4rt_app
