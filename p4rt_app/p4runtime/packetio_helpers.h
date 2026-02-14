// Copyright 2022 Google LLC
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
#ifndef PINS_P4RT_APP_P4RUNTIME_PACKET_IO_HELPERS_H_
#define PINS_P4RT_APP_P4RUNTIME_PACKET_IO_HELPERS_H_

#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "boost/bimap.hpp"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4rt_app/sonic/packetio_interface.h"

namespace p4rt_app {

#define SEND_TO_INGRESS_PORT_NAME "SEND_TO_INGRESS"

// Add the required metadata and return a PacketIn.
p4::v1::PacketIn CreatePacketInMessage(const std::string &source_port_id,
                                       const std::string &target_port_id);

// Utility function to parse the packet metadata and send it out via the
// socket interface.
absl::Status SendPacketOut(
    const pdpi::IrP4Info &p4_info, bool translate_port_ids,
    const boost::bimap<std::string, std::string> &port_translation_map,
    sonic::PacketIoInterface *const packetio_impl,
    const p4::v1::PacketOut &packet);

} // namespace p4rt_app

#endif // PINS_P4RT_APP_P4RUNTIME_PACKET_IO_HELPERS_H_
