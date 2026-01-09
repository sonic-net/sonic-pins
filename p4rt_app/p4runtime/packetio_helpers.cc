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
#include "p4rt_app/p4runtime/packetio_helpers.h"

#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "boost/bimap.hpp"
#include "gutil/status.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/utils/ir.h"
#include "p4rt_app/p4runtime/ir_translation.h"
#include "p4rt_app/sonic/packetio_impl.h"
#include "p4rt_app/sonic/packetio_interface.h"
#include "sai_p4/fixed/ids.h"
#include "swss/schema.h"

namespace p4rt_app {

// Adds the given metadata to the PacketIn.
p4::v1::PacketIn CreatePacketInMessage(const std::string& source_port_id,
                                       const std::string& target_port_id) {
  p4::v1::PacketIn packet;
  p4::v1::PacketMetadata* metadata = packet.add_metadata();
  // Add Ingress port id.
  metadata->set_metadata_id(PACKET_IN_INGRESS_PORT_ID);
  metadata->set_value(source_port_id);

  // Add target egress port id.
  metadata = packet.add_metadata();
  metadata->set_metadata_id(PACKET_IN_TARGET_EGRESS_PORT_ID);
  metadata->set_value(target_port_id);

  return packet;
}

absl::Status SendPacketOut(
    const pdpi::IrP4Info& p4_info, bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    sonic::PacketIoInterface* const packetio_impl,
    const p4::v1::PacketOut& packet) {
  // Convert to IR to check validity of PacketOut message (e.g. duplicate or
  // missing metadata fields).
  auto translate_status = pdpi::PiPacketOutToIr(p4_info, packet);
  if (!translate_status.ok()) {
    LOG(WARNING) << "PDPI PacketOutToIr failure: " << translate_status.status();
    LOG(WARNING) << "PDPI could not translate PacketOut packet: "
                 << packet.ShortDebugString();
    return gutil::StatusBuilder(translate_status.status().code())
           << "[P4RT/PDPI] " << translate_status.status().message();
  }
  auto ir = *translate_status;

  std::string egress_port_id;
  int submit_to_ingress = 0;
  // Parse the packet metadata to get the value of different attributes,
  for (const auto& meta : packet.metadata()) {
    switch (meta.metadata_id()) {
      case PACKET_OUT_EGRESS_PORT_ID: {
        egress_port_id = meta.value();
        break;
      }
      case PACKET_OUT_SUBMIT_TO_INGRESS_ID: {
        ASSIGN_OR_RETURN(
            submit_to_ingress,
            pdpi::ArbitraryByteStringToUint(meta.value(), /*bitwidth=*/1),
            _ << "Unable to get inject_ingress from the packet metadata");
        break;
      }
      case PACKET_OUT_UNUSED_PAD_ID: {
        // Nothing to do.
        break;
      }
      default:
        return gutil::InvalidArgumentErrorBuilder()
               << "Unexpected Packet Out metadata id " << meta.metadata_id();
    }
  }

  std::string sonic_port_name;
  if (submit_to_ingress == 1) {
    // Use submit_to_ingress attribute value netdev port.
    sonic_port_name = SEND_TO_INGRESS_PORT_NAME;
  } else {
    // Use egress_port_id attribute value.
    if (translate_port_ids) {
      ASSIGN_OR_RETURN(sonic_port_name,
                       TranslatePort(TranslationDirection::kForOrchAgent,
                                     port_translation_map, egress_port_id));
    } else {
      sonic_port_name = egress_port_id;
    }
  }

  // Send packet out via the socket.
  RETURN_IF_ERROR(
      packetio_impl->SendPacketOut(sonic_port_name, packet.payload()));

  return absl::OkStatus();
}

}  // namespace p4rt_app
