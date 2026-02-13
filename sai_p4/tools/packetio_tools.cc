// Copyright 2024 Google LLC
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

#include "sai_p4/tools/packetio_tools.h"

#include "absl/status/statusor.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "sai_p4/fixed/ids.h"

namespace sai {

absl::StatusOr<p4::v1::PacketOut> MakePiPacketOutMessage(
    const p4::config::v1::P4Info& p4info,
    const PacketOutMetadata& packet_out_metadata) {
  ASSIGN_OR_RETURN(pdpi::IrP4Info ir_p4info, pdpi::CreateIrP4Info(p4info));
  return (MakePiPacketOutMessage(ir_p4info, packet_out_metadata));
}

// Function must be updated if new packet out metadata is added to SAI P4
// program, otherwise will return an UNIMPLEMENTED error. Changes must not be
// made if metadata is removed for the sake of backwards compatibility.
absl::StatusOr<p4::v1::PacketOut> MakePiPacketOutMessage(
    const pdpi::IrP4Info& p4info,
    const PacketOutMetadata& packet_out_metadata) {
  p4::v1::PacketOut packet_out;
  packet_out.set_payload(packet_out_metadata.payload);

  for (const auto& [id, metadata_definition] :
       p4info.packet_out_metadata_by_id()) {
    p4::v1::PacketMetadata* metadata = packet_out.add_metadata();
    metadata->set_metadata_id(id);
    switch (id) {
      case PACKET_OUT_SUBMIT_TO_INGRESS_ID:
        metadata->set_value((packet_out_metadata.submit_to_ingress
                                 ? std::string({'\1'})
                                 : std::string({'\0'})));
        break;
      case PACKET_OUT_EGRESS_PORT_ID:
        metadata->set_value(packet_out_metadata.egress_port);
        break;
      case PACKET_OUT_UNUSED_PAD_ID:
        // Unused padding always contains zero-value string.
        metadata->set_value(std::string({'\0'}));
        break;
      default:
        return gutil::UnimplementedErrorBuilder()
               << "Metadata with id `" << id << "` and name `"
               << metadata_definition.metadata().name()
               << "` is not currently supported. Ensure change to packet out "
                  "is desired and if so, update this function to add support.";
    }
  }

  return packet_out;
}

}  // namespace sai
