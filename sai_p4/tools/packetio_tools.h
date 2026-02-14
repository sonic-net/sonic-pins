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

#ifndef PINS_SAI_P4_TOOLS_PACKETIO_TOOLS_H_
#define PINS_SAI_P4_TOOLS_PACKETIO_TOOLS_H_

#include "absl/status/statusor.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"

namespace sai {

// The SAI P4 packet out metadata as a struct.
struct PacketOutMetadata {
  bool submit_to_ingress;
  const std::string &payload;
  const std::string &egress_port;
};

// Creates a PI PacketOut message in a backwards-compatible manner. Done by
// enumerating all metadata seen in current and previous SAI P4 programs and
// only including the metadata present in `p4info`.
absl::StatusOr<p4::v1::PacketOut>
MakePiPacketOutMessage(const p4::config::v1::P4Info &p4info,
                       const PacketOutMetadata &packet_out_metadata);

// TODO: Remove overload that takes in IR p4info to avoid PDPI
// dependency. Issue is that callers only have access to Ir P4Info. Once this is
// no longer an issue, move implementation from this overload to PI version.
absl::StatusOr<p4::v1::PacketOut>
MakePiPacketOutMessage(const pdpi::IrP4Info &p4info,
                       const PacketOutMetadata &packet_out_metadata);

} // namespace sai

#endif // PINS_SAI_P4_TOOLS_PACKETIO_H_
