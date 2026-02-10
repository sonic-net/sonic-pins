// Copyright (c) 2024, Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#ifndef PINS_LIB_BASIC_TRAFFIC_BASIC_P4RT_UTIL_H_
#define PINS_LIB_BASIC_TRAFFIC_BASIC_P4RT_UTIL_H_

#include <functional>
#include <string>

#include "absl/functional/bind_front.h"
#include "absl/status/status.h"
#include "absl/strings/str_format.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.pb.h"

namespace pins_test::basic_traffic {

// A function that handles sending a write request to a `P4RuntimeSession`.
using WriteRequestHandler = std::function<absl::Status(pdpi::P4RuntimeSession *,
                                                       p4::v1::WriteRequest &)>;

// Returns a standardized IP from a `port_id` for use by `basic_traffic`
// utilities.
inline std::string PortIdToIP(int port_id) {
  return absl::StrFormat("10.0.%d.%d", port_id / 256, port_id % 256);
}

// Returns a standardized MAC from a `port_id` for use by `basic_traffic`
// utilities.
inline std::string PortIdToMac(int port_id) {
  return absl::StrFormat("00:00:00:00:%02x:%02x", port_id / 256, port_id % 256);
}

// Programs a VRF that matches on all packets ingressing into the SUT. Takes in
// a function that programs a `WriteRequest`.
absl::Status ProgramTrafficVrf(
    const std::function<absl::Status(p4::v1::WriteRequest &)> &write_request,
    const pdpi::IrP4Info &ir_p4info);

// Programs a VRF that matches on all packets ingressing into the SUT. Takes in
// a `P4RuntimeSession`.
inline absl::Status
ProgramTrafficVrf(pdpi::P4RuntimeSession *session,
                  const pdpi::IrP4Info &ir_p4info,
                  const WriteRequestHandler &write_request =
                      pdpi::SetMetadataAndSendPiWriteRequest) {
  return ProgramTrafficVrf(absl::bind_front(write_request, session), ir_p4info);
}

// Programs a router interface for the specified `port_id`. Uses `PortIdToMac`
// as the MAC address. Takes in a function that programs a `WriteRequest`.
absl::Status ProgramRouterInterface(
    const std::function<absl::Status(p4::v1::WriteRequest &)> &write_request,
    int port_id, const pdpi::IrP4Info &ir_p4info);

// Programs a router interface for the specified `port_id`. Uses `PortIdToMac`
// as the MAC address. Takes in a `P4RuntimeSession`.
inline absl::Status
ProgramRouterInterface(pdpi::P4RuntimeSession *session, int port_id,
                       const pdpi::IrP4Info &ir_p4info,
                       const WriteRequestHandler &write_request =
                           pdpi::SetMetadataAndSendPiWriteRequest) {
  return ProgramRouterInterface(absl::bind_front(write_request, session),
                                port_id, ir_p4info);
}

// Programs an IPv4 route that forwards a destination IP to the specified
// `port_id`. Uses `PortIdToIP` for the destination IP to match against. Takes
// in a function that programs a `WriteRequest`.
absl::Status ProgramIPv4Route(
    const std::function<absl::Status(p4::v1::WriteRequest &)> &write_request,
    int port_id, const pdpi::IrP4Info &ir_p4info);

// Programs an IPv4 route that forwards a destination IP to the specified
// `port_id`. Uses `PortIdToIP` for the destination IP to match against. Takes
// in a `P4RuntimeSession`.
inline absl::Status
ProgramIPv4Route(pdpi::P4RuntimeSession *session, int port_id,
                 const pdpi::IrP4Info &ir_p4info,
                 const WriteRequestHandler &write_request =
                     pdpi::SetMetadataAndSendPiWriteRequest) {
  return ProgramIPv4Route(absl::bind_front(write_request, session), port_id,
                          ir_p4info);
}

// Programs L3 admit table entry allowing all unicast packets to be routed.
// Takes in a function that programs a `WriteRequest`.
absl::Status ProgramL3AdmitTableEntry(
    const std::function<absl::Status(p4::v1::WriteRequest &)> &write_request,
    const pdpi::IrP4Info &ir_p4info);

// Programs L3 admit table entry allowing all unicast packets to be routed.
// Takes in a `P4RuntimeSession`.
inline absl::Status
ProgramL3AdmitTableEntry(pdpi::P4RuntimeSession *session,
                         const pdpi::IrP4Info &ir_p4info,
                         const WriteRequestHandler &write_request =
                             pdpi::SetMetadataAndSendPiWriteRequest) {
  return ProgramL3AdmitTableEntry(absl::bind_front(write_request, session),
                                  ir_p4info);
}

} // namespace pins_test::basic_traffic

#endif // PINS_LIB_BASIC_TRAFFIC_BASIC_P4RT_UTIL_H_
