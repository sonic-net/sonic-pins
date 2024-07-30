// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "tests/forwarding/util.h"

#include <algorithm>
#include <sstream>

#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "gutil/status.h"
#include "p4_pdpi/ir.pb.h"
#include "sai_p4/tools/packetio_tools.h"

namespace gpins {

absl::Status TryUpToNTimes(int n, absl::Duration delay,
                           std::function<absl::Status(int)> callback) {
  RET_CHECK(n > 0) << "n should be greater than 0";
  absl::Status result;
  for (int i = 1; i <= n; ++i) {
    result = callback(i);
    if (result.ok() || i == n) break;
    absl::SleepFor(delay);
  }
  return result;
}

absl::Status TryUpToNTimes(int n, absl::Duration delay,
                           std::function<absl::Status()> callback) {
  return TryUpToNTimes(n, delay, [=](int) { return callback(); });
}

absl::Status InjectEgressPacket(const std::string& port,
                                const std::string& packet,
                                const pdpi::IrP4Info& p4info,
                                pdpi::P4RuntimeSession* p4rt,
                                std::optional<absl::Duration> packet_delay) {
  // Assemble P4Runtime request.
  p4::v1::StreamMessageRequest request;
  ASSIGN_OR_RETURN(
      *request.mutable_packet(),
      sai::MakePiPacketOutMessage(p4info, sai::PacketOutMetadata{
                                              .submit_to_ingress = false,
                                              .payload = packet,
                                              .egress_port = port,
                                          }));

  // Rate limit the packets, if specified.
  if (packet_delay.has_value()) absl::SleepFor(*packet_delay);

  return p4rt->StreamChannelWrite(request)
             ? absl::OkStatus()
             : gutil::InternalErrorBuilder()
                   << "Failed to write stream message request: "
                   << request.ShortDebugString();
}

absl::Status InjectIngressPacket(const std::string& packet,
                                 const pdpi::IrP4Info& p4info,
                                 pdpi::P4RuntimeSession* p4rt,
                                 std::optional<absl::Duration> packet_delay) {
  // Assemble P4Runtime request.
  p4::v1::StreamMessageRequest request;
  ASSIGN_OR_RETURN(
      *request.mutable_packet(),
      sai::MakePiPacketOutMessage(p4info, sai::PacketOutMetadata{
                                              .submit_to_ingress = true,
                                              .payload = packet,
                                              .egress_port = "Unused",
                                          }));

  // Rate limit the packets, if specified.
  if (packet_delay.has_value()) absl::SleepFor(*packet_delay);

  return p4rt->StreamChannelWrite(request)
             ? absl::OkStatus()
             : gutil::InternalErrorBuilder()
                   << "Failed to write stream message request: "
                   << request.ShortDebugString();
}

}  // namespace gpins
