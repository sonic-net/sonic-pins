// Copyright 2025 Google LLC
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
#ifndef PINS_LIB_LACP_IXIA_HELPER_H_
#define PINS_LIB_LACP_IXIA_HELPER_H_

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <variant>
#include <vector>

#include "absl/status/statusor.h"
#include "thinkit/generic_testbed.h"

namespace pins_test::ixia {

inline constexpr std::string_view kLacpHeaderName = "LACP";

// LACP should be the second header in the stack after Ethernet.
inline constexpr int kLacpStackIndex = 2;

inline constexpr std::string_view kLacpDestinationMac = "01:80:c2:00:00:02";

// LACP field indices from the Ixia REST API:
// https://screenshot.googleplex.com/7xbTsRujEo35fCQ
// https://screenshot.googleplex.com/5xr8swenjNcYcXs
// https://screenshot.googleplex.com/4kx5bAJg4NsiFQV
namespace LacpField {

inline constexpr int kSubType = 1;
inline constexpr int kVersion = 2;
inline constexpr int kActorTlvType = 3;
inline constexpr int kActorTlvLength = 4;
inline constexpr int kActorSystemPriority = 5;
inline constexpr int kActorSystemId = 6;
inline constexpr int kActorKey = 7;
inline constexpr int kActorPortPriority = 8;
inline constexpr int kActorPortId = 9;
inline constexpr int kActorState = 10;
// Field 11 is reserved.
inline constexpr int kPartnerTlvType = 12;
inline constexpr int kPartnerTlvLength = 13;
inline constexpr int kPartnerSystemPriority = 14;
inline constexpr int kPartnerSystemId = 15;
inline constexpr int kPartnerKey = 16;
inline constexpr int kPartnerPortPriority = 17;
inline constexpr int kPartnerPortId = 18;
inline constexpr int kPartnerState = 19;
// Field 20 is reserved.
inline constexpr int kCollectorTlvType = 21;
inline constexpr int kCollectorTlvLength = 22;
inline constexpr int kCollectorMaxDelay = 23;
// Field 24 is reserved.
inline constexpr int kTerminatorTlvType = 25;
inline constexpr int kTerminatorTlvLength = 26;
// Field 27 is reserved.
inline constexpr int kFCS = 28;

}  // namespace LacpField

namespace LacpState {

inline constexpr int kActivity = 1 << 0;
inline constexpr int kTimeout = 1 << 1;
inline constexpr int kAggregation = 1 << 2;
inline constexpr int kSync = 1 << 3;
inline constexpr int kCollecting = 1 << 4;
inline constexpr int kDistributing = 1 << 5;
inline constexpr int kDefaulted = 1 << 6;
inline constexpr int kExpired = 1 << 7;

}  // namespace LacpState

// Information about an agent (actor or partner).
// Each field can either be a single value or a vector of values.
// If a single value is provided, it will be used for all packets.
// If a vector is provided, the values will cycle through the vector elements.
// The strings are always interpreted as hex values (0x prefix is optional).
struct AgentInfo {
  std::variant<std::string, std::vector<std::string>> system_priority;
  std::variant<std::string, std::vector<std::string>> system_id;
  std::variant<std::string, std::vector<std::string>> key;
  std::variant<std::string, std::vector<std::string>> port_priority;
  std::variant<std::string, std::vector<std::string>> port_id;
  std::variant<std::string, std::vector<std::string>> state;
};

// Information about the LACP packets to send.
// Contains the information for actor and partner, as well as the source MAC to
// set in the Ethernet header.
struct LacpInfo {
  std::string source_mac;
  AgentInfo actor;
  AgentInfo partner;
};

// Options for sending traffic. If `packet_count` isn't set, the traffic will be
// sent continuously.
struct LacpTrafficItemOptions {
  float packets_per_second;
  std::optional<int64_t> packet_count;
};

// Creates a traffic item that sends LACP packets.
// The created traffic item still needs to be generated, applied, and then
// started/stopped.
absl::StatusOr<std::string> CreateLacpTrafficItem(
    std::string_view vport, const LacpInfo& lacp_info,
    const LacpTrafficItemOptions& options, thinkit::GenericTestbed& testbed);

}  // namespace pins_test::ixia

#endif  // PINS_LIB_LACP_IXIA_HELPER_H_
