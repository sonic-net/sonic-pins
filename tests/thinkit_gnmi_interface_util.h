// Copyright 2025 Google LLC
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

#ifndef PINS_TESTS_THINKIT_GNMI_INTERFACE_UTIL_H_
#define PINS_TESTS_THINKIT_GNMI_INTERFACE_UTIL_H_

#include <string>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "gutil/gutil/testing.h"
#include "include/nlohmann/json.hpp"
#include "lib/gnmi/gnmi_helper.h"
#include "p4_infra/p4_pdpi/pd.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

namespace pins_test {

inline constexpr int kMaxPortLanes = 8;
inline constexpr int kEthernetLen = 8;
inline constexpr int kBreakoutSpeedOffset = 3;
inline constexpr char kEthernet[] = "Ethernet";
const int kSlotIndex = 0;
const int kPortIndex = 1;
const int kLaneIndex = 2;
const int kSlotPortLaneMinValues = 2;
const int kSlotPortLaneMaxValues = 3;

// PortBreakoutInfo contains physical channels and operational status for an
// interface.
typedef struct {
  std::string physical_channels;  // Eg. format: [0,1,2,3]
  std::string oper_status;        // Eg. format: "UP"
  std::string breakout_speed;     // Eg. format: 400G
} PortBreakoutInfo;

typedef struct {
  std::string port_name;  // Randomly selected port on switch.
  std::string
      curr_breakout_mode;  // Currently configured breakout mode on the port.
  std::string supported_breakout_mode;  // Supported breakout mode on port
                                        // different from current breakout mode.
} RandomPortBreakoutInfo;

typedef struct {
  int slot;
  int port;
  int lane;
} SlotPortLane;

enum BreakoutType { kAny, kChannelized };

// GetSupportedBreakoutModesForPort returns list of supported breakout modes for
// given interface.
absl::StatusOr<std::vector<std::string>> GetSupportedBreakoutModesForPort(
    const std::string& interface_info, const absl::string_view port,
    const BreakoutType breakout_type = BreakoutType::kAny);

// BreakoutResultsInSpeedChangeOnly returns whether changing from current to new
// breakout mode would result in a speed change only.
absl::StatusOr<bool> BreakoutResultsInSpeedChangeOnly(
    const std::string& port, const std::string& current_breakout_mode,
    const std::string& new_breakout_mode);

absl::StatusOr<bool> IsSfpPlusPort(gnmi::gNMI::StubInterface& sut_gnmi_stub,
                                   absl::string_view port_name);

absl::StatusOr<absl::flat_hash_set<int>> GetPortSetWithOsfpOptics(
    gnmi::gNMI::StubInterface& sut_gnmi_stub);

absl::StatusOr<absl::flat_hash_map<int, std::vector<std::string>>>
GetXcvrToInterfacesMapGivenPmdType(gnmi::gNMI::StubInterface& sut_gnmi_stub,
                                   absl::string_view pmd_type);

// GetRandomPortWithSupportedBreakoutModes attempts to get a random port from
// list of front panel ports that supports at least one more breakout mode other
// than the currently configured breakout mode.
// If allow_list is empty, all available ports on the switch will be used.
absl::StatusOr<RandomPortBreakoutInfo> GetRandomPortWithSupportedBreakoutModes(
    gnmi::gNMI::StubInterface& sut_gnmi_stub,
    const std::string& platform_json_contents,
    const BreakoutType new_breakout_type = BreakoutType::kAny,
    const BreakoutType current_breakout_type = BreakoutType::kAny,
    const std::vector<absl::string_view>& allow_list = {});

// GetBreakoutStateInfoForPort returns the state values of physical channels and
// operational status information for ports in a given breakout mode.
absl::StatusOr<absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>>
GetBreakoutStateInfoForPort(gnmi::gNMI::StubInterface* sut_gnmi_stub,
                            const std::string& port,
                            absl::string_view breakout_mode);

// GetExpectedPortInfoForBreakoutMode returns the expected port list and
// physical channels for a given breakout mode.
// Eg. Ethernet0 configured to a breakout mode of "2x100G + 1x200G" will return
// the following: Ethernet0:{0,1}, Ethernet2:{2,3}, Ethernet4:{4,5,6,7}. The
// number of physical channels per breakout mode is used to compute the offset
// from the parent port number.
absl::StatusOr<absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>>
GetExpectedPortInfoForBreakoutMode(const std::string& port,
                                   absl::string_view breakout_mode);

// GetBreakoutModeConfigFromString returns breakout config path values from
// given breakout mode. Breakout mode is in the format "numBreakouts1 x
// breakoutSpeed1 + numBreakouts2 x breakoutSpeed2 + ... Eg: "1x400G", 2x100G +
// 1x200G".
absl::Status GetBreakoutModeConfigFromString(
    gnmi::SetRequest& req, gnmi::gNMI::StubInterface* sut_gnmi_stub,
    const absl::string_view port_index, const absl::string_view intf_name,
    const absl::string_view breakout_mode);
// Same as above expect this function returns a JSON string.
absl::StatusOr<std::string> GetBreakoutModeConfigJson(
    gnmi::gNMI::StubInterface* sut_gnmi_stub,
    const absl::string_view port_index, const absl::string_view intf_name,
    const absl::string_view breakout_mode);

// GetNonExistingPortsAfterBreakout returns list of ports that were part of a
// previous breakout config but no longer exist after a new breakout config is
// applied.
// For a negative test case where we do not expect the breakout mode on
// the port to change, ports in new breakout config that were not originally
// present should not exist as the config is not successfully applied.
// For a successful test case where we expect the breakout mode to be applied on
// the port, ports in original breakout config that were not in new breakout
// config should no longer exist as new breakout is now applied.
std::vector<std::string> GetNonExistingPortsAfterBreakout(
    const absl::flat_hash_map<std::string, PortBreakoutInfo>&
        original_port_info,
    const absl::flat_hash_map<std::string, PortBreakoutInfo>& new_port_info,
    bool expected_success);

// ValidateBreakoutState checks the breakout related state paths with the
// expected values.
// For a negative test case where we do not expect the breakout mode on the port
// to change, the expected_port_info contains state path values of the original
// breakout mode before pushing new breakout mode.
// For a successful test case where we expect the breakout mode to be applied on
// the port, the expected_port_info contains expected breakout values for the
// new mode.
absl::Status ValidateBreakoutState(
    gnmi::gNMI::StubInterface* sut_gnmi_stub,
    const absl::flat_hash_map<std::string, PortBreakoutInfo>&
        expected_port_info,
    const std::vector<std::string>& non_existing_ports_list);

absl::StatusOr<std::string> GetPortIndex(
    absl::string_view platform_json_contents, absl::string_view port);

std::string ConstructSupportedBreakoutMode(absl::string_view num_breakouts,
                                           absl::string_view breakout_speed);

// IsCopperPort returns whether the port is copper or optic.
absl::StatusOr<bool> IsCopperPort(gnmi::gNMI::StubInterface* sut_gnmi_stub,
                                  absl::string_view port);

// Returns (slot/port/lane) info for a front panel port Ethernet<slot/port/lane>
absl::StatusOr<SlotPortLane> GetSlotPortLaneForPort(
    const absl::string_view port);

// GetCurrentBreakoutModeForPort returns the current breakout mode for the
// master port.
absl::StatusOr<std::string> GetCurrentBreakoutModeForPort(
    gnmi::gNMI::StubInterface& sut_gnmi_stub, absl::string_view port);

// IsParentPort returns status OK is port is a parent port.
absl::StatusOr<bool> IsParentPort(absl::string_view port);

// IsChannelizedBreakoutMode returns whether the given breakout mode is
// channelized or no.
absl::StatusOr<bool> IsChannelizedBreakoutMode(const std::string& mode);

// Returns an EK_PHYSICAL_PORT name given an EK_PORT name.
// For example, the call below would return "phy-1/2".
//   DeriveEkPhysicalPort("Ethernet1/2/5")
absl::StatusOr<std::string> DeriveEkPhysicalPort(absl::string_view ek_port);
}  // namespace pins_test
#endif  // PINS_TESTS_THINKIT_GNMI_INTERFACE_UTIL_H_
