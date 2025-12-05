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

#include "tests/thinkit_gnmi_interface_util.h"

#include <grp.h>

#include <algorithm>
#include <cstddef>
#include <cstdlib>
#include <cstring>
#include <ostream>
#include <string>
#include <unordered_set>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_join.h"
#include "absl/strings/str_replace.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status.h"
#include "include/nlohmann/json.hpp"
#include "lib/gnmi/gnmi_helper.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "re2/re2.h"
#include "tests/thinkit_util.h"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

namespace pins_test {
namespace {

using ::nlohmann::json;

}  // namespace

std::string ConstructSupportedBreakoutMode(absl::string_view num_breakouts,
                                           absl::string_view breakout_speed) {
  std::string breakout_mode = absl::StrCat(num_breakouts, "x", breakout_speed);
  StripSymbolFromString(breakout_mode, ' ');
  return breakout_mode;
}

absl::StatusOr<std::vector<std::string>> GetSupportedBreakoutModesForPort(
    const std::string& interface_info, const absl::string_view port,
    const BreakoutType breakout_type) {
  auto interface_json = json::parse(interface_info);
  // Get breakout modes information from interface entry in platforms.json.
  const auto breakout_modes = interface_json.find("breakout_modes");
  if (breakout_modes == interface_json.end()) {
    return gutil::InternalErrorBuilder().LogError() << absl::InternalError(
               absl::StrCat("Supported breakout modes not found for ", port,
                            " in platform.json"));
  }

  // Create vector of supported breakout modes.
  std::vector<std::string> modes;
  auto breakout_modes_str = breakout_modes->dump();
  StripSymbolFromString(breakout_modes_str, '\"');

  // Parse the breakout_modes_str to extract supported breakout modes.
  // Each supported breakout mode is in the format:
  // num_breakouts x speedG [alternate_speedG, ...]
  size_t i = 0, pos = 0;
  while (i < breakout_modes_str.size() && pos != std::string::npos) {
    pos = breakout_modes_str.find('x', i);
    auto num_breakouts = breakout_modes_str.substr(i, pos - i);
    i = pos + 1;
    pos = breakout_modes_str.find_first_of(",[", i);
    if (pos != std::string::npos) {
      auto speed = breakout_modes_str.substr(i, pos - i);
      modes.push_back(ConstructSupportedBreakoutMode(num_breakouts, speed));
      i = pos + 1;
      if (breakout_modes_str[pos] == '[') {
        // Get alternate speeds for a breakout mode if available.
        do {
          pos = breakout_modes_str.find_first_of(",]", i);
          speed = breakout_modes_str.substr(i, pos - i);
          modes.push_back(ConstructSupportedBreakoutMode(num_breakouts, speed));
          i = pos + 1;
          if (pos != std::string::npos && breakout_modes_str[pos] == ']')
            i += 1;
        } while (breakout_modes_str[pos] != ']');
        if (pos == std::string::npos) {
          // Breakout mode with alternate speeds is the last supported breakout
          // modes in the list.
          break;
        }
      }
    } else {
      // Get last breakout mode in list of breakout modes.
      auto speed = breakout_modes_str.substr(i, std::string::npos);
      modes.push_back(ConstructSupportedBreakoutMode(num_breakouts, speed));
    }
  }

  // Return requested type of breakout modes only is specified.
  // By default all breakout modes will be returned.
  std::vector<std::string> supported_breakout_modes;
  if (breakout_type == BreakoutType::kChannelized) {
    for (const auto& mode : modes) {
      ASSIGN_OR_RETURN(auto is_channelized, IsChannelizedBreakoutMode(mode));
      if (is_channelized) {
        supported_breakout_modes.push_back(mode);
      }
    }
    return supported_breakout_modes;
  }
  return modes;
}

absl::StatusOr<bool> BreakoutResultsInSpeedChangeOnly(
    const std::string& port, const std::string& current_breakout_mode,
    const std::string& new_breakout_mode) {
  // Get list of interfaces for current and new breakout modes.
  ASSIGN_OR_RETURN(auto current_port_info, GetExpectedPortInfoForBreakoutMode(
                                               port, current_breakout_mode));
  ASSIGN_OR_RETURN(auto new_port_info,
                   GetExpectedPortInfoForBreakoutMode(port, new_breakout_mode));
  for (const auto& [key, unused_val] : current_port_info) {
    if (!new_port_info.count(key)) {
      return false;
    }
  }
  for (const auto& [key, unused_val] : new_port_info) {
    if (!current_port_info.count(key)) {
      return false;
    }
  }
  return true;
}

absl::StatusOr<std::string> GetCurrentBreakoutModeForPort(
    gnmi::gNMI::StubInterface& sut_gnmi_stub, absl::string_view port) {
  ASSIGN_OR_RETURN(auto is_parent, IsParentPort(port));
  if (!is_parent) {
    return gutil::InternalErrorBuilder().LogError()
           << "Requested port (" << port << ") is not a parent port";
  }

  // Get the physical port for the front panel port.
  auto if_state_path =
      absl::StrCat("interfaces/interface[name=", port, "]/state/hardware-port");
  auto resp_parse_str = "openconfig-platform-port:hardware-port";
  ASSIGN_OR_RETURN(
      auto physical_port,
      GetGnmiStatePathInfo(&sut_gnmi_stub, if_state_path, resp_parse_str),
      _ << "Failed to get GNMI state path value for interface hardware-port "
           "for port "
        << port);
  StripSymbolFromString(physical_port, '\"');
  // Get the component breakout state paths.
  if_state_path = absl::StrCat("components/component[name=", physical_port,
                               "]/port/breakout-mode/groups");
  resp_parse_str = "openconfig-platform-port:groups";
  ASSIGN_OR_RETURN(
      auto state_path_response,
      GetGnmiStatePathInfo(&sut_gnmi_stub, if_state_path, resp_parse_str),
      _ << "Failed to get GNMI state path value for component breakout paths "
           "for port "
        << port);
  const auto groups = json::parse(state_path_response);
  const auto group = groups.find("group");
  if (group == groups.end()) {
    return gutil::InternalErrorBuilder().LogError()
           << "group not found in state path response";
  }
  std::string current_breakout_mode = "";
  for (const auto& i : *group) {
    auto index = i.find("index");
    if (index == i.end()) {
      return gutil::InternalErrorBuilder().LogError()
             << "index not found in breakout group";
    }
    auto state = i.find("state");
    if (state == i.end()) {
      return gutil::InternalErrorBuilder().LogError()
             << "state not found in breakout group";
    }
    auto num_breakouts = state->find("num-breakouts");
    if (num_breakouts == state->end()) {
      return gutil::InternalErrorBuilder().LogError()
             << "num-breakouts not found in breakout group state";
    }
    auto breakout_speed = state->find("breakout-speed");
    if (breakout_speed == state->end()) {
      return gutil::InternalErrorBuilder().LogError()
             << "breakout-speed not found in breakout group state";
    }
    // Extract speed from breakout-speed string
    // eg: "openconfig-if-ethernet:SPEED_400GB"
    auto pos = breakout_speed->dump().find('_');
    auto len = breakout_speed->dump().length() - pos - kBreakoutSpeedOffset;
    auto bs = breakout_speed->dump().substr(pos + 1, len);
    int index_int;
    if (!absl::SimpleAtoi(index->dump(), &index_int)) {
      return gutil::InternalErrorBuilder().LogError()
             << "Failed to convert string (" << index->dump() << ") to integer";
    }
    if (index_int > 0) {
      absl::StrAppend(&current_breakout_mode, "+");
    }
    absl::StrAppend(&current_breakout_mode, num_breakouts->dump(), "x", bs);
  }
  return current_breakout_mode;
}

absl::StatusOr<bool> IsChannelizedBreakoutMode(const std::string& mode) {
  // A breakout mode is a channelized mode if it is either a mixed mode (eg.
  // 1x200G(4)+2x100G(4)) or it results in more than one number of
  // interfaces (eg. 2x200G).
  auto num_breakouts_str = mode.substr(0, mode.find('x'));
  int num_breakouts;
  if (!absl::SimpleAtoi(num_breakouts_str, &num_breakouts)) {
    return gutil::InternalErrorBuilder().LogError()
           << "Failed to convert string (" << num_breakouts_str
           << ") to integer";
  }
  return ((num_breakouts > 1) || absl::StrContains(mode, "+"));
}

absl::StatusOr<absl::flat_hash_set<int>> GetPortSetWithOsfpOptics(
    gnmi::gNMI::StubInterface& sut_gnmi_stub) {
  absl::flat_hash_set<int> optics_set;
  absl::flat_hash_map<std::string, std::string>
      transceiver_to_ethernet_pmd_type_map, transceiver_to_form_factor_map;
  ASSIGN_OR_RETURN(transceiver_to_ethernet_pmd_type_map,
                   pins_test::GetTransceiverToEthernetPmdMap(sut_gnmi_stub));
  ASSIGN_OR_RETURN(transceiver_to_form_factor_map,
                   pins_test::GetTransceiverToFormFactorMap(sut_gnmi_stub));
  for (const auto& [xcvr_name, form_factor] : transceiver_to_form_factor_map) {
    if (!absl::StrContains(form_factor, "OSFP")) {
      // Skip non-OSFP transceivers.
      continue;
    }

    int xcvr_num;
    if (!absl::SimpleAtoi(xcvr_name.substr(kEthernetLen), &xcvr_num)) {
      return gutil::InternalErrorBuilder().LogError()
             << "Failed to parse transceiver number in " << xcvr_name;
    }

    if (!transceiver_to_ethernet_pmd_type_map.contains(xcvr_name)) {
      return gutil::InternalErrorBuilder().LogError()
             << "Transceiver pmd type not found for " << xcvr_name;
    }

    std::string ethernet_pmd = transceiver_to_ethernet_pmd_type_map[xcvr_name];
    if (absl::StrContains(ethernet_pmd, "_CR")) {
      // Skip coppers. ETH_2X400GBASE_CR4 and ETH_400GBASE_CR8 are coppers.
      continue;
    }
    optics_set.insert(xcvr_num);
  }
  return optics_set;
}

absl::StatusOr<absl::flat_hash_map<int, std::vector<std::string>>>
GetXcvrToInterfacesMapGivenPmdType(gnmi::gNMI::StubInterface& sut_gnmi_stub,
                                   absl::string_view pmd_type) {
  absl::flat_hash_map<int, std::vector<std::string>> xcvr_to_interfaces_map;
  absl::flat_hash_map<std::string, std::string> interface_to_transceiver_map,
      transceiver_to_ethernet_pmd_type_map;
  ASSIGN_OR_RETURN(interface_to_transceiver_map,
                   pins_test::GetInterfaceToTransceiverMap(sut_gnmi_stub));
  ASSIGN_OR_RETURN(transceiver_to_ethernet_pmd_type_map,
                   pins_test::GetTransceiverToEthernetPmdMap(sut_gnmi_stub));
  for (const auto& [interface, xcvr_name] : interface_to_transceiver_map) {
    if (!transceiver_to_ethernet_pmd_type_map.contains(xcvr_name)) {
      // Skip the interfaces that doesn't have PMD types.
      continue;
    }
    std::string ethernet_pmd = transceiver_to_ethernet_pmd_type_map[xcvr_name];
    // Check suffix.
    if (absl::EndsWith(ethernet_pmd, pmd_type)) {
      int xcvr_num;
      if (!absl::SimpleAtoi(xcvr_name.substr(kEthernetLen), &xcvr_num)) {
        return gutil::InternalErrorBuilder().LogError()
               << "Failed to parse transceiver number in " << xcvr_name;
      }
      xcvr_to_interfaces_map[xcvr_num].push_back(interface);
    }
  }
  return xcvr_to_interfaces_map;
}

absl::StatusOr<bool> IsSfpPlusPort(gnmi::gNMI::StubInterface& sut_gnmi_stub,
                                   absl::string_view port_name) {
  absl::flat_hash_map<std::string, std::string> interface_to_transceiver_map,
      transceiver_to_ethernet_pmd_type_map;
  ASSIGN_OR_RETURN(interface_to_transceiver_map,
                   pins_test::GetInterfaceToTransceiverMap(sut_gnmi_stub));
  ASSIGN_OR_RETURN(transceiver_to_ethernet_pmd_type_map,
                   pins_test::GetTransceiverToEthernetPmdMap(sut_gnmi_stub));
  if (!interface_to_transceiver_map.contains(port_name)) {
    return gutil::InternalErrorBuilder().LogError()
           << "Interface " << port_name
           << " not found in interfaces to transceiver map";
  }
  if (!transceiver_to_ethernet_pmd_type_map.contains(
          interface_to_transceiver_map[port_name])) {
    return gutil::InternalErrorBuilder().LogError()
           << "Transceiver not found for interface " << port_name;
  }
  return absl::StrContains(transceiver_to_ethernet_pmd_type_map
                               [interface_to_transceiver_map[port_name]],
                           "LR");
}

absl::StatusOr<RandomPortBreakoutInfo> GetRandomPortWithSupportedBreakoutModes(
    gnmi::gNMI::StubInterface& sut_gnmi_stub,
    const std::string& platform_json_contents,
    const BreakoutType new_breakout_type,
    const BreakoutType current_breakout_type,
    const std::vector<absl::string_view>& allow_list) {
  // Get map of front panel port to oper-status on the switch.
  absl::flat_hash_map<std::string, std::string> interface_to_oper_status_map;
  ASSIGN_OR_RETURN(
      interface_to_oper_status_map,
      GetInterfaceToOperStatusMapOverGnmi(sut_gnmi_stub,
                                          /*timeout=*/absl::Seconds(60)),
      _ << "Failed to get oper-status map for ports on switch");
  // Consider only ports from provided list.
  std::vector<absl::string_view> port_list;
  if (!allow_list.empty()) {
    port_list = allow_list;
  } else {
    // Use all available ports if allow list is empty.
    for (auto& [intf, oper_status] : interface_to_oper_status_map) {
      port_list.push_back(intf);
    }
  }
  if (port_list.empty()) {
    return gutil::InternalErrorBuilder().LogError()
           << "No ports found on switch";
  }

  // Consider only ports that have p4rt ID modelled as this ID is required to
  // configure P4RT router interface on the port.
  ASSIGN_OR_RETURN(auto port_id_by_interface,
                   GetAllInterfaceNameToPortId(sut_gnmi_stub),
                   _ << "Failed to get interface name to p4rt id map");

  // Get interfaces from platform.json.
  const auto platform_json = json::parse(platform_json_contents);
  const auto interfaces_json = platform_json.find(kInterfaces);
  if (interfaces_json == platform_json.end()) {
    return gutil::InternalErrorBuilder().LogError()
           << absl::StrCat("Interfaces not found in platform.json");
  }

  // Get a random port.
  unsigned int seed = time(NULL);
  RandomPortBreakoutInfo port_info;
  absl::flat_hash_set<int> already_tried_port_indices;
  while (already_tried_port_indices.size() < port_list.size()) {
    int index = rand_r(&seed) % port_list.size();
    while (already_tried_port_indices.contains(index)) {
      index = (index + 1) % port_list.size();
    }
    already_tried_port_indices.insert(index);
    absl::string_view port = port_list[index];
    port_info.port_name = port;

    // Check if port has a p4rt id value in the state path.
    if (!port_id_by_interface.contains(port_info.port_name)) {
      continue;
    }

    // Consider only operationally up front panel parent ports.
    if (!absl::StartsWith(port_info.port_name, kEthernet)) {
      continue;
    } else {
      ASSIGN_OR_RETURN(const auto is_parent, IsParentPort(port_info.port_name));
      if (!is_parent ||
          interface_to_oper_status_map.contains(port_info.port_name) == 0 ||
          interface_to_oper_status_map.at(port_info.port_name) == kStateDown) {
        continue;
      }
    }

    // Skip SFP+ ports as breakout is not applicable to them.
    ASSIGN_OR_RETURN(const bool is_sfpp_port,
                     IsSfpPlusPort(sut_gnmi_stub, port));
    if (is_sfpp_port) {
      LOG(INFO) << "Skipping SFP+ port " << port;
      continue;
    }

    // Get the port entry from platform.json interfaces info.
    const auto interface_json = interfaces_json->find(port);
    if (interface_json == interfaces_json->end()) {
      return gutil::InternalErrorBuilder().LogError() << absl::InternalError(
                 absl::StrCat(port, " entry not found in platform.json"));
    }
    // Get current breakout mode for the port.
    ASSIGN_OR_RETURN(
        auto curr_breakout_mode,
        GetCurrentBreakoutModeForPort(sut_gnmi_stub, port_info.port_name));
    port_info.curr_breakout_mode = curr_breakout_mode;

    // Skip the port if it does not have the required breakout type for the
    // currently configure breakout mode.
    if (current_breakout_type == kChannelized) {
      ASSIGN_OR_RETURN(auto is_channelized,
                       IsChannelizedBreakoutMode(curr_breakout_mode));
      if (!is_channelized) {
        continue;
      }
    }
    // Get supported breakout modes based on breakout type for the port.
    ASSIGN_OR_RETURN(
        auto supported_breakout_modes,
        GetSupportedBreakoutModesForPort(interface_json->dump(), port,
                                         new_breakout_type),
        _ << "Breakout modes not found for " << port << " in platform.json");

    // Get a supported breakout mode other than current breakout mode.
    for (const auto& supported_breakout_mode : supported_breakout_modes) {
      if (supported_breakout_mode != port_info.curr_breakout_mode) {
        // Check if new breakout mode would result in a speed change only.
        ASSIGN_OR_RETURN(auto speed_change_only,
                         BreakoutResultsInSpeedChangeOnly(
                             port_info.port_name, port_info.curr_breakout_mode,
                             supported_breakout_mode));
        if (!speed_change_only) {
          port_info.supported_breakout_mode = supported_breakout_mode;
          StripSymbolFromString(port_info.supported_breakout_mode, '\"');
          break;
        }
      }
    }
    if (!port_info.supported_breakout_mode.empty()) {
      return port_info;
    }
  }
  return gutil::InternalErrorBuilder().LogError()
         << "No random interface with supported breakout modes found";
}

absl::StatusOr<SlotPortLane> GetSlotPortLaneForPort(
    const absl::string_view port) {
  if (!absl::StartsWith(port, kEthernet)) {
    return absl::InvalidArgumentError(
        absl::StrCat("Requested port (", port, ") is not a front panel port"));
  }
  auto slot_port_lane_str = port.substr(kEthernetLen);
  std::vector<std::string> values = absl::StrSplit(slot_port_lane_str, '/');
  if (values.size() < kSlotPortLaneMinValues) {
    return absl::InvalidArgumentError(absl::StrCat(
        "Requested port (", port,
        ") does not have a valid format (EthernetX/Y/Z or EthernetX/Y)"));
  }
  SlotPortLane slot_port_lane;
  if (!absl::SimpleAtoi(values[kSlotIndex], &slot_port_lane.slot)) {
    return gutil::InternalErrorBuilder().LogError()
           << "Failed to convert string (" << values[kSlotIndex]
           << ") to integer";
  }
  if (!absl::SimpleAtoi(values[kPortIndex], &slot_port_lane.port)) {
    return gutil::InternalErrorBuilder().LogError()
           << "Failed to convert string (" << values[kPortIndex]
           << ") to integer";
  }
  // Unchannelizable ports will not contain a lane number.
  // Use default lane number of 1.
  slot_port_lane.lane = 1;
  if (values.size() == kSlotPortLaneMaxValues) {
    if (!absl::SimpleAtoi(values[kLaneIndex], &slot_port_lane.lane)) {
      return gutil::InternalErrorBuilder().LogError()
             << "Failed to convert string (" << values[kLaneIndex]
             << ") to integer";
    }
  }
  return slot_port_lane;
}

// TODO: Remove port naming dependent logic.
absl::StatusOr<absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>>
GetExpectedPortInfoForBreakoutMode(const std::string& port,
                                   absl::string_view breakout_mode) {
  if (breakout_mode.empty()) {
    return gutil::InternalErrorBuilder().LogError()
           << "Found empty breakout mode";
  }
  ASSIGN_OR_RETURN(auto is_parent, IsParentPort(port));
  if (!is_parent) {
    return gutil::InternalErrorBuilder().LogError()
           << "Requested port (" << port << ") is not a parent port";
  }

  // For a mixed breakout mode, get "+" separated breakout groups.
  // Eg. For a mixed breakout mode of "2x100G(4) + 1x200G(4)"; modes =
  // {2x100G(4), 1x200G(4)}
  std::vector<std::string> modes = absl::StrSplit(breakout_mode, '+');
  // Get maximum physical channels in a breakout group which is max
  // lanes per physical port/number of groups in a breakout mode.
  auto max_channels_in_group = kMaxPortLanes / modes.size();
  ASSIGN_OR_RETURN(auto slot_port_lane, GetSlotPortLaneForPort(port));
  auto current_physical_channel = 0;
  auto curr_lane_number = 1;
  absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>
      expected_breakout_info;
  for (auto& mode : modes) {
    // Strip quotes from breakout mode string.
    StripSymbolFromString(mode, '\"');
    std::vector<std::string> values = absl::StrSplit(mode, 'x');
    if (values.size() != 2) {
      return gutil::InternalErrorBuilder().LogError()
             << "Invalid breakout mode found: " << mode;
    }
    int num_breakouts;
    if (!absl::SimpleAtoi(values[0], &num_breakouts)) {
      return gutil::InternalErrorBuilder().LogError()
             << "Failed to convert string (" << values[0] << ") to integer";
    }
    auto breakout_speed = values[1].substr(0, values[1].find('('));

    // For each resulting interface, construct the front panel interface name
    // using offset from the parent port. For a breakout mode of Ethernet1/1/1
    // => 2x100(4)G+1x200G(4), the max channels per group would be 4 (8 max
    // lanes per port/2 groups). Hence, breakout mode 2x100G (numBreakouts=2)
    // would have an offset of 2 and 1x200G(numBreakouts=1) would have an offset
    // of 1 leading to interfaces Ethernet1/1/1, Ethernet1/1/3 for mode 2x100G
    // and Ethernet1/1/5 for mode 1x200G.
    for (int i = 0; i < num_breakouts; i++) {
      auto port =
          absl::StrCat(kEthernet, slot_port_lane.slot, "/", slot_port_lane.port,
                       "/", std::to_string(curr_lane_number));
      // Populate expected physical channels for each port.
      // Physical channels are between 0 to 7.
      int offset = max_channels_in_group / num_breakouts;
      if (max_channels_in_group % num_breakouts != 0) {
        return gutil::InternalErrorBuilder().LogError()
               << "Invalid breakout mode (" << breakout_mode << ") found";
      }
      std::string physical_channels = "[";
      for (int j = current_physical_channel;
           j < offset + current_physical_channel; j++) {
        physical_channels += std::to_string(j);
        // Add comma after each but last entry.
        if (j < offset + current_physical_channel - 1) physical_channels += ",";
      }
      physical_channels += "]";
      current_physical_channel += offset;
      curr_lane_number += offset;
      PortBreakoutInfo current_breakout_info;
      current_breakout_info.physical_channels = physical_channels;
      current_breakout_info.breakout_speed = breakout_speed;
      expected_breakout_info[port] = current_breakout_info;
    }
  }
  return expected_breakout_info;
}

absl::StatusOr<absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>>
GetBreakoutStateInfoForPort(gnmi::gNMI::StubInterface* sut_gnmi_stub,
                            const std::string& port,
                            absl::string_view breakout_mode) {
  // Check port exists on the switch.
  ASSIGN_OR_RETURN(
      auto interface_to_oper_status_map,
      GetInterfaceToOperStatusMapOverGnmi(*sut_gnmi_stub, absl::Seconds(60)));

  absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo> port_infos;
  ASSIGN_OR_RETURN(port_infos,
                   GetExpectedPortInfoForBreakoutMode(port, breakout_mode));
  std::vector<std::string> skipped_ports;
  for (auto& [port_name, breakout_info] : port_infos) {
    // Current port is not on switch, skip.
    if (!interface_to_oper_status_map.contains(port_name)) {
      skipped_ports.push_back(port_name);
      continue;
    }
    auto if_state_path = absl::StrCat("interfaces/interface[name=", port_name,
                                      "]/state/oper-status");
    auto resp_parse_str = "openconfig-interfaces:oper-status";
    ASSIGN_OR_RETURN(
        auto state_path_response,
        GetGnmiStatePathInfo(sut_gnmi_stub, if_state_path, resp_parse_str),
        _ << "Failed to get GNMI state path value for oper-status for "
             "port "
          << port_name);
    breakout_info.oper_status = state_path_response;

    auto if_physical_channels_path = absl::StrCat(
        "interfaces/interface[name=", port_name, "]/state/physical-channel");
    resp_parse_str = "openconfig-platform-transceiver:physical-channel";
    ASSIGN_OR_RETURN(
        state_path_response,
        GetGnmiStatePathInfo(sut_gnmi_stub, if_physical_channels_path,
                             resp_parse_str),
        _ << "Failed to get GNMI state path value for physical-channels for "
             "port "
          << port_name);
    breakout_info.physical_channels = state_path_response;
  }
  for (const std::string& skipped_port : skipped_ports) {
    port_infos.erase(skipped_port);
  }
  return port_infos;
}

absl::StatusOr<std::string> GenerateComponentBreakoutConfig(
    absl::string_view breakout_speed, int index, int num_breakouts,
    absl::string_view num_physical_channels) {
  auto component_config = absl::Substitute(
      R"pb({
             "config": {
               "breakout-speed": "openconfig-if-ethernet:SPEED_$0B",
               "index": $1,
               "num-breakouts": $2,
               "num-physical-channels": $3
             },
             "index": $1
           })pb",
      breakout_speed, index, num_breakouts, num_physical_channels);
  return component_config;
}

absl::StatusOr<bool> IsCopperPort(gnmi::gNMI::StubInterface* sut_gnmi_stub,
                                  absl::string_view port) {
  // Get transceiver name for the port.
  auto state_path =
      absl::StrFormat("interfaces/interface[name=%s]/state/transceiver", port);
  auto resp_parse_str = "openconfig-platform-transceiver:transceiver";
  ASSIGN_OR_RETURN(
      auto xcvrd_name,
      GetGnmiStatePathInfo(sut_gnmi_stub, state_path, resp_parse_str),
      _ << "Failed to get GNMI state path value for port transceiver for "
           "port "
        << port);
  StripSymbolFromString(xcvrd_name, '\"');

  state_path = absl::StrFormat(
      "components/component[name=%s]/transceiver/state/ethernet-pmd",
      xcvrd_name);
  resp_parse_str = "openconfig-platform-transceiver:ethernet-pmd";
  ASSIGN_OR_RETURN(
      auto ethernet_pmd,
      GetGnmiStatePathInfo(sut_gnmi_stub, state_path, resp_parse_str),
      _ << "Failed to get GNMI state path value for ethernet-pmd for "
           "port "
        << port);
  StripSymbolFromString(ethernet_pmd, '\"');

  // PMD state path value for copper ports ends in CR2/CR4/CR8.
  auto pos = ethernet_pmd.find_last_of('_');
  return (ethernet_pmd.substr(pos + 1, 2) == "CR");
}

absl::StatusOr<uint32_t> ComputePortIDForPort(
    gnmi::gNMI::StubInterface* sut_gnmi_stub, absl::string_view port) {
  // Try to get currently configured id for the port from the switch.
  std::string if_state_path =
      absl::StrCat("interfaces/interface[name=", port, "]/state/id");
  std::string resp_parse_str = "openconfig-interfaces:id";
  uint32_t id;
  auto state_path_response =
      GetGnmiStatePathInfo(sut_gnmi_stub, if_state_path, resp_parse_str);
  if (state_path_response.ok() && !state_path_response.value().empty()) {
    if (!absl::SimpleAtoi(state_path_response.value(), &id)) {
      return gutil::InternalErrorBuilder().LogError()
             << "Failed to convert string (" << state_path_response.value()
             << ") to integer";
    }
    return id;
  }
  // Generate ID same as that used by controller, if not found on switch.
  ASSIGN_OR_RETURN(auto is_parent, IsParentPort(port));
  ASSIGN_OR_RETURN(auto slot_port_lane, GetSlotPortLaneForPort(port));
  // Port ID is same as port index/parent port number for parent ports.
  if (is_parent) {
    return slot_port_lane.port;
  }
  // Port ID is computed for child ports using
  // (laneIndex*512 + parentPortNumber + 1)
  return (slot_port_lane.lane * 512 + slot_port_lane.port + 1);
}

absl::StatusOr<std::string> GenerateInterfaceBreakoutConfig(
    gnmi::gNMI::StubInterface* sut_gnmi_stub, absl::string_view port,
    absl::string_view breakout_speed, const bool is_copper_port) {
  ASSIGN_OR_RETURN(auto id, ComputePortIDForPort(sut_gnmi_stub, port));
  auto interface_config = absl::Substitute(
      R"pb({
             "config": {
               "enabled": true,
               "loopback-mode": "NONE",
               "mtu": 9216,
               "name": "$0",
               "type": "iana-if-type:ethernetCsmacd",
               "openconfig-p4rt:id": $2
             },
             "name": "$0",
             "openconfig-if-ethernet:ethernet": {
               "config": { "port-speed": "openconfig-if-ethernet:SPEED_$1B" }
             },
             "subinterfaces": {
               "subinterface":
               [ {
                 "config": { "index": 0 },
                 "index": 0,
                 "openconfig-if-ip:ipv6": {
                   "unnumbered": { "config": { "enabled": true } }
                 }
               }]
             }
           }
      )pb",
      port, breakout_speed, id);
  if (is_copper_port) {
    interface_config = absl::Substitute(
        R"pb({
               "config": {
                 "enabled": true,
                 "loopback-mode": "NONE",
                 "mtu": 9216,
                 "name": "$0",
                 "type": "iana-if-type:ethernetCsmacd",
                 "openconfig-p4rt:id": $2
               },
               "name": "$0",
               "openconfig-if-ethernet:ethernet": {
                 "config": {
                   "port-speed": "openconfig-if-ethernet:SPEED_$1B",
                   "standalone-link-training": true
                 }
               },
               "subinterfaces": {
                 "subinterface":
                 [ {
                   "config": { "index": 0 },
                   "index": 0,
                   "openconfig-if-ip:ipv6": {
                     "unnumbered": { "config": { "enabled": true } }
                   }
                 }]
               }
             }
        )pb",
        port, breakout_speed, id);
  }
  return interface_config;
}

// TODO: Remove port naming dependent logic.
absl::StatusOr<std::string> GetBreakoutModeConfigJson(
    gnmi::gNMI::StubInterface* sut_gnmi_stub,
    const absl::string_view port_index, const absl::string_view intf_name,
    const absl::string_view breakout_mode) {
  std::string kBreakoutPath = absl::StrCat("components/component[name=1/",
                                           port_index, "]/port/breakout-mode");
  // Get breakout groups corresponding to breakout mode.
  // For a mixed breakout mode, get "+" separated breakout groups.
  // Eg. For a mixed breakout mode of "2x100G(4) + 1x200G(4)"; modes =
  // {2x100G(4), 1x200G(4)}
  std::vector<std::string> modes = absl::StrSplit(breakout_mode, '+');
  std::vector<std::string> group_configs;
  std::vector<std::string> interface_configs;
  auto max_channels_in_group = kMaxPortLanes / modes.size();
  auto index = 0;

  // Get current port number.
  ASSIGN_OR_RETURN(auto slot_port_lane, GetSlotPortLaneForPort(intf_name));
  ASSIGN_OR_RETURN(bool is_copper_port, IsCopperPort(sut_gnmi_stub, intf_name));
  auto curr_lane_number = 1;
  for (const auto& mode : modes) {
    auto num_breakouts_str = mode.substr(0, mode.find('x'));
    int num_breakouts;
    if (!absl::SimpleAtoi(num_breakouts_str, &num_breakouts)) {
      return gutil::InternalErrorBuilder().LogError()
             << "Failed to convert string (" << num_breakouts_str
             << ") to integer";
    }
    auto xpos = mode.find('x');
    auto breakout_speed = mode.substr(xpos + 1, mode.find('(') - xpos - 1);
    auto num_physical_channels = max_channels_in_group / num_breakouts;
    ASSIGN_OR_RETURN(
        auto group_config,
        GenerateComponentBreakoutConfig(breakout_speed, index, num_breakouts,
                                        std::to_string(num_physical_channels)));
    group_configs.push_back(group_config);

    // Get the interface config for all ports corresponding to current breakout
    // group.
    for (int i = 0; i < num_breakouts; i++) {
      auto port =
          absl::StrCat(kEthernet, slot_port_lane.slot, "/", slot_port_lane.port,
                       "/", std::to_string(curr_lane_number));
      ASSIGN_OR_RETURN(
          auto interface_config,
          GenerateInterfaceBreakoutConfig(sut_gnmi_stub, port, breakout_speed,
                                          is_copper_port));
      interface_configs.push_back(interface_config);
      int offset = max_channels_in_group / num_breakouts;
      curr_lane_number += offset;
    }
    index += 1;
  }

  std::string full_component_config = absl::StrJoin(group_configs, ",");
  std::string full_interface_config = absl::StrJoin(interface_configs, ",");

  return absl::Substitute(
      R"pb({
             "openconfig-interfaces:interfaces": { "interface": [ $0 ] },
             "openconfig-platform:components": {
               "component":
               [ {
                 "name": "$1",
                 "config": { "name": "$1" },
                 "port": {
                   "config": { "port-id": $2 },
                   "breakout-mode": { "groups": { "group": [ $3 ] } }
                 }
               }]
             }
           })pb",
      full_interface_config, absl::StrCat("1/", port_index), port_index,
      full_component_config);
}

absl::Status GetBreakoutModeConfigFromString(
    gnmi::SetRequest& req, gnmi::gNMI::StubInterface* sut_gnmi_stub,
    const absl::string_view port_index, const absl::string_view intf_name,
    const absl::string_view breakout_mode) {
  ASSIGN_OR_RETURN(auto config,
                   GetBreakoutModeConfigJson(sut_gnmi_stub, port_index,
                                             intf_name, breakout_mode));
  // Build GNMI config set request for given port breakout mode.
  ASSIGN_OR_RETURN(req, BuildGnmiSetRequest("", GnmiSetType::kReplace, config));
  return absl::OkStatus();
}

std::vector<std::string> GetNonExistingPortsAfterBreakout(
    const absl::flat_hash_map<std::string, PortBreakoutInfo>&
        original_port_info,
    const absl::flat_hash_map<std::string, PortBreakoutInfo>& new_port_info,
    bool expected_success) {
  std::vector<std::string> non_existing_ports;
  const auto* original_map = &original_port_info;
  const auto* new_map = &new_port_info;

  if (!expected_success) {
    original_map = &new_port_info;
    new_map = &original_port_info;
  }
  for (const auto& [port_name, unused] : *original_map) {
    if (new_map->find(port_name) == new_map->end()) {
      non_existing_ports.push_back(port_name);
    }
  }
  return non_existing_ports;
}

absl::Status ValidateBreakoutState(
    gnmi::gNMI::StubInterface* sut_gnmi_stub,
    const absl::flat_hash_map<std::string, PortBreakoutInfo>&
        expected_port_info,
    const std::vector<std::string>& non_existing_ports_list) {
  if (expected_port_info.empty()) {
    return gutil::InternalErrorBuilder().LogError()
           << "Expected port info map is empty";
  }

  for (const auto& [port_name, breakout_info] : expected_port_info) {
    // Verify that the oper-status state path value is as expected.
    auto expected_oper_status = breakout_info.oper_status;
    StripSymbolFromString(expected_oper_status, '\"');
    RETURN_IF_ERROR(pins_test::CheckInterfaceOperStateOverGnmi(
        *sut_gnmi_stub, expected_oper_status, {port_name}));
    // Verify that the physical-channels state path value is as expected.
    auto interface_state_path = absl::StrCat(
        "interfaces/interface[name=", port_name, "]/state/physical-channel");
    auto response_parse_str =
        "openconfig-platform-transceiver:physical-channel";
    ASSIGN_OR_RETURN(
        auto state_path_response,
        GetGnmiStatePathInfo(sut_gnmi_stub, interface_state_path,
                             response_parse_str),
        _ << "Failed to get GNMI state path value for physical-channels for "
             "port "
          << port_name);
    if (!absl::StrContains(state_path_response,
                           breakout_info.physical_channels)) {
      return gutil::InternalErrorBuilder().LogError()
             << absl::StrCat("Physical channel match failed for port ",
                             port_name, ". got: ", state_path_response,
                             ", want: ", breakout_info.physical_channels);
    }
  }

  // Verify that ports that are not expected to be existing do not exist.
  for (const auto& port : non_existing_ports_list) {
    auto if_state_path =
        absl::StrCat("interfaces/interface[name=", port, "]/state/oper-status");
    auto resp_parse_str = "openconfig-interfaces:oper-status";
    auto state_path_response =
        GetGnmiStatePathInfo(sut_gnmi_stub, if_state_path, resp_parse_str);
    if (state_path_response.status() == absl::OkStatus()) {
      return gutil::InternalErrorBuilder().LogError()
             << absl::StrCat("Unexpected port (", port,
                             ") found after application of breakout mode");
    }
  }
  return absl::OkStatus();
}

absl::StatusOr<std::string> GetPortIndex(
    absl::string_view platform_json_contents, absl::string_view port) {
  // Get interfaces from platform.json.
  const auto platform_json = json::parse(platform_json_contents);
  const auto interfaces_json = platform_json.find(kInterfaces);
  if (interfaces_json == platform_json.end()) {
    return gutil::InternalErrorBuilder().LogError()
           << absl::StrCat("Interfaces not found in platform.json");
  }
  // Get the port entry from platform.json interfaces info.
  const auto interface_json = interfaces_json->find(port);
  if (interface_json == interfaces_json->end()) {
    return gutil::InternalErrorBuilder().LogError() << absl::InternalError(
               absl::StrCat(port, " entry not found in platform.json"));
  }
  // Get index for the port.
  const auto index = interface_json->find("index");
  if (index == interface_json->end()) {
    return gutil::InternalErrorBuilder().LogError() << absl::InternalError(
               absl::StrCat("Index not found for ", port, " in platform.json"));
  }
  auto port_index = index->dump();
  StripSymbolFromString(port_index, '\"');
  return port_index.substr(0, port_index.find(','));
}

// TODO: Remove port naming dependent logic.
absl::StatusOr<bool> IsParentPort(absl::string_view port) {
  ASSIGN_OR_RETURN(auto slot_port_lane, GetSlotPortLaneForPort(port));
  // Lane number for a master port is always 1.
  return slot_port_lane.lane == 1;
}

// Returns an EK_PHYSICAL_PORT name given an EK_PORT name.
absl::StatusOr<std::string> DeriveEkPhysicalPort(absl::string_view ek_port) {
  int slot;
  int port;
  RET_CHECK(RE2::FullMatch(ek_port, R"(\w+(\d+)\/(\d+)(\/\d+)*)", &slot, &port))
      << "no match found for " << ek_port;
  return absl::StrCat("phy-", slot, "/", port);
}
}  // namespace pins_test
