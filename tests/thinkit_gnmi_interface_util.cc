#include "tests/thinkit_gnmi_interface_util.h"

#include <grp.h>

#include <algorithm>
#include <cstddef>
#include <cstdlib>
#include <ostream>
#include <string>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/str_replace.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "include/nlohmann/json.hpp"
#include "lib/gnmi/gnmi_helper.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
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
    const std::string& interface_info, const std::string& port,
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
  int i = 0, pos = 0;
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
      if ((num_breakouts > 1) || absl::StrContains(mode, "+")) {
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

absl::StatusOr<RandomPortBreakoutInfo> GetRandomPortWithSupportedBreakoutModes(
    gnmi::gNMI::StubInterface& sut_gnmi_stub,
    const std::string& platform_json_contents,
    const BreakoutType breakout_type) {
  // Get map of front panel port to oper-status on the switch.
  ASSIGN_OR_RETURN(
      auto interface_to_oper_status_map,
      GetInterfaceToOperStatusMapOverGnmi(sut_gnmi_stub,
                                          /*timeout=*/absl::Seconds(60)),
      _ << "Failed to get oper-status map for ports on switch");

  // Consider only ports that have p4rt ID modelled as this ID is required to
  // configure P4RT router interface on the port.
  ASSIGN_OR_RETURN(auto port_id_by_interface,
                   GetAllInterfaceNameToPortId(sut_gnmi_stub),
                   _ << "Failed to get interface name to p4rt id map");

  // Consider only operationally up front panel parent ports.
  std::vector<std::string> up_parent_port_list;
  for (auto& intf : interface_to_oper_status_map) {
    if (absl::StartsWith(intf.first, kEthernet)) {
      ASSIGN_OR_RETURN(std::vector<std::string> slot_port_lane,
                       GetSlotPortLaneForPort(intf.first));
      int curr_lane_number;
      if (!absl::SimpleAtoi(slot_port_lane[kLaneIndex], &curr_lane_number)) {
        return gutil::InternalErrorBuilder().LogError()
               << "Failed to convert string (" << slot_port_lane[kLaneIndex]
               << ") to integer";
      }
      if ((curr_lane_number == 1) && intf.second == kStateUp) {
        up_parent_port_list.push_back(intf.first);
      }
    }
  }
  if (up_parent_port_list.empty()) {
    return gutil::InternalErrorBuilder().LogError()
           << "No operationally up parent ports found on switch";
  }

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
  while (!up_parent_port_list.empty()) {
    // Randomly pick a port.
    auto index = rand_r(&seed) % up_parent_port_list.size();
    auto port = up_parent_port_list[index];
    port_info.port_name = port;

    // Check if port has a p4rt id value in the state path.
    if (!port_id_by_interface.count(port_info.port_name)) {
      up_parent_port_list.erase(up_parent_port_list.begin() + index);
      continue;
    }

    // Get the port entry from platform.json interfaces info.
    const auto interface_json = interfaces_json->find(port);
    if (interface_json == interfaces_json->end()) {
      return gutil::InternalErrorBuilder().LogError() << absl::InternalError(
                 absl::StrCat(port, " entry not found in platform.json"));
    }
    // Get default breakout mode for the port.
    const auto default_breakout_mode =
        interface_json->find("default_brkout_mode");
    if (default_breakout_mode == interface_json->end()) {
      return gutil::InternalErrorBuilder().LogError() << absl::InternalError(
                 absl::StrCat("Default breakout mode not found for ", port,
                              " in platform.json"));
    }
    port_info.curr_breakout_mode = default_breakout_mode->dump();
    StripSymbolFromString(port_info.curr_breakout_mode, '\"');

    // Get supported breakout modes based on breakout type for the port.
    ASSIGN_OR_RETURN(
        auto supported_breakout_modes,
        GetSupportedBreakoutModesForPort(interface_json->dump(), port,
                                         breakout_type),
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
      break;
    }
    // Remove port from list.
    up_parent_port_list.erase(up_parent_port_list.begin() + index);
  }
  if (up_parent_port_list.empty()) {
    return gutil::InternalErrorBuilder().LogError()
           << "No random interface with supported breakout modes found";
  }
  return port_info;
}

absl::StatusOr<std::vector<std::string>> GetSlotPortLaneForPort(
    const absl::string_view port) {
  if (!absl::StartsWith(port, kEthernet)) {
    return absl::InvalidArgumentError(
        absl::StrCat("Requested port (", port, ") is not a front panel port"));
  }
  auto slot_port_lane = port.substr(kEthernetLen);
  std::vector<std::string> values = absl::StrSplit(slot_port_lane, '/');
  if (values.size() != 3) {
    return absl::InvalidArgumentError(
        absl::StrCat("Requested port (", port,
                     ") does not have a valid format (EthernetX/Y/Z)"));
  }
  return values;
}

absl::StatusOr<absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>>
GetExpectedPortInfoForBreakoutMode(const std::string& port,
                                   absl::string_view breakout_mode) {
  if (breakout_mode.empty()) {
    return gutil::InternalErrorBuilder().LogError()
           << "Found empty breakout mode";
  }

  // For a mixed breakout mode, get "+" separated breakout groups.
  // Eg. For a mixed breakout mode of "2x100G(4) + 1x200G(4)"; modes =
  // {2x100G(4), 1x200G(4)}
  std::vector<std::string> modes = absl::StrSplit(breakout_mode, '+');
  // Get maximum physical channels in a breakout group which is max
  // lanes per physical port/number of groups in a breakout mode.
  auto max_channels_in_group = kMaxPortLanes / modes.size();
  ASSIGN_OR_RETURN(std::vector<std::string> slot_port_lane,
                   GetSlotPortLaneForPort(port));
  int curr_lane_number;
  if (!absl::SimpleAtoi(slot_port_lane[kLaneIndex], &curr_lane_number)) {
    return gutil::InternalErrorBuilder().LogError()
           << "Failed to convert string (" << slot_port_lane[kLaneIndex]
           << ") to integer";
  }
  // Lane number for a master port is always 1.
  if (curr_lane_number != 1) {
    return absl::InvalidArgumentError(
        absl::StrCat("Requested port (", port, ") is not a parent port"));
  }
  auto current_physical_channel = 0;
  absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>
      expected_breakout_info;
  for (auto& mode : modes) {
    // Strip quotes from breakout mode string.
    StripSymbolFromString(mode, '\"');
    std::vector<std::string> values = absl::StrSplit(mode, 'x');
    int num_breakouts;
    if (!absl::SimpleAtoi(values[0], &num_breakouts)) {
      return gutil::InternalErrorBuilder().LogError()
             << "Failed to convert string (" << values[0] << ") to integer";
    }

    // For each resulting interface, construct the front panel interface name
    // using offset from the parent port. For a breakout mode of Ethernet1/1/1
    // => 2x100(4)G+1x200G(4), the max channels per group would be 4 (8 max
    // lanes per port/2 groups). Hence, breakout mode 2x100G (numBreakouts=2)
    // would have an offset of 2 and 1x200G(numBreakouts=1) would have an offset
    // of 1 leading to interfaces Ethernet1/1/1, Ethernet1/1/3 for mode 2x100G
    // and Ethernet1/1/5 for mode 1x200G.
    for (int i = 0; i < num_breakouts; i++) {
      auto port = absl::StrCat(kEthernet, slot_port_lane[kSlotIndex], "/",
                               slot_port_lane[kPortIndex], "/",
                               std::to_string(curr_lane_number));
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
      expected_breakout_info[port] = PortBreakoutInfo{physical_channels};
    }
  }
  return expected_breakout_info;
}

absl::StatusOr<absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>>
GetBreakoutStateInfoForPort(gnmi::gNMI::StubInterface* sut_gnmi_stub,
                            const std::string& port,
                            absl::string_view breakout_mode) {
  absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo> port_infos;
  ASSIGN_OR_RETURN(port_infos,
                   GetExpectedPortInfoForBreakoutMode(port, breakout_mode));
  for (auto& [port_name, breakout_info] : port_infos) {
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
      absl::StrCat("interfaces/interface[name=", port, "]/state/transceiver");
  auto resp_parse_str = "openconfig-platform-transceiver:transceiver";
  ASSIGN_OR_RETURN(
      auto xcvrd_name,
      GetGnmiStatePathInfo(sut_gnmi_stub, state_path, resp_parse_str),
      _ << "Failed to get GNMI state path value for port transceiver for "
           "port "
        << port);
  StripSymbolFromString(xcvrd_name, '\"');

  // TODO: Replace with PMD type when supported.
  // Get cable length for the port transceiver.
  state_path =
      absl::StrCat("components/component[name=", xcvrd_name,
                   "]/transceiver/state/openconfig-platform-ext:cable-length");
  resp_parse_str = "openconfig-platform-ext:cable-length";
  ASSIGN_OR_RETURN(
      auto cable_length_str,
      GetGnmiStatePathInfo(sut_gnmi_stub, state_path, resp_parse_str),
      _ << "Failed to get GNMI state path value for cable-length for "
           "port "
        << port);
  StripSymbolFromString(cable_length_str, '\"');

  // Only cable lengths of copper ports are a positive value.
  float cable_length;
  if (!absl::SimpleAtof(cable_length_str, &cable_length)) {
    return gutil::InternalErrorBuilder().LogError()
           << "Failed to convert string (" << cable_length_str << ") to float";
  }
  return (cable_length > 0);
}

absl::StatusOr<std::string> GenerateInterfaceBreakoutConfig(
    absl::string_view port, const int id, absl::string_view breakout_speed,
    const bool is_copper_port) {

  auto interface_config = absl::Substitute(
      R"pb({
             "config": {
               "enabled": true,
               "loopback-mode": false,
               "mtu": 9216,
               "name": "$0",
               "type": "iana-if-type:ethernetCsmacd"
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
      port, breakout_speed);
  if (is_copper_port) {
    interface_config = absl::Substitute(
        R"pb({
               "config": {
                 "enabled": true,
                 "loopback-mode": false,
                 "mtu": 9216,
                 "name": "$0",
                 "type": "iana-if-type:ethernetCsmacd"
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
        port, breakout_speed);
  }
  return interface_config;
}

absl::Status GetBreakoutModeConfigFromString(
    gnmi::SetRequest& req, gnmi::gNMI::StubInterface* sut_gnmi_stub,
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
  ASSIGN_OR_RETURN(std::vector<std::string> slot_port_lane,
                   GetSlotPortLaneForPort(intf_name));
  int curr_lane_number;
  if (!absl::SimpleAtoi(slot_port_lane[kLaneIndex], &curr_lane_number)) {
    return gutil::InternalErrorBuilder().LogError()
           << "Failed to convert string (" << slot_port_lane[kLaneIndex]
           << ") to integer";
  }
  ASSIGN_OR_RETURN(bool is_copper_port, IsCopperPort(sut_gnmi_stub, intf_name));

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
      auto port = absl::StrCat(kEthernet, slot_port_lane[kSlotIndex], "/",
                               slot_port_lane[kPortIndex], "/",
                               std::to_string(curr_lane_number));
      ASSIGN_OR_RETURN(
          auto interface_config,
          GenerateInterfaceBreakoutConfig(port, curr_lane_number,
                                          breakout_speed, is_copper_port));
      interface_configs.push_back(interface_config);
      int offset = max_channels_in_group / num_breakouts;
      curr_lane_number += offset;
    }
    index += 1;
  }

  std::string full_component_config = absl::StrJoin(group_configs, ",");
  std::string full_interface_config = absl::StrJoin(interface_configs, ",");

  auto kBreakoutConfig = absl::Substitute(
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
  // Build GNMI config set request for given port breakout mode.
  ASSIGN_OR_RETURN(
      req, BuildGnmiSetRequest("", GnmiSetType::kReplace, kBreakoutConfig));
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
    auto interface_state_path = absl::StrCat(
        "interfaces/interface[name=", port_name, "]/state/oper-status");
    auto response_parse_str = "openconfig-interfaces:oper-status";
    ASSIGN_OR_RETURN(
        auto state_path_response,
        GetGnmiStatePathInfo(sut_gnmi_stub, interface_state_path,
                             response_parse_str),
        _ << "Failed to get GNMI state path value for oper-status for "
             "port "
          << port_name);
    if (!absl::StrContains(state_path_response, breakout_info.oper_status)) {
      return gutil::InternalErrorBuilder().LogError()
             << absl::StrCat("Port oper-status match failed for port ",
                             port_name, ". got: ", state_path_response,
                             ", want:", breakout_info.oper_status);
    }
    // Verify that the physical-channels state path value is as expected.
    interface_state_path = absl::StrCat("interfaces/interface[name=", port_name,
                                        "]/state/physical-channel");
    response_parse_str = "openconfig-platform-transceiver:physical-channel";
    ASSIGN_OR_RETURN(
        state_path_response,
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
    const std::string& platform_json_contents, absl::string_view port) {
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
}  // namespace pins_test
