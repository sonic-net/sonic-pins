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

void StripSymbolFromString(std::string& str, const char symbol) {
  str.erase(remove(str.begin(), str.end(), symbol), str.end());
}

std::string ConstructSupportedBreakoutMode(std::string& num_breakouts,
                                           std::string& breakout_speed) {
  StripSymbolFromString(num_breakouts, ' ');
  StripSymbolFromString(breakout_speed, ' ');
  return absl::StrCat(num_breakouts, "x", breakout_speed);
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
      // 1x200G+2x100G) or it results in more than one number of interfaces
      // (eg. 2x200G).
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

  // Consider only operationally up front panel parent ports.
  std::vector<std::string> up_parent_port_list;
  for (auto& intf : interface_to_oper_status_map) {
    if (absl::StartsWith(intf.first, kEthernet)) {
      auto port_number_str = intf.first.substr(kEthernetLen);
      int port_number;
      if (!absl::SimpleAtoi(port_number_str, &port_number)) {
        return gutil::InternalErrorBuilder().LogError()
               << "Failed to convert string (" << port_number_str
               << ") to integer";
      }
      if (((port_number % kMaxPortLanes) == 0) && intf.second == kStateUp) {
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
        port_info.supported_breakout_mode = supported_breakout_mode;
        StripSymbolFromString(port_info.supported_breakout_mode, '\"');
        break;
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

absl::StatusOr<absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>>
GetExpectedPortInfoForBreakoutMode(const std::string& port,
                                   absl::string_view breakout_mode) {
  if (breakout_mode.empty()) {
    return gutil::InternalErrorBuilder().LogError()
           << "Found empty breakout mode";
  }

  // For a mixed breakout mode, get "+" separated breakout groups.
  // Eg. For a mixed breakout mode of "2x100G + 1x200G"; modes = {2x100G,
  // 1x200G}
  std::vector<std::string> modes = absl::StrSplit(breakout_mode, '+');
  // Get maximum physical channels in a breakout group which is max
  // lanes per physical port/number of groups in a breakout mode.
  auto max_channels_in_group = kMaxPortLanes / modes.size();
  auto port_number_str = port.substr(kEthernetLen);
  int curr_port_number;
  if (!absl::SimpleAtoi(port_number_str, &curr_port_number)) {
    return gutil::InternalErrorBuilder().LogError()
           << "Failed to convert string (" << port_number_str << ") to integer";
  }
  if (curr_port_number % kMaxPortLanes != 0) {
    return gutil::InternalErrorBuilder().LogError()
           << "Requested port (" << port << ") is not a parent port";
  }

  auto curr_physical_channel = 0;
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
    // using offset from the parent port. For a breakout mode of Ethernet0 =>
    // 2x100G+1x200G, the max channels per group would be 4 (8 max lanes per
    // port/2 groups). Hence, breakout mode 2x100G (numBreakouts=2) would have
    // an offset of 2 and 1x200G(numBreakouts=1) would have an offset of 1
    // leading to interfaces Ethernet0, Ethernet2 for mode 2x100G and
    // Ethernet4 for mode 1x200G.
    for (int i = 0; i < num_breakouts; i++) {
      auto port = absl::StrCat(kEthernet, std::to_string(curr_port_number));
      // Populate expected physical channels for each port.
      // Physical channels are between 0 to 7.
      int offset = max_channels_in_group / num_breakouts;
      if (max_channels_in_group % num_breakouts != 0) {
        return gutil::InternalErrorBuilder().LogError()
               << "Invalid breakout mode (" << breakout_mode << ") found";
      }
      std::string physical_channels = "[";
      for (int j = curr_physical_channel; j < offset + curr_physical_channel;
           j++) {
        physical_channels += std::to_string(j);
        // Add comma after each but last entry.
        if (j < offset + curr_physical_channel - 1) physical_channels += ",";
      }
      physical_channels += "]";
      curr_physical_channel += offset;
      curr_port_number += offset;
      expected_breakout_info[port] = PortBreakoutInfo{physical_channels};
    }
  }
  return expected_breakout_info;
}

absl::StatusOr<absl::flat_hash_map<std::string, pins_test::PortBreakoutInfo>>
GetBreakoutStateInfoForPort(gnmi::gNMI::StubInterface* sut_gnmi_stub,
                            const std::string& port,
                            absl::string_view breakout_mode) {
  ASSIGN_OR_RETURN(auto port_info,
                   GetExpectedPortInfoForBreakoutMode(port, breakout_mode));
  for (auto& p : port_info) {
    auto if_state_path = absl::StrCat("interfaces/interface[name=", p.first,
                                      "]/state/oper-status");
    auto resp_parse_str = "openconfig-interfaces:oper-status";
    ASSIGN_OR_RETURN(
        auto state_path_response,
        GetGnmiStatePathInfo(sut_gnmi_stub, if_state_path, resp_parse_str),
        _ << "Failed to get GNMI state path value for oper-status for "
             "port "
          << p.first);
    p.second.oper_status = state_path_response;

    auto if_physical_channels_path = absl::StrCat(
        "interfaces/interface[name=", p.first, "]/state/physical-channel");
    resp_parse_str = "openconfig-platform-transceiver:physical-channel";
    ASSIGN_OR_RETURN(
        state_path_response,
        GetGnmiStatePathInfo(sut_gnmi_stub, if_physical_channels_path,
                             resp_parse_str),
        _ << "Failed to get GNMI state path value for physical-channels for "
             "port "
          << p.first);
    p.second.physical_channels = state_path_response;
  }
  return port_info;
}

absl::Status GetBreakoutModeConfigFromString(
    gnmi::SetRequest& req, const absl::string_view port_index,
    const absl::string_view breakout_mode) {
  std::string kBreakoutPath = absl::StrCat("components/component[name=1/",
                                           port_index, "]/port/breakout-mode");
  // Get breakout groups corresponding to breakout mode.
  // For a mixed breakout mode, get "+" separated breakout groups.
  // Eg. For a mixed breakout mode of "2x100G + 1x200G"; modes = {2x100G,
  // 1x200G}
  std::vector<std::string> modes = absl::StrSplit(breakout_mode, '+');
  std::vector<std::string> group_configs;
  auto max_channels_in_group = kMaxPortLanes / modes.size();
  auto index = 0;
  for (auto& mode : modes) {
    auto num_breakouts_str = mode.substr(0, mode.find('x'));
    int num_breakouts;
    if (!absl::SimpleAtoi(num_breakouts_str, &num_breakouts)) {
      return gutil::InternalErrorBuilder().LogError()
             << "Failed to convert string (" << num_breakouts_str
             << ") to integer";
    }
    auto breakout_speed = mode.substr(mode.find('x') + 1);
    auto num_physical_channels = max_channels_in_group / num_breakouts;
    auto group_config = absl::Substitute(
        R"pb({
               "config": {
                 "breakout-speed": "openconfig-if-ethernet:SPEED_$0B",
                 "index": $1,
                 "num-breakouts": $2,
                 "num-physical-channels": $3
               },
               "index": $1
             })pb",
        breakout_speed, index, num_breakouts,
        std::to_string(num_physical_channels));
    group_configs.push_back(group_config);
    index += 1;
  }

  std::string main;
  for (auto& group_config : group_configs) {
    main += absl::StrCat(group_config, ",");
  }
  // Pop the last comma from the group config array.
  main.pop_back();
  auto kBreakoutConfig = absl::Substitute(
      R"pb({ "openconfig-platform-port:groups": { "group": [ $0 ] } })pb",
      main);

  // Build GNMI config set request for given port breakout mode.
  ASSIGN_OR_RETURN(req,
                   BuildGnmiSetRequest(kBreakoutPath, GnmiSetType::kReplace,
                                       kBreakoutConfig));
  return absl::OkStatus();
}

std::vector<std::string> GetNonExistingPortsAfterBreakout(
    absl::flat_hash_map<std::string, PortBreakoutInfo>& orig_port_info,
    absl::flat_hash_map<std::string, PortBreakoutInfo>& new_port_info,
    bool expected_success) {
  std::vector<std::string> nonExistingPortList;
  absl::flat_hash_map<std::string, PortBreakoutInfo>*orig_map = &orig_port_info,
                                   *new_map = &new_port_info;
  if (!expected_success) {
    orig_map = &new_port_info;
    new_map = &orig_port_info;
  }
  for (const auto& port : *orig_map) {
    if (new_map->find(port.first) == new_map->end()) {
      nonExistingPortList.push_back(port.first);
    }
  }
  return nonExistingPortList;
}

absl::Status ValidateBreakoutState(
    gnmi::gNMI::StubInterface* sut_gnmi_stub,
    absl::flat_hash_map<std::string, PortBreakoutInfo>& expected_port_info,
    std::vector<std::string>& non_existing_ports_list) {
  if (expected_port_info.empty()) {
    return gutil::InternalErrorBuilder().LogError()
           << "Expected port info map is empty";
  }

  for (const auto& port : expected_port_info) {
    // Verify that the oper-status state path value is as expected.
    auto if_state_path = absl::StrCat("interfaces/interface[name=", port.first,
                                      "]/state/oper-status");
    auto resp_parse_str = "openconfig-interfaces:oper-status";
    ASSIGN_OR_RETURN(
        auto state_path_response,
        GetGnmiStatePathInfo(sut_gnmi_stub, if_state_path, resp_parse_str),
        _ << "Failed to get GNMI state path value for oper-status for "
             "port "
          << port.first);
    if (!absl::StrContains(state_path_response, port.second.oper_status)) {
      return gutil::InternalErrorBuilder().LogError()
             << absl::StrCat("Port oper-status match failed for port ",
                             port.first, ". got: ", state_path_response,
                             ", want:", port.second.oper_status);
    }
    // Verify that the physical-channels state path value is as expected.
    if_state_path = absl::StrCat("interfaces/interface[name=", port.first,
                                 "]/state/physical-channel");
    resp_parse_str = "openconfig-platform-transceiver:physical-channel";
    ASSIGN_OR_RETURN(
        state_path_response,
        GetGnmiStatePathInfo(sut_gnmi_stub, if_state_path, resp_parse_str),
        _ << "Failed to get GNMI state path value for physical-channels for "
             "port "
          << port.first);
    if (!absl::StrContains(state_path_response,
                           port.second.physical_channels)) {
      return gutil::InternalErrorBuilder().LogError()
             << absl::StrCat("Physical channel match failed for port ",
                             port.first, ". got: ", state_path_response,
                             ", want: ", port.second.physical_channels);
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
