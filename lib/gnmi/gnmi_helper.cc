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

#include "lib/gnmi/gnmi_helper.h"

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

#include "absl/algorithm/container.h"
#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/log/log.h"
#include "absl/numeric/int128.h"
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
#include "absl/strings/strip.h"
#include "absl/strings/substitute.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "absl/flags/flag.h"
#include "github.com/openconfig/gnmi/proto/gnmi_ext/gnmi_ext.pb.h"
#include "github.com/openconfig/gnoi/types/types.pb.h"
#include "google/protobuf/any.pb.h"
#include "google/protobuf/text_format.h"
#include "grpcpp/client_context.h"
#include "gutil/collections.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "lib/gnmi/openconfig.pb.h"
#include "lib/p4rt/p4rt_port.h"
#include "lib/utils/json_utils.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "proto/gnmi/gnmi.pb.h"
#include "re2/re2.h"
#include "thinkit/switch.h"

// It is assumed that getting the device id through gnmi and the gnmi
// get type of CONFIG is supported by default. But they can be overriden
// using these flags
// TODO(PINS): To be removed when get device id and get config are supported
ABSL_FLAG(bool, gnmi_deviceid_support, true, "gNMI supports GetDeviceId");
ABSL_FLAG(bool, gnmi_get_config_support, true,
              "gNMI supports config type in gnmi get request");

namespace pins_test {
namespace {

using ::nlohmann::json;

// Splits string to tokens separated by a char '/' as long as '/' is not
// included in [].
const LazyRE2 kSplitBreakSquareBraceRE = {R"(([^\[\/]+(\[[^\]]+\])*)\/?)"};

const absl::flat_hash_map<BreakoutSpeed, absl::string_view>&
BreakoutSpeedToOpenconfig() {
  static const auto* const kMap =
      new absl::flat_hash_map<BreakoutSpeed, absl::string_view>({
          {BreakoutSpeed::k100GB, "openconfig-if-ethernet:SPEED_100GB"},
          {BreakoutSpeed::k200GB, "openconfig-if-ethernet:SPEED_200GB"},
          {BreakoutSpeed::k400GB, "openconfig-if-ethernet:SPEED_400GB"},
      });
  return *kMap;
}

// Given a JSON string for OpenConfig interfaces. This function will parse
// through the JSON and identify any ports with an 'openconfig-p4rt:id' value
// set, and return a map of the Port Name to the Port ID.
//
// `field_type` is the type of open config data this function should parse (e.g.
// "config" or "state").
absl::StatusOr<absl::flat_hash_map<std::string, std::string>>
GetPortNameToIdMapFromJsonString(absl::string_view json_string,
                                 absl::string_view field_type) {
  VLOG(2) << "Getting Port Name -> ID Map from JSON string: " << json_string;
  const nlohmann::basic_json<> response_json = json::parse(json_string);

  // TODO: Only check for "openconfig-interfaces:interfaces" once
  // LegoHerc responses are scoped at the correct level.
  auto oc_intf_list_json = response_json.find("interface");
  if (oc_intf_list_json == response_json.end()) {
    const auto oc_intf_json =
        response_json.find("openconfig-interfaces:interfaces");
    if (oc_intf_json == response_json.end()) {
      return absl::NotFoundError(
          absl::StrCat("'openconfig-interfaces:interfaces' not found: ",
                       response_json.dump()));
    }
    oc_intf_list_json = oc_intf_json->find("interface");
    if (oc_intf_list_json == oc_intf_json->end()) {
      return absl::NotFoundError(
          absl::StrCat("'interface' not found: ", oc_intf_json->dump()));
    }
  }

  absl::flat_hash_map<std::string, std::string> interface_name_to_port_id;
  for (const auto& element : oc_intf_list_json->items()) {
    const auto element_name_json = element.value().find("name");
    if (element_name_json == element.value().end()) {
      return absl::NotFoundError(
          absl::StrCat("'name' not found: ", element.value().dump()));
    }
    std::string name = element_name_json->get<std::string>();

    const auto element_interface_json = element.value().find(field_type);
    if (element_interface_json == element.value().end()) {
      return gutil::NotFoundErrorBuilder()
             << "'" << field_type << "' not found: " << element.value().dump();
    }

    const auto element_id_json =
        element_interface_json->find("openconfig-p4rt:id");
    if (element_id_json == element_interface_json->end()) {
      continue;
    }

    interface_name_to_port_id[name] = absl::StrCat(element_id_json->get<int>());
  }
  return interface_name_to_port_id;
}

absl::StatusOr<json> GetField(const json& object,
                              absl::string_view field_name) {
  auto field = object.find(field_name);
  if (field == object.end()) {
    return absl::NotFoundError(
        absl::StrCat(field_name, " not found in ", object.dump(), "."));
  }
  return absl::StatusOr<json>(*std::move(field));
}

absl::StatusOr<json> AccessJsonValue(const json& json_value,
                                     absl::Span<const absl::string_view> path) {
  json json_result = json_value;
  for (const auto& current_path : path) {
    ASSIGN_OR_RETURN(json_result, GetField(json_result, current_path));
  }
  return json_result;
}

absl::StatusOr<uint64_t> ParseJsonValueAsUint(
    const json& json_value, absl::Span<const absl::string_view> path) {
  ASSIGN_OR_RETURN(json value, AccessJsonValue(json_value, path));
  if (uint64_t int_value;
      absl::SimpleAtoi(value.get<std::string>(), &int_value)) {
    return int_value;
  }
  return absl::InvalidArgumentError(absl::StrCat(
      json_yang::DumpJson(value), " could not be parsed as an uint64."));
}

std::optional<uint64_t> ParseJsonValueAsOptionalUint(
    const json& json_value, absl::Span<const absl::string_view> path) {
  auto parsedValue = ParseJsonValueAsUint(json_value, path);

  if (parsedValue.ok()) return *parsedValue;
  return std::nullopt;
}

absl::StatusOr<json> GetElement(const json& array, int index) {
  if (!array.is_array()) {
    return absl::InvalidArgumentError("Passed in json was not an array.");
  }
  if (index < 0 || index >= array.size()) {
    return absl::InvalidArgumentError(
        absl::StrCat("Index ", index, " is out of range (array is size ",
                     array.size(), ")."));
  }
  return json(array[index]);
}

absl::StatusOr<json> GetBreakoutConfigWithIndex(const json& json_array,
                                                uint32_t index) {
  RET_CHECK(json_array.is_array())
      << "The breakout group should be a valid Json array";
  for (const auto& group_config : json_array) {
    ASSIGN_OR_RETURN(const auto& current_index,
                     AccessJsonValue(group_config, {"index"}));
    if (index == current_index) {
      return AccessJsonValue(group_config, {"config"});
    }
  }
  return absl::NotFoundError(
      absl::StrCat("Couldn't find the breakout group with index: ", index));
}

absl::Status IsBreakoutModeMatch(const BreakoutMode& breakout,
                                 const json& json_array) {
  // Convert the JSON array of groups to a vector of breakout speed.
  std::vector<std::string> json_breakout;
  for (int index = 0; index < json_array.size(); ++index) {
    ASSIGN_OR_RETURN(const auto& breakout_config,
                     GetBreakoutConfigWithIndex(json_array, index));
    ASSIGN_OR_RETURN(const auto& breakout_num,
                     AccessJsonValue(breakout_config, {"num-breakouts"}));
    ASSIGN_OR_RETURN(const auto& json_port_speed,
                     AccessJsonValue(breakout_config, {"breakout-speed"}));
    json_breakout.insert(json_breakout.end(), breakout_num, json_port_speed);
  }

  if (json_breakout.size() != breakout.size()) {
    return absl::NotFoundError("Breakout channel count mismatch");
  }

  for (int index = 0; index < breakout.size(); ++index) {
    ASSIGN_OR_RETURN(
        auto port_speed_str,
        gutil::FindOrStatus(BreakoutSpeedToOpenconfig(), breakout[index]));
    if (json_breakout[index] != port_speed_str) {
      return absl::NotFoundError("Breakout channel speed mismatch");
    }
  }
  return absl::OkStatus();
}

absl::StatusOr<int> FindBreakoutModeFromComponentJsonArray(
    const BreakoutMode& breakout, const json& json_array,
    const absl::flat_hash_set<int>& ignore_ports) {
  RET_CHECK(json_array.is_array())
      << "The component should be a valid Json array";
  for (const auto& component : json_array) {
    auto port_id = AccessJsonValue(
        component, {"port", "config", "openconfig-pins-platform-port:port-id"});
    auto breakout_group = AccessJsonValue(
        component,
        {"port", "openconfig-platform-port:breakout-mode", "groups", "group"});

    if (!port_id.ok() || !breakout_group.ok()) continue;

    if (ignore_ports.contains(*port_id)) {
      LOG(INFO) << "Skipped the ignore port: " << *port_id;
      continue;
    }

    if (IsBreakoutModeMatch(breakout, *breakout_group).ok()) {
      LOG(INFO) << *port_id << " matches the given breakout mode";
      return *port_id;
    }
  }
  return absl::NotFoundError("Couldn't find the breakout mode");
}

absl::StatusOr<std::vector<std::string>>
FindInterfacesNameFromInterfaceJsonArray(int port_number,
                                         const json& json_array) {
  std::vector<std::string> interfaces_name;
  RET_CHECK(json_array.is_array())
      << "The interface should be a valid Json array";
  for (const auto& interface : json_array) {
    auto interface_name = AccessJsonValue(interface, {"name"});

    if (!interface_name.ok()) continue;
    auto interface_name_str = interface_name->get<std::string>();
    if (absl::StartsWith(interface_name_str,
                         absl::StrFormat("Ethernet1/%d/", port_number))) {
      interfaces_name.push_back(interface_name_str);
    }
  }
  return interfaces_name;
}

absl::StatusOr<gnmi::GetResponse> SendGnmiGetRequest(
    gnmi::gNMI::StubInterface* gnmi_stub, const gnmi::GetRequest& request,
    std::optional<absl::Duration> timeout) {
  VLOG(1) << "Sending GET request: " << request.ShortDebugString();
  gnmi::GetResponse response;
  grpc::ClientContext context;
  if (timeout.has_value()) {
    context.set_deadline(absl::ToChronoTime(absl::Now() + *timeout));
  }
  RETURN_IF_ERROR(gutil::GrpcStatusToAbslStatus(
                      gnmi_stub->Get(&context, request, &response)))
          .LogError()
          .SetPrepend()
      << "GET request failed with error: ";
  VLOG(1) << "Received GET response: " << response.ShortDebugString();
  return response;
}

// Deletes a single interface's P4RT id.
absl::Status DeleteInterfaceP4rtId(
    gnmi::gNMI::StubInterface& gnmi_stub,
    const openconfig::Interfaces::Interface& interface) {
  std::string ops_config_path =
      absl::StrCat("interfaces/interface[name=", interface.name(),
                   "]/config/openconfig-p4rt:id");
  // Value is irrelevant for deletes.
  return pins_test::SetGnmiConfigPath(&gnmi_stub, ops_config_path,
                                      GnmiSetType::kDelete, /*value=*/"");
}

// Modifies a single interface's P4RT id.
absl::Status ModifyInterfaceP4rtId(
    gnmi::gNMI::StubInterface& gnmi_stub,
    const openconfig::Interfaces::Interface& interface) {
  std::string ops_config_path =
      absl::StrCat("interfaces/interface[name=", interface.name(),
                   "]/config/openconfig-p4rt:id");
  std::string ops_val = absl::StrCat(
      "{\"openconfig-p4rt:id\":", interface.config().p4rt_id(), "}");

  // Due to limitations of the P4RT server, we first delete the path, in case it
  // exists, then set it.
  // Value is irrelevant for deletes.
  RETURN_IF_ERROR(pins_test::SetGnmiConfigPath(
      &gnmi_stub, ops_config_path, GnmiSetType::kDelete, /*value=*/""));
  return pins_test::SetGnmiConfigPath(&gnmi_stub, ops_config_path,
                                      GnmiSetType::kUpdate, ops_val);
}

absl::StatusOr<Counters> GetCountersForInterface(const json& interface_json) {
  Counters counters;
  ASSIGN_OR_RETURN(
      counters.in_pkts,
      ParseJsonValueAsUint(interface_json, {"state", "counters", "in-pkts"}));
  ASSIGN_OR_RETURN(
      counters.out_pkts,
      ParseJsonValueAsUint(interface_json, {"state", "counters", "out-pkts"}));
  ASSIGN_OR_RETURN(
      counters.in_octets,
      ParseJsonValueAsUint(interface_json, {"state", "counters", "in-octets"}));
  ASSIGN_OR_RETURN(counters.out_octets,
                   ParseJsonValueAsUint(interface_json,
                                        {"state", "counters", "out-octets"}));
  ASSIGN_OR_RETURN(counters.in_unicast_pkts,
                   ParseJsonValueAsUint(interface_json, {"state", "counters",
                                                         "in-unicast-pkts"}));
  ASSIGN_OR_RETURN(counters.out_unicast_pkts,
                   ParseJsonValueAsUint(interface_json, {"state", "counters",
                                                         "out-unicast-pkts"}));
  ASSIGN_OR_RETURN(counters.in_multicast_pkts,
                   ParseJsonValueAsUint(interface_json, {"state", "counters",
                                                         "in-multicast-pkts"}));
  ASSIGN_OR_RETURN(
      counters.out_multicast_pkts,
      ParseJsonValueAsUint(interface_json,
                           {"state", "counters", "out-multicast-pkts"}));
  ASSIGN_OR_RETURN(counters.in_broadcast_pkts,
                   ParseJsonValueAsUint(interface_json, {"state", "counters",
                                                         "in-broadcast-pkts"}));
  ASSIGN_OR_RETURN(
      counters.out_broadcast_pkts,
      ParseJsonValueAsUint(interface_json,
                           {"state", "counters", "out-broadcast-pkts"}));
  ASSIGN_OR_RETURN(
      counters.in_errors,
      ParseJsonValueAsUint(interface_json, {"state", "counters", "in-errors"}));
  ASSIGN_OR_RETURN(counters.out_errors,
                   ParseJsonValueAsUint(interface_json,
                                        {"state", "counters", "out-errors"}));
  ASSIGN_OR_RETURN(counters.in_discards,
                   ParseJsonValueAsUint(interface_json,
                                        {"state", "counters", "in-discards"}));
  ASSIGN_OR_RETURN(counters.out_discards,
                   ParseJsonValueAsUint(interface_json,
                                        {"state", "counters", "out-discards"}));
  ASSIGN_OR_RETURN(
      counters.in_buffer_discards,
      ParseJsonValueAsUint(
          interface_json,
          {"state", "counters", "pins-interfaces:in-buffer-discards"}));
  ASSIGN_OR_RETURN(
      counters.in_maxsize_exceeded,
      ParseJsonValueAsUint(interface_json,
                           {"openconfig-if-ethernet:ethernet", "state",
                            "counters", "in-maxsize-exceeded"}));
  ASSIGN_OR_RETURN(counters.in_fcs_errors,
                   ParseJsonValueAsUint(
                       interface_json, {"state", "counters", "in-fcs-errors"}));
  counters.carrier_transitions = ParseJsonValueAsOptionalUint(
      interface_json, {"state", "counters", "carrier-transitions"});
  ASSIGN_OR_RETURN(
      json subinterfaces,
      AccessJsonValue(interface_json, {"subinterfaces", "subinterface"}));
  ASSIGN_OR_RETURN(json subinterface, GetElement(subinterfaces, 0));
  ASSIGN_OR_RETURN(
      counters.in_ipv4_pkts,
      ParseJsonValueAsUint(subinterface, {"openconfig-if-ip:ipv4", "state",
                                          "counters", "in-pkts"}));
  ASSIGN_OR_RETURN(
      counters.out_ipv4_pkts,
      ParseJsonValueAsUint(subinterface, {"openconfig-if-ip:ipv4", "state",
                                          "counters", "out-pkts"}));
  ASSIGN_OR_RETURN(
      counters.in_ipv6_pkts,
      ParseJsonValueAsUint(subinterface, {"openconfig-if-ip:ipv6", "state",
                                          "counters", "in-pkts"}));
  ASSIGN_OR_RETURN(
      counters.out_ipv6_pkts,
      ParseJsonValueAsUint(subinterface, {"openconfig-if-ip:ipv6", "state",
                                          "counters", "out-pkts"}));
  ASSIGN_OR_RETURN(
      counters.in_ipv6_discarded_pkts,
      ParseJsonValueAsUint(subinterface, {"openconfig-if-ip:ipv6", "state",
                                          "counters", "in-discarded-pkts"}));
  ASSIGN_OR_RETURN(
      counters.out_ipv6_discarded_pkts,
      ParseJsonValueAsUint(subinterface, {"openconfig-if-ip:ipv6", "state",
                                          "counters", "out-discarded-pkts"}));

  // Copy the blackhole port counters only if all the blackhole port counters
  // are available.
  absl::StatusOr<uint64_t> in_discard_events = ParseJsonValueAsUint(
      interface_json,
      {"state", "pins-interfaces:blackhole", "in-discard-events"});
  absl::StatusOr<uint64_t> out_discard_events = ParseJsonValueAsUint(
      interface_json,
      {"state", "pins-interfaces:blackhole", "out-discard-events"});
  absl::StatusOr<uint64_t> in_error_events = ParseJsonValueAsUint(
      interface_json,
      {"state", "pins-interfaces:blackhole", "in-error-events"});
  absl::StatusOr<uint64_t> fec_not_correctable_events = ParseJsonValueAsUint(
      interface_json, {"state", "pins-interfaces:blackhole",
                       "fec-not-correctable-events"});
  if (in_discard_events.ok() && out_discard_events.ok() &&
      in_error_events.ok() && fec_not_correctable_events.ok()) {
    counters.blackhole_counters = BlackholePortCounters{
        .in_discard_events = *in_discard_events,
        .out_discard_events = *out_discard_events,
        .in_error_events = *in_error_events,
        .fec_not_correctable_events = *fec_not_correctable_events};
  }
  return counters;
}

constexpr absl::string_view kBlackholeSwitchCountersParseKey =
    "pins-platform:blackhole";

absl::StatusOr<BlackholeSwitchCounters> ParseBlackholeSwitchCounters(
    const json& switch_state_json) {
  BlackholeSwitchCounters counters;

  ASSIGN_OR_RETURN(
      counters.in_discard_events,
      ParseJsonValueAsUint(switch_state_json, {kBlackholeSwitchCountersParseKey,
                                               "in-discard-events"}));
  ASSIGN_OR_RETURN(
      counters.out_discard_events,
      ParseJsonValueAsUint(switch_state_json, {kBlackholeSwitchCountersParseKey,
                                               "out-discard-events"}));
  ASSIGN_OR_RETURN(
      counters.in_error_events,
      ParseJsonValueAsUint(switch_state_json, {kBlackholeSwitchCountersParseKey,
                                               "in-error-events"}));
  ASSIGN_OR_RETURN(
      counters.lpm_miss_events,
      ParseJsonValueAsUint(switch_state_json, {kBlackholeSwitchCountersParseKey,
                                               "lpm-miss-events"}));
  ASSIGN_OR_RETURN(
      counters.fec_not_correctable_events,
      ParseJsonValueAsUint(switch_state_json, {kBlackholeSwitchCountersParseKey,
                                               "fec-not-correctable-events"}));
  ASSIGN_OR_RETURN(
      counters.memory_error_events,
      ParseJsonValueAsUint(switch_state_json, {kBlackholeSwitchCountersParseKey,
                                               "memory-error-events"}));
  ASSIGN_OR_RETURN(
      counters.blackhole_events,
      ParseJsonValueAsUint(switch_state_json, {kBlackholeSwitchCountersParseKey,
                                               "blackhole-events"}));

  return counters;
}

absl::StatusOr<BlackholePortCounters> ParseBlackholePortCounters(
    const json& port_counters_json) {
  BlackholePortCounters counters;

  ASSIGN_OR_RETURN(
      counters.in_discard_events,
      ParseJsonValueAsUint(port_counters_json, {"in-discard-events"}));
  ASSIGN_OR_RETURN(
      counters.out_discard_events,
      ParseJsonValueAsUint(port_counters_json, {"out-discard-events"}));
  ASSIGN_OR_RETURN(
      counters.in_error_events,
      ParseJsonValueAsUint(port_counters_json, {"in-error-events"}));
  ASSIGN_OR_RETURN(
      counters.fec_not_correctable_events,
      ParseJsonValueAsUint(port_counters_json, {"fec-not-correctable-events"}));

  return counters;
}

// Parses `val` into a JSON value, extracting `match_tag` if non-empty.
absl::StatusOr<nlohmann::json> ParseJsonResponseAsJson(
    absl::string_view val, absl::string_view match_tag) {
  ASSIGN_OR_RETURN(const nlohmann::json resp_json, json_yang::ParseJson(val));
  if (match_tag.empty()) return absl::StatusOr<nlohmann::json>(resp_json);
  const auto match_tag_json = resp_json.find(match_tag);
  if (match_tag_json == resp_json.end()) {
    return gutil::InternalErrorBuilder().LogError()
           << match_tag << " not present in JSON response " << val;
  }
  return absl::StatusOr<nlohmann::json>(*match_tag_json);
}

// Parses a JSON value from the update in `notification`, extracting `match_tag`
// (if one is given).
// WARNING: Returns InternalError if notification does not have exactly 1
// update.
absl::StatusOr<nlohmann::json> ParseGnmiNotificationAsJson(
    const gnmi::Notification& notification, absl::string_view match_tag) {
  if (notification.update_size() != 1)
    return gutil::InternalErrorBuilder().LogError()
           << "Unexpected update size in response (should be 1): "
           << notification.update_size();
  switch (notification.update(0).val().value_case()) {
    case gnmi::TypedValue::kStringVal:
      // A string value is also a JSON string value.
      return notification.update(0).val().string_val();
    case gnmi::TypedValue::kJsonVal:
      return ParseJsonResponseAsJson(notification.update(0).val().json_val(),
                                     match_tag);
    case gnmi::TypedValue::kJsonIetfVal:
      return ParseJsonResponseAsJson(
          notification.update(0).val().json_ietf_val(), match_tag);
    default:
      return gutil::InternalErrorBuilder().LogError()
             << "Unexpected data type: "
             << notification.update(0).val().value_case();
  }
}

absl::StatusOr<json> GetBlackholePortCountersJson(
    absl::string_view interface_name, gnmi::gNMI::StubInterface& gnmi_stub) {
  const std::string ops_state_path =
      absl::StrCat("interfaces/interface[name=", interface_name,
                   "]/state/pins-interfaces:blackhole");
  const std::string ops_parse_str = "pins-interfaces:blackhole";
  ASSIGN_OR_RETURN(
      std::string port_counters_info,
      GetGnmiStatePathInfo(&gnmi_stub, ops_state_path, ops_parse_str));
  return json_yang::ParseJson(port_counters_info);
}

}  // namespace

void StripSymbolFromString(std::string& str, char symbol) {
  str.erase(std::remove(str.begin(), str.end(), symbol), str.end());
}

std::string GnmiFieldTypeToString(GnmiFieldType field_type) {
  switch (field_type) {
    case GnmiFieldType::kConfig:
      return "config";
    case GnmiFieldType::kState:
      return "state";
  }
  LOG(DFATAL) << "invalid GnmiFieldType: " << static_cast<int>(field_type);
  return "";
}

std::string OpenConfigWithInterfaces(
    GnmiFieldType field_type,
    absl::Span<const OpenConfigInterfaceDescription> interfaces) {
  using json = nlohmann::json;
  std::vector<json> port_configs;
  for (const auto& interface : interfaces) {
    port_configs.push_back({{"name", interface.port_name},
                            {GnmiFieldTypeToString(field_type),
                             {{"openconfig-p4rt:id", interface.port_id}}}});
  }
  json open_config{
      {"openconfig-interfaces:interfaces", {{"interface", port_configs}}}};
  return open_config.dump();
}

std::string EmptyOpenConfig() {
  return OpenConfigWithInterfaces(GnmiFieldType::kConfig, /*interfaces=*/{});
}

// This API generates gNMI path from OC path string.
// Example1:
// components/component[name=integrated_circuit0]/integrated-circuit/state.
// Example2:
// components/component[name=1/1]/integrated-circuit/state.
// Example3:
// sampling/sflow/collectors/collector[address=127.0.0.1][port=6343]/state/address
gnmi::Path ConvertOCStringToPath(absl::string_view oc_path) {
  absl::string_view element;
  std::vector<absl::string_view> elements;
  while (RE2::FindAndConsume(&oc_path, *kSplitBreakSquareBraceRE, &element)) {
    elements.push_back(element);
  }
  gnmi::Path path;
  for (absl::string_view node : elements) {
    // Splits string in format "component[name=integrated_circuit0]" to two
    // tokens, i.e., "component" and "[name=integrated_circuit0]".
    static constexpr LazyRE2 kSplitNameValueRE = {
        R"(([^\[]+)(\[(.+)=(.+)\]+))"};
    std::string key;
    absl::string_view attr_to_value;
    // "key/[attribute=value]" requests are in the format
    // Ex:interface[name=Ethernet0].
    if (RE2::FullMatch(node, *kSplitNameValueRE, &key, &attr_to_value)) {
      auto* elem = path.add_elem();
      elem->set_name(key);
      std::string attribute;
      std::string value;
      static constexpr LazyRE2 kSplitAttributeValueRE = {
          R"(\[([^=]+)=([^\]]+)\])"};
      // Keep parsing more <attribute, value> in this string. e.g.,
      // [address=127.0.0.1][port=6343] ==> {{address, 127.0.0.1}, {port, 6343}}
      while (RE2::Consume(&attr_to_value, *kSplitAttributeValueRE, &attribute,
                          &value)) {
        (*elem->mutable_key())[attribute] = value;
      }
    } else {
      path.add_elem()->set_name(std::string(node));
    }
  }
  return path;
}

gnoi::types::Path GnmiToGnoiPath(gnmi::Path path) {
  gnoi::types::Path gnoi_path;
  gnoi_path.set_origin(std::move(*path.mutable_origin()));
  for (gnmi::PathElem& element : *path.mutable_elem()) {
    gnoi::types::PathElem& gnoi_element = *gnoi_path.add_elem();
    gnoi_element.set_name(std::move(*element.mutable_name()));
    *gnoi_element.mutable_key() = std::move(*element.mutable_key());
  }
  return gnoi_path;
}

absl::StatusOr<gnmi::SetRequest> BuildGnmiSetRequest(
    absl::string_view oc_path, GnmiSetType set_type,
    absl::string_view json_val) {
  gnmi::SetRequest req;
  req.mutable_prefix()->set_origin(kOpenconfigStr);
  req.mutable_prefix()->set_target(kTestChassisNameForGnmi);
  gnmi::Path* path;

  switch (set_type) {
    case GnmiSetType::kUpdate: {
      gnmi::Update* update = req.add_update();
      path = update->mutable_path();
      update->mutable_val()->set_json_ietf_val(std::string(json_val));
    } break;

    case GnmiSetType::kReplace: {
      gnmi::Update* replace = req.add_replace();
      path = replace->mutable_path();
      replace->mutable_val()->set_json_ietf_val(std::string(json_val));
    } break;

    case GnmiSetType::kDelete: {
      path = req.add_delete_();
    } break;

    default:
      return gutil::InternalErrorBuilder().LogError()
             << "Unknown gNMI Set Request";
  }

  *path = ConvertOCStringToPath(oc_path);
  return req;
}

absl::StatusOr<gnmi::GetRequest> BuildGnmiGetRequest(
    absl::string_view oc_path, gnmi::GetRequest::DataType req_type) {
  gnmi::GetRequest req;
  req.set_type(req_type);
  req.mutable_prefix()->set_origin(kOpenconfigStr);
  req.mutable_prefix()->set_target(kTestChassisNameForGnmi);
  req.set_encoding(gnmi::JSON_IETF);
  if (oc_path.empty()) {
    return req;
  }
  *req.add_path() = ConvertOCStringToPath(oc_path);
  return req;
}

absl::StatusOr<std::string> ParseGnmiGetResponse(
    const gnmi::GetResponse& response, absl::string_view match_tag,
    int indent) {
  nlohmann::json json_config = json::object();
  if (response.notification_size() == 1) {
    ASSIGN_OR_RETURN(json_config, ParseGnmiNotificationAsJson(
                                      response.notification(0), match_tag));
    return json_config.dump(indent);
  }
  // Get the JSON objects from each notification and merge together into a
  // single, larger object.
  for (const gnmi::Notification& notification : response.notification()) {
    ASSIGN_OR_RETURN(const nlohmann::json partial_config,
                     ParseGnmiNotificationAsJson(notification, match_tag));
    if (partial_config.is_null()) continue;
    for (auto& [key, value] : partial_config.items()) {
      if (json_config.contains(key)) {
        return gutil::InternalErrorBuilder()
               << "Got key '" << key
               << "' twice in a single GetResponse: " << response.DebugString();
      }
      json_config[key] = value;
    }
  }
  return json_config.dump(indent);
}

absl::Status SetGnmiConfigPath(gnmi::gNMI::StubInterface* gnmi_stub,
                               absl::string_view config_path,
                               GnmiSetType operation, absl::string_view value) {
  ASSIGN_OR_RETURN(gnmi::SetRequest request,
                   BuildGnmiSetRequest(config_path, operation, value));
  LOG(INFO) << "Sending SET request: " << request.ShortDebugString();
  gnmi::SetResponse response;
  grpc::ClientContext context;
  auto status = gnmi_stub->Set(&context, request, &response);
  if (!status.ok()) {
    return gutil::UnknownErrorBuilder().LogError()
           << "SET request failed! Error code: " << status.error_code()
           << " , Error message: " << status.error_message();
  }
  LOG(INFO) << "Received SET response: " << response.ShortDebugString();
  return absl::OkStatus();
}

absl::Status UpdateGnmiConfigLeaf(gnmi::gNMI::StubInterface* gnmi_stub,
                                  absl::string_view config_path,
                                  absl::string_view value) {
  size_t leaf_pos = config_path.find_last_of('/');
  if (leaf_pos == config_path.npos) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Unable to update gNMI leaf. Config path must be of the form "
           << "<subtree>/<leaf>: " << config_path;
  }
  if (!absl::StrContains(config_path, "/config/")) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Unable to update gNMI leaf. Config path must be in a '/config/ "
           << "subtree: " << config_path;
  }
  absl::string_view leaf = config_path.substr(leaf_pos + 1);
  RETURN_IF_ERROR(
      SetGnmiConfigPath(gnmi_stub, config_path, GnmiSetType::kUpdate,
                        absl::Substitute("{\"$0\":\"$1\"}", leaf, value)));
  return absl::OkStatus();
}

absl::Status UpdateAndVerifyGnmiConfigLeaf(gnmi::gNMI::StubInterface* gnmi_stub,
                                           absl::string_view config_path,
                                           absl::string_view value,
                                           absl::Duration timeout) {
  absl::Time deadline = absl::Now() + timeout;
  RETURN_IF_ERROR(UpdateGnmiConfigLeaf(gnmi_stub, config_path, value));
  std::string state_path =
      absl::StrReplaceAll(config_path, {{"/config/", "/state/"}});
  absl::StatusOr<std::string> state_value;
  do {
    state_value = GetGnmiStateLeafValue(gnmi_stub, state_path);
    if (state_value.ok() && *state_value == value) return absl::OkStatus();
  } while (absl::Now() < deadline);
  return gutil::DeadlineExceededErrorBuilder()
         << "Failed to verify gNMI state leaf after configuration for path ["
         << config_path << "]. "
         << (state_value.ok() ? "Final value: " : "Final status: ")
         << (state_value.ok() ? *state_value : state_value.status().ToString());
}

absl::Status PushGnmiConfig(gnmi::gNMI::StubInterface& stub,
                            const std::string& chassis_name,
                            absl::string_view gnmi_config,
                            absl::uint128 election_id) {
  gnmi::SetRequest req;
  req.mutable_prefix()->set_origin("openconfig");
  req.mutable_prefix()->set_target(chassis_name);
  gnmi::Update* replace = req.add_replace();
  replace->mutable_path();
  replace->mutable_val()->set_json_ietf_val(gnmi_config);
  gnmi_ext::MasterArbitration* arbitration =
      req.add_extension()->mutable_master_arbitration();
  arbitration->mutable_role()->set_id("dataplane test");
  arbitration->mutable_election_id()->set_high(
      absl::Uint128High64(election_id));
  arbitration->mutable_election_id()->set_low(absl::Uint128Low64(election_id));

  gnmi::SetResponse resp;
  grpc::ClientContext context;
  grpc::Status status = stub.Set(&context, req, &resp);
  if (!status.ok()) return gutil::GrpcStatusToAbslStatus(status);
  LOG(INFO) << "Config push response: " << resp.ShortDebugString();
  return absl::OkStatus();
}

absl::Status PushGnmiConfig(thinkit::Switch& chassis,
                            absl::string_view gnmi_config) {
  ASSIGN_OR_RETURN(auto stub, chassis.CreateGnmiStub());
  return pins_test::PushGnmiConfig(
      *stub, chassis.ChassisName(),
      UpdateDeviceIdInJsonConfig(gnmi_config,
                                 absl::StrCat(chassis.DeviceId())));
}

absl::Status WaitForGnmiPortIdConvergence(gnmi::gNMI::StubInterface& stub,
                                          absl::string_view gnmi_config,
                                          const absl::Duration& timeout) {
  absl::Time deadline = absl::Now() + timeout;

  // Get expected port ID mapping from the gNMI config.
  absl::flat_hash_map<std::string, std::string> expected_port_id_by_name;
  ASSIGN_OR_RETURN(
      expected_port_id_by_name,
      GetPortNameToIdMapFromJsonString(gnmi_config, /*field_type=*/"config"));

  // Poll the switch's state waiting for the port name and ID mappings to match.
  LOG(INFO) << "Waiting for port name & ID mappings to converge.";
  absl::flat_hash_map<std::string, std::string> actual_port_id_by_name;
  while (expected_port_id_by_name != actual_port_id_by_name) {
    ASSIGN_OR_RETURN(gnmi::GetResponse response,
                     GetAllInterfaceOverGnmi(stub, absl::Seconds(60)));
    if (response.notification_size() < 1) {
      return absl::InternalError(
          absl::StrCat("Invalid response: ", response.DebugString()));
    }

    ASSIGN_OR_RETURN(
        actual_port_id_by_name,
        GetPortNameToIdMapFromJsonString(
            response.notification(0).update(0).val().json_ietf_val(),
            /*field_type=*/"state"));

    if (absl::Now() > deadline) {
      return gutil::FailedPreconditionErrorBuilder()
             << "Port IDs did not coverge after " << timeout << ": got=\n  "
             << absl::StrJoin(actual_port_id_by_name, "\n  ",
                              absl::PairFormatter(":"))
             << "\nwant=\n  "
             << absl::StrJoin(expected_port_id_by_name, "\n  ",
                              absl::PairFormatter(":"));
    }
  }

  return absl::OkStatus();
}

absl::Status WaitForGnmiPortIdConvergence(thinkit::Switch& chassis,
                                          absl::string_view gnmi_config,
                                          const absl::Duration& timeout) {
  ASSIGN_OR_RETURN(auto stub, chassis.CreateGnmiStub());
  return WaitForGnmiPortIdConvergence(*stub, gnmi_config, timeout);
}

absl::Status WaitForGnmiPortIdConvergence(gnmi::gNMI::StubInterface& stub,
                                          const absl::Duration& timeout) {
  // Use CONFIG as the gnmi get type by default. Use ALL if the flag is
  // is set to false in the command line
  // TODO(PINS): To be removed when config is supported
  const auto request_type = absl::GetFlag(FLAGS_gnmi_get_config_support)
                                ? gnmi::GetRequest::CONFIG
                                : gnmi::GetRequest::ALL;
  ASSIGN_OR_RETURN(gnmi::GetRequest request,
                   BuildGnmiGetRequest("interfaces", request_type));

  ASSIGN_OR_RETURN(gnmi::GetResponse interface_response,
                   SendGnmiGetRequest(&stub, request, timeout));
  return WaitForGnmiPortIdConvergence(
      stub, interface_response.notification(0).update(0).val().json_ietf_val(),
      timeout);
}

absl::Status CanGetAllInterfaceOverGnmi(gnmi::gNMI::StubInterface& stub,
                                        absl::Duration timeout) {
  return GetAllInterfaceOverGnmi(stub).status();
}

absl::StatusOr<gnmi::GetResponse> GetAllInterfaceOverGnmi(
    gnmi::gNMI::StubInterface& stub, absl::Duration timeout) {
  ASSIGN_OR_RETURN(auto req,
                   BuildGnmiGetRequest("interfaces", gnmi::GetRequest::STATE));
  return SendGnmiGetRequest(&stub, req, timeout);
}

absl::StatusOr<absl::flat_hash_map<std::string, std::string>>
GetInterfaceToOperStatusMapOverGnmi(gnmi::gNMI::StubInterface& stub,
                                    absl::Duration timeout) {
  ASSIGN_OR_RETURN(auto req,
                   BuildGnmiGetRequest("interfaces", gnmi::GetRequest::STATE));
  ASSIGN_OR_RETURN(gnmi::GetResponse resp,
                   SendGnmiGetRequest(&stub, req, timeout));
  if (resp.notification_size() < 1 || resp.notification(0).update_size() < 1) {
    return absl::InternalError(
        absl::StrCat("Invalid response: ", resp.DebugString()));
  }

  const auto resp_json = nlohmann::json::parse(
      resp.notification(0).update(0).val().json_ietf_val());
  // TODO: Only check for "openconfig-interfaces:interfaces" once
  // LegoHerc responses are scoped at the correct level.
  auto oc_intf_list_json = resp_json.find("interface");
  if (oc_intf_list_json == resp_json.end()) {
    const auto oc_intf_json =
        resp_json.find("openconfig-interfaces:interfaces");
    if (oc_intf_json == resp_json.end()) {
      return absl::NotFoundError(absl::StrCat(
          "'openconfig-interfaces:interfaces' not found: ", resp_json.dump()));
    }
    oc_intf_list_json = oc_intf_json->find("interface");
    if (oc_intf_list_json == oc_intf_json->end()) {
      return absl::NotFoundError(
          absl::StrCat("'interface' not found: ", oc_intf_json->dump()));
    }
  }

  absl::flat_hash_map<std::string, std::string> interface_to_oper_status_map;
  for (auto const& element : oc_intf_list_json->items()) {
    const auto element_name_json = element.value().find("name");
    if (element_name_json == element.value().end()) {
      return absl::NotFoundError(
          absl::StrCat("'name' not found: ", element.value().dump()));
    }
    std::string name = std::string(StripQuotes(element_name_json->dump()));

    // TODO: Remove once CPU contains the oper-state subtree.
    // TODO: Remove once eth1 contains the oper-state subtree.
    if (absl::StartsWith(name, "CPU") || absl::StartsWith(name, "br") ||
        absl::StartsWith(name, "eth1")) {
      LOG(INFO) << "Skipping " << name << ".";
      continue;
    }

    const auto element_interface_state_json = element.value().find("state");
    if (element_interface_state_json == element.value().end()) {
      return absl::NotFoundError(absl::StrCat("'state' not found: ", name));
    }
    const auto element_status_json =
        element_interface_state_json->find("oper-status");
    if (element_status_json == element_interface_state_json->end()) {
      return absl::NotFoundError(
          absl::StrCat("'oper-status' not found: ", name));
    }
    interface_to_oper_status_map[name] =
        std::string(StripQuotes(element_status_json->dump()));
  }

  return interface_to_oper_status_map;
}

absl::Status CheckInterfaceOperStateOverGnmi(
    gnmi::gNMI::StubInterface& stub, absl::string_view interface_oper_state,
    absl::Span<const std::string> interfaces, bool skip_non_ethernet_interfaces,
    absl::Duration timeout) {
  ASSIGN_OR_RETURN(const auto interface_to_oper_status_map,
                   GetInterfaceToOperStatusMapOverGnmi(stub, timeout));

  std::vector<std::string> all_interfaces;
  absl::flat_hash_set<std::string> matching_interfaces;
  for (const auto& [interface, oper_status] : interface_to_oper_status_map) {
    all_interfaces.push_back(interface);
    if (oper_status == interface_oper_state) {
      matching_interfaces.insert(interface);
    }
  }
  if (interfaces.empty()) {
    interfaces = all_interfaces;
  }

  std::vector<std::string> unavailable_interfaces;
  for (const std::string& interface : interfaces) {
    if (skip_non_ethernet_interfaces &&
        !absl::StrContains(interface, "Ethernet")) {
      LOG(INFO) << "Skipping check on interface: " << interface;
      continue;
    }
    if (!matching_interfaces.contains(interface)) {
      LOG(WARNING) << "Interface "
                   << interface << " not found in interfaces that are "
                   << interface_oper_state;
      unavailable_interfaces.push_back(interface);
    }
  }

  if (!unavailable_interfaces.empty()) {
    return absl::UnavailableError(absl::StrCat(
        "Some interfaces are not in the expected state ", interface_oper_state,
        ":\n", absl::StrJoin(unavailable_interfaces, "\n"),
        "\n\nInterfaces provided:\n", absl::StrJoin(interfaces, "\n")));
  }
  return absl::OkStatus();
}

absl::StatusOr<std::string> ReadGnmiPath(
    gnmi::gNMI::StubInterface* gnmi_stub, absl::string_view path,
    gnmi::GetRequest::DataType req_type, absl::string_view resp_parse_str,
    std::optional<absl::Duration> timeout) {
  ASSIGN_OR_RETURN(gnmi::GetRequest request,
                   BuildGnmiGetRequest(path, req_type));
  ASSIGN_OR_RETURN(gnmi::GetResponse response,
                   SendGnmiGetRequest(gnmi_stub, request, timeout));
  return ParseGnmiGetResponse(response, resp_parse_str);
}

absl::StatusOr<std::string> GetGnmiStatePathInfo(
    gnmi::gNMI::StubInterface* gnmi_stub, absl::string_view state_path,
    absl::string_view resp_parse_str, std::optional<absl::Duration> timeout) {
  return ReadGnmiPath(gnmi_stub, state_path, gnmi::GetRequest::STATE,
                      resp_parse_str, kVerifyOperStateDefaultTimeout);
}

absl::StatusOr<ResultWithTimestamp> GetGnmiStatePathAndTimestamp(
    gnmi::gNMI::StubInterface* gnmi_stub, absl::string_view path,
    absl::string_view resp_parse_str) {
  ASSIGN_OR_RETURN(gnmi::GetRequest request,
                   BuildGnmiGetRequest(path, gnmi::GetRequest::STATE));
  ASSIGN_OR_RETURN(
      gnmi::GetResponse response,
      SendGnmiGetRequest(gnmi_stub, request, /*timeout=*/std::nullopt));
  ASSIGN_OR_RETURN(std::string result,
                   ParseGnmiGetResponse(response, resp_parse_str));

  if (response.notification().empty()) {
    return absl::InternalError("Invalid response");
  }

  return ResultWithTimestamp{.response = std::string(StripQuotes(result)),
                             .timestamp = response.notification(0).timestamp()};
}

absl::StatusOr<std::string> GetGnmiStateLeafValue(
    gnmi::gNMI::StubInterface* gnmi_stub, absl::string_view state_path) {
  ASSIGN_OR_RETURN(std::string json,
                   GetGnmiStatePathInfo(gnmi_stub, state_path));
  ASSIGN_OR_RETURN(
      std::string value, ParseJsonValue(json),
      _ << "Failed to parse state path info for [" << state_path << "]");
  return value;
}

void AddSubtreeToGnmiSubscription(absl::string_view subtree_root,
                                  gnmi::SubscriptionList& subscription_list,
                                  gnmi::SubscriptionMode mode,
                                  bool suppress_redundant,
                                  absl::Duration interval) {
  gnmi::Subscription* subscription = subscription_list.add_subscription();
  subscription->set_mode(mode);
  if (mode == gnmi::SAMPLE) {
    subscription->set_sample_interval(absl::ToInt64Nanoseconds(interval));
  }
  subscription->set_suppress_redundant(suppress_redundant);
  *subscription->mutable_path() = ConvertOCStringToPath(subtree_root);
}

absl::StatusOr<std::vector<absl::string_view>>
GnmiGetElementFromTelemetryResponse(const gnmi::SubscribeResponse& response) {
  if (response.update().update_size() <= 0)
    return gutil::InternalErrorBuilder().LogError()
           << "Unexpected update size in response (should be > 0): "
           << response.update().update_size();
  LOG(INFO) << "Update size in response: " << response.update().update_size();

  std::vector<absl::string_view> elements;
  for (const auto& u : response.update().update()) {
    if (u.path().elem_size() <= 0)
      return gutil::InternalErrorBuilder().LogError()
             << "Unexpected element size in response (should be > 0): "
             << u.path().elem_size();

    for (const auto& e : u.path().elem()) {
      elements.push_back(e.name());
    }
  }
  return elements;
}

absl::StatusOr<std::vector<std::string>> GetUpInterfacesOverGnmi(
    gnmi::gNMI::StubInterface& stub, InterfaceType type,
    absl::Duration timeout) {
  ASSIGN_OR_RETURN(
      const auto interfaces,
      GetMatchingInterfacesAsProto(
          stub, gnmi::GetRequest::STATE,
          [type](const openconfig::Interfaces::Interface& interface) {
            const auto& state = interface.state();
            if (state.p4rt_id() == 0) return false;
            if (state.cpu() || state.management()) return false;
            switch (type) {
              case InterfaceType::kAny:
                return true;
              case InterfaceType::kSingleton:
                return absl::EndsWithIgnoreCase(state.type(), "ethernetCsmacd");
              case InterfaceType::kLag:
                return absl::EndsWithIgnoreCase(state.type(), "ieee8023adLag");
              case InterfaceType::kLoopback:
                return absl::EndsWithIgnoreCase(state.type(),
                                                "softwareLoopback");
            }
            return false;  // Should never be hit.
          },
          timeout));

  std::vector<std::string> up_interfaces;
  for (const openconfig::Interfaces::Interface& interface :
       interfaces.interfaces()) {
    if (interface.state().oper_status() == "UP") {
      up_interfaces.push_back(interface.name());
    }
  }
  return up_interfaces;
}

absl::StatusOr<absl::flat_hash_set<std::string>> GetConfigDisabledInterfaces(
    gnmi::gNMI::StubInterface& stub) {
  absl::flat_hash_set<std::string> disabled_interfaces;
  ASSIGN_OR_RETURN(auto all_interfaces, pins_test::GetInterfacesAsProto(
                                            stub, gnmi::GetRequest::CONFIG));
  for (const auto& interface : all_interfaces.interfaces()) {
    if (interface.config().enabled() == false) {
      disabled_interfaces.insert(interface.name());
    }
  }
  return disabled_interfaces;
}

absl::StatusOr<absl::flat_hash_set<std::string>> GetConfigEnabledInterfaces(
    gnmi::gNMI::StubInterface& stub) {
  absl::flat_hash_set<std::string> enabled_interfaces;
  ASSIGN_OR_RETURN(auto all_interfaces, pins_test::GetInterfacesAsProto(
                                            stub, gnmi::GetRequest::CONFIG));
  for (const auto& interface : all_interfaces.interfaces()) {
    if (interface.config().enabled() == true) {
      enabled_interfaces.insert(interface.name());
    }
  }
  return enabled_interfaces;
}

absl::StatusOr<OperStatus> GetInterfaceOperStatusOverGnmi(
    gnmi::gNMI::StubInterface& stub, absl::string_view if_name) {
  std::string if_req = absl::StrCat("interfaces/interface[name=", if_name,
                                    "]/state/oper-status");
  ASSIGN_OR_RETURN(auto request,
                   BuildGnmiGetRequest(if_req, gnmi::GetRequest::STATE));
  ASSIGN_OR_RETURN(
      gnmi::GetResponse response,
      SendGnmiGetRequest(&stub, request, /*timeout=*/std::nullopt));

  if (response.notification_size() != 1 ||
      response.notification(0).update_size() != 1) {
    return absl::InternalError(
        absl::StrCat("Invalid response: ", response.DebugString()));
  }
  ASSIGN_OR_RETURN(
      std::string oper_status,
      ParseGnmiGetResponse(response, "openconfig-interfaces:oper-status"));

  if (absl::StrContains(oper_status, "UP")) {
    return OperStatus::kUp;
  }
  if (absl::StrContains(oper_status, "DOWN")) {
    return OperStatus::kDown;
  }
  if (absl::StrContains(oper_status, "TESTING")) {
    return OperStatus::kTesting;
  }
  if (absl::StrContains(oper_status, "NOT_PRESENT")) {
    return OperStatus::kNotPresent;
  }
  return OperStatus::kUnknown;
}

absl::StatusOr<AdminStatus> GetInterfaceAdminStatusOverGnmi(
    gnmi::gNMI::StubInterface& stub, absl::string_view if_name) {
  std::string if_req = absl::StrCat("interfaces/interface[name=", if_name,
                                    "]/state/admin-status");
  ASSIGN_OR_RETURN(auto request,
                   BuildGnmiGetRequest(if_req, gnmi::GetRequest::STATE));
  ASSIGN_OR_RETURN(
      gnmi::GetResponse response,
      SendGnmiGetRequest(&stub, request, /*timeout=*/std::nullopt));

  if (response.notification_size() != 1 ||
      response.notification(0).update_size() != 1) {
    return absl::InternalError(
        absl::StrCat("Invalid response: ", response.DebugString()));
  }
  ASSIGN_OR_RETURN(
      std::string admin_status,
      ParseGnmiGetResponse(response, "openconfig-interfaces:admin-status"));

  if (absl::StrContains(admin_status, "UP")) {
    return AdminStatus::kUp;
  }
  if (absl::StrContains(admin_status, "DOWN")) {
    return AdminStatus::kDown;
  }
  if (absl::StrContains(admin_status, "TESTING")) {
    return AdminStatus::kTesting;
  }
  return AdminStatus::kUnknown;
}

absl::StatusOr<openconfig::Interfaces> GetInterfacesAsProto(
    gnmi::gNMI::StubInterface& stub, gnmi::GetRequest::DataType type,
    absl::Duration timeout) {
  ASSIGN_OR_RETURN(auto request, BuildGnmiGetRequest("interfaces", type));
  ASSIGN_OR_RETURN(gnmi::GetResponse response,
                   SendGnmiGetRequest(&stub, request, timeout));

  ASSIGN_OR_RETURN(openconfig::Config config,
                   gutil::ParseJsonAsProto<openconfig::Config>(
                       response.notification(0).update(0).val().json_ietf_val(),
                       /*ignore_unknown_fields=*/true));
  return config.interfaces();
}

absl::StatusOr<std::string> GetGnmiConfig(
    gnmi::gNMI::StubInterface& gnmi_stub) {
  ASSIGN_OR_RETURN(
      gnmi::GetRequest request,
      pins_test::BuildGnmiGetRequest(/*oc_path=*/"", gnmi::GetRequest::CONFIG));
  gnmi::GetResponse response;
  grpc::ClientContext context;
  RETURN_IF_ERROR(gutil::GrpcStatusToAbslStatus(
      gnmi_stub.Get(&context, request, &response)));
  // Pretty print the full gNMI config using 2 spaces as a tab.
  return ParseGnmiGetResponse(response, /*match_tag=*/{}, /*indent=*/2);
}

absl::StatusOr<openconfig::Interfaces> GetMatchingInterfacesAsProto(
    gnmi::gNMI::StubInterface& stub, gnmi::GetRequest::DataType type,
    std::function<bool(const openconfig::Interfaces::Interface&)> predicate,
    absl::Duration timeout) {
  ASSIGN_OR_RETURN(const openconfig::Interfaces interfaces,
                   GetInterfacesAsProto(stub, type, timeout));

  openconfig::Interfaces matching_interfaces;
  absl::c_copy_if(
      interfaces.interfaces(),
      RepeatedFieldBackInserter(matching_interfaces.mutable_interfaces()),
      predicate);
  return matching_interfaces;
}

absl::StatusOr<std::vector<P4rtPortId>> GetMatchingP4rtPortIds(
    gnmi::gNMI::StubInterface& stub,
    std::function<bool(const openconfig::Interfaces::Interface&)> predicate) {
  ASSIGN_OR_RETURN(
      const pins_test::openconfig::Interfaces interfaces,
      GetMatchingInterfacesAsProto(stub, gnmi::GetRequest::STATE, predicate));

  std::vector<P4rtPortId> ports;
  for (const auto& interface : interfaces.interfaces()) {
    if (interface.state().has_p4rt_id()) {
      ports.push_back(
          P4rtPortId::MakeFromOpenConfigEncoding(interface.state().p4rt_id()));
    }
  }
  absl::c_sort(ports);
  return ports;
}

bool IsEnabledEthernetInterface(
    const openconfig::Interfaces::Interface& interface) {
  return (interface.state().enabled() || interface.config().enabled()) &&
         absl::StartsWith(interface.name(), "Ethernet");
}

absl::StatusOr<absl::flat_hash_map<std::string, std::string>>
GetAllEnabledInterfaceNameToPortId(gnmi::gNMI::StubInterface& stub,
                                   absl::Duration timeout) {
  // Gets the config path for all interfaces.
  ASSIGN_OR_RETURN(
      openconfig::Interfaces interfaces,
      GetInterfacesAsProto(stub, gnmi::GetRequest::CONFIG, timeout));

  absl::flat_hash_map<std::string, std::string> port_id_by_interface;
  for (const openconfig::Interfaces::Interface& interface :
       interfaces.interfaces()) {
    // Only return enabled ports.
    if (interface.config().enabled()) {
      port_id_by_interface[interface.name()] =
          absl::StrCat(interface.config().p4rt_id());
    }
  }
  return port_id_by_interface;
}

absl::StatusOr<absl::flat_hash_map<std::string, std::string>>
GetAllUpInterfacePortIdsByName(gnmi::gNMI::StubInterface& stub,
                               absl::Duration timeout) {
  ASSIGN_OR_RETURN(std::vector<std::string> up_interfaces,
                   GetUpInterfacesOverGnmi(stub, timeout));
  ASSIGN_OR_RETURN(auto port_id_by_name, GetAllInterfaceNameToPortId(stub));

  absl::flat_hash_map<std::string, std::string> result;
  for (const auto& interface : up_interfaces) {
    if (auto it = port_id_by_name.find(interface);
        it != port_id_by_name.end()) {
      result[it->first] = it->second;
      VLOG(1) << "Found: " << it->first << " which is UP and has port ID "
              << it->second << ".";
    }
  }
  return result;
}

absl::StatusOr<std::string> GetAnyUpInterfacePortId(
    gnmi::gNMI::StubInterface& stub, absl::Duration timeout) {
  ASSIGN_OR_RETURN(auto ids,
                   GetNUpInterfacePortIds(stub, /*num_interfaces=*/1, timeout));
  return ids[0];
}

absl::StatusOr<std::vector<std::string>> GetNUpInterfacePortIds(
    gnmi::gNMI::StubInterface& stub, int num_interfaces,
    absl::Duration timeout) {
  ASSIGN_OR_RETURN(auto ids_by_name,
                   GetAllUpInterfacePortIdsByName(stub, timeout));
  std::vector<std::string> result;
  for (const auto& [name, id] : ids_by_name) {
    LOG(INFO) << "Selecting interface " << name << " with ID " << id << ".";
    result.push_back(id);
    if (result.size() == num_interfaces) {
      return result;
    }
  }
  return absl::FailedPreconditionError(
      absl::StrCat("Could not find ", num_interfaces,
                   " interfaces that are UP with a port ID."));
}

absl::StatusOr<std::vector<std::string>> GetInterfaceNamesForGivenPortNumber(
    gnmi::gNMI::StubInterface& stub, absl::string_view port_number) {
  ASSIGN_OR_RETURN(gnmi::GetResponse response,
                   pins_test::GetAllInterfaceOverGnmi(stub, absl::Seconds(60)));
  if (response.notification_size() < 1) {
    return absl::InternalError(
        absl::StrCat("Invalid response: ", response.DebugString()));
  }
  const nlohmann::basic_json<> response_json =
      json::parse(response.notification(0).update(0).val().json_ietf_val());

  const auto oc_intf_json =
      response_json.find("openconfig-interfaces:interfaces");
  if (oc_intf_json == response_json.end()) {
    return absl::NotFoundError(
        absl::StrCat("'openconfig-interfaces:interfaces' not found: ",
                     response_json.dump()));
  }
  auto oc_intf_list_json = oc_intf_json->find("interface");
  if (oc_intf_list_json == oc_intf_json->end()) {
    return absl::NotFoundError(
        absl::StrCat("'interface' not found: ", oc_intf_json->dump()));
  }

  std::vector<std::string> interface_names_for_port_number;
  for (const auto& element : oc_intf_list_json->items()) {
    const auto element_name_json = element.value().find("name");
    if (element_name_json == element.value().end()) {
      return absl::NotFoundError(
          absl::StrCat("'name' not found: ", element.value().dump()));
    }
    std::string name = element_name_json->get<std::string>();
    if (name.empty()) {
      continue;
    }
    const std::string kPortIdRegex =
        absl::StrCat("^Ethernet1/", port_number, "(/.*|$)");
    if (RE2::FullMatch(name, kPortIdRegex)) {
      interface_names_for_port_number.push_back(name);
    }
  }
  return interface_names_for_port_number;
}

absl::StatusOr<absl::flat_hash_map<std::string, std::string>>
GetAllInterfaceNameToPortId(
    absl::string_view gnmi_config, absl::string_view field_type,
    absl::AnyInvocable<bool(const PortIdByNameIterType&)> filter) {
  ASSIGN_OR_RETURN(auto result,
                   GetPortNameToIdMapFromJsonString(gnmi_config, field_type));
  absl::erase_if(result, std::move(filter));
  return result;
}

absl::StatusOr<absl::flat_hash_map<std::string, std::string>>
GetAllInterfaceNameToPortId(
    gnmi::gNMI::StubInterface& stub, absl::string_view field_type,
    absl::AnyInvocable<bool(const PortIdByNameIterType&)> filter) {
  ASSIGN_OR_RETURN(gnmi::GetResponse response,
                   pins_test::GetAllInterfaceOverGnmi(stub, absl::Seconds(60)));
  if (response.notification_size() < 1) {
    return absl::InternalError(
        absl::StrCat("Invalid response: ", response.DebugString()));
  }
  return GetAllInterfaceNameToPortId(
      response.notification(0).update(0).val().json_ietf_val(), field_type,
      std::move(filter));
}

absl::StatusOr<std::vector<std::string>> GetNEthernetInterfacePortIds(
    gnmi::gNMI::StubInterface& stub, int num_interfaces) {
  ASSIGN_OR_RETURN(auto ids_by_name, GetAllInterfaceNameToPortId(stub));
  std::vector<std::string> result;
  result.reserve(num_interfaces);
  for (const auto& [name, id] : ids_by_name) {
    if (!absl::StartsWith(name, "Ethernet")) {
      continue;
    }
    LOG(INFO) << "Selecting interface " << name << " with ID " << id << ".";
    result.push_back(id);
    if (result.size() == num_interfaces) {
      return result;
    }
  }
  return absl::FailedPreconditionError(absl::StrCat(
      "Could not find ", num_interfaces, " interfaces with a port ID."));
}

absl::Status MapP4rtIdsToMatchingInterfaces(
    gnmi::gNMI::StubInterface& gnmi_stub,
    const absl::btree_set<int>& desired_p4rt_ids,
    std::function<bool(const openconfig::Interfaces::Interface&)> predicate,
    absl::Duration timeout) {
  // Gets the config path for all interfaces matching the predicate.
  ASSIGN_OR_RETURN(
      const openconfig::Interfaces existing_interfaces,
      GetMatchingInterfacesAsProto(gnmi_stub, gnmi::GetRequest::CONFIG,
                                   predicate, timeout));

  // If there are more desired P4RT IDs than matching interfaces, then we return
  // an error.
  if (desired_p4rt_ids.size() > existing_interfaces.interfaces_size()) {
    return absl::InvalidArgumentError(absl::Substitute(
        "requested '$0' P4RT IDs, but only '$1' interfaces matching the given "
        "predicate are configured on switch",
        desired_p4rt_ids.size(), existing_interfaces.interfaces_size()));
  }

  // Collect the interfaces that do not already map a desired P4RT ID as well as
  // those ids that have not yet been mapped.
  std::vector<openconfig::Interfaces::Interface> changeable_interfaces;
  absl::btree_set<int> remaining_desired_p4rt_ids(desired_p4rt_ids);
  for (const auto& interface : existing_interfaces.interfaces()) {
    if (interface.config().has_p4rt_id() &&
        desired_p4rt_ids.contains(interface.config().p4rt_id())) {
      remaining_desired_p4rt_ids.erase(interface.config().p4rt_id());
    } else {
      changeable_interfaces.push_back(interface);
    }
  }

  // Map each remaining desired P4RT ID to an interface that doesn't map one.
  openconfig::Interfaces interfaces_to_change;
  for (int desired_id : remaining_desired_p4rt_ids) {
    if (changeable_interfaces.empty()) {
      return absl::InternalError(
          "no changeable interfaces remain even though we already ensured "
          "that there were enough to cover the desired number of P4RT ids");
    }

    changeable_interfaces.back().mutable_config()->set_p4rt_id(desired_id);
    *interfaces_to_change.add_interfaces() =
        std::move(changeable_interfaces.back());
    changeable_interfaces.pop_back();
  }

  // Modify the collected interfaces.
  return SetInterfaceP4rtIds(gnmi_stub, interfaces_to_change);
}

// Sets the P4RT IDs of `interfaces` by:
// 1. Determining which interfaces are already correctly set.
// 2. Deleting the rest of the P4RT IDs from any existing interfaces on the
//    switch (since a P4RT ID can only be mapped to a single interface).
// 3. Setting the P4RT ID of the remaining interfaces that have one.
absl::Status SetInterfaceP4rtIds(gnmi::gNMI::StubInterface& gnmi_stub,
                                 const openconfig::Interfaces& interfaces) {
  // Determine which interfaces need remapping.
  ASSIGN_OR_RETURN(const openconfig::Interfaces& existing_interfaces,
                   GetInterfacesAsProto(gnmi_stub, gnmi::GetRequest::CONFIG));
  std::vector<openconfig::Interfaces::Interface> interfaces_to_modify;

  for (const auto& interface : interfaces.interfaces()) {
    // If the interface is not already correctly mapped in
    // `existing_interfaces`, we add it to `interfaces_to_modify`.
    if (absl::c_none_of(existing_interfaces.interfaces(),
                        [&interface](const auto& existing_interface) {
                          return interface.name() ==
                                     existing_interface.name() &&
                                 interface.config().p4rt_id() ==
                                     existing_interface.config().p4rt_id();
                        })) {
      interfaces_to_modify.push_back(interface);
    }
  }

  // Get the set of P4RT IDs to map.
  absl::btree_set<int> desired_p4rt_ids;
  absl::flat_hash_set<absl::string_view> interface_names;
  for (const auto& interface : interfaces_to_modify) {
    if (interface.config().has_p4rt_id()) {
      desired_p4rt_ids.insert(interface.config().p4rt_id());
      interface_names.insert(interface.name());
    }
  }

  // Ensure all interfaces that are being set exist.
  for (const auto& interface : existing_interfaces.interfaces()) {
    interface_names.erase(interface.name());
  }
  if (!interface_names.empty()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "expected only interfaces that exist on switch, but also got: "
           << absl::StrJoin(interface_names, ", ") << ".";
  }

  // Delete `desired_p4rt_ids` from existing interfaces.
  for (const auto& interface : existing_interfaces.interfaces()) {
    if (desired_p4rt_ids.contains(interface.config().p4rt_id())) {
      RETURN_IF_ERROR(DeleteInterfaceP4rtId(gnmi_stub, interface))
          << "failed to delete interface " << interface.name() << "'s P4RT id.";
    }
  }

  // Then, set the P4RT IDs for all given `interfaces`.
  for (const auto& interface : interfaces_to_modify) {
    if (interface.config().has_p4rt_id()) {
      RETURN_IF_ERROR(ModifyInterfaceP4rtId(gnmi_stub, interface))
          << "failed to delete, then set interface " << interface.name()
          << " to " << interface.config().p4rt_id() << ".";
    }
  }
  return absl::OkStatus();
}

absl::StatusOr<absl::btree_set<std::string>> GetAllPortIds(
    absl::string_view gnmi_config) {
  ASSIGN_OR_RETURN(auto interface_name_to_port_id,
                   GetAllInterfaceNameToPortId(gnmi_config));

  absl::btree_set<std::string> port_ids;
  for (const auto& [_, port_id] : interface_name_to_port_id) {
    port_ids.insert(port_id);
  }
  return port_ids;
}

absl::StatusOr<absl::btree_set<std::string>> GetAllPortIds(
    gnmi::gNMI::StubInterface& stub) {
  ASSIGN_OR_RETURN(auto interface_name_to_port_id,
                   GetAllInterfaceNameToPortId(stub));

  absl::btree_set<std::string> port_ids;
  for (const auto& [_, port_id] : interface_name_to_port_id) {
    port_ids.insert(port_id);
  }
  return port_ids;
}

absl::StatusOr<std::vector<std::string>> ParseAlarms(
    const std::string& alarms_json) {
  auto alarms_array = json::parse(alarms_json);
  if (!alarms_array.is_array()) {
    return absl::InvalidArgumentError(
        "Input JSON should be an array of alarms.");
  }

  std::vector<std::string> alarm_messages;
  for (const auto& alarm : alarms_array) {
    auto state = alarm.find("state");
    if (state == alarm.end()) {
      return absl::InvalidArgumentError(
          "Input JSON alarm does not have a state field.");
    }

    // The state of an alarm will look like:
    // {
    //   "id": ...
    //   "resource": "linkqual:linkqual"
    //   "severity": "openconfig-alarm-types:WARNING"
    //   "text": "INACTIVE: Unknown"
    //   "time-created": ...
    //   "type-id": "Software Error"
    // }
    //
    // We can build an error message to look like (missing fields will be
    // omitted):
    // [linkqual:linkqual WARNING] Software Error INACTIVE: Unknown
    std::string message = "[";
    auto resource = state->find("resource");
    if (resource != state->end()) {
      absl::StrAppend(&message, StripQuotes(resource->dump()), " ");
    }
    auto severity = state->find("severity");
    if (severity != state->end()) {
      // We only need the last part.
      std::vector<std::string> parts =
          absl::StrSplit(StripQuotes(severity->dump()), ':');
      absl::StrAppend(&message, parts.back());
    }
    absl::StrAppend(&message, "] ");
    auto type_id = state->find("type-id");
    if (type_id != state->end()) {
      absl::StrAppend(&message, StripQuotes(type_id->dump()), " ");
    }
    auto text = state->find("text");
    if (text != state->end()) {
      absl::StrAppend(&message, StripQuotes(text->dump()));
    }
    alarm_messages.push_back(std::move(message));
  }
  return alarm_messages;
}

absl::StatusOr<std::vector<std::string>> GetAlarms(
    gnmi::gNMI::StubInterface& gnmi_stub) {
  ASSIGN_OR_RETURN(
      gnmi::GetRequest request,
      BuildGnmiGetRequest("system/alarms", gnmi::GetRequest::STATE));
  LOG(INFO) << "Sending GET request: " << request.ShortDebugString();
  ASSIGN_OR_RETURN(
      gnmi::GetResponse response,
      SendGnmiGetRequest(&gnmi_stub, request, /*timeout=*/std::nullopt));

  if (response.notification_size() != 1) {
    return gutil::InternalErrorBuilder().LogError()
           << "Unexpected size in response (should be 1): "
           << response.notification_size();
  }
  if (response.notification(0).update_size() != 1) {
    return gutil::InternalErrorBuilder().LogError()
           << "Unexpected update size in response (should be 1): "
           << response.notification(0).update_size();
  }

  const auto response_json =
      json::parse(response.notification(0).update(0).val().json_ietf_val());
  const auto alarms_json = response_json.find("openconfig-system:alarms");
  // If alarms returns an empty subtree, assume no alarms and return an empty
  // list.
  if (alarms_json == response_json.end()) {
    return std::vector<std::string>();
  }

  const auto alarm_json = alarms_json->find("alarm");
  if (alarm_json == alarms_json->end()) {
    return std::vector<std::string>();
  }
  return ParseAlarms(alarm_json->dump());
}

absl::StatusOr<gnmi::GetResponse> GetAllSystemProcesses(
    gnmi::gNMI::StubInterface& gnmi_stub) {
  ASSIGN_OR_RETURN(
      gnmi::GetRequest request,
      BuildGnmiGetRequest("system/processes", gnmi::GetRequest::STATE));
  LOG(INFO) << "Sending GET request: " << request.ShortDebugString();
  return SendGnmiGetRequest(&gnmi_stub, request, /*timeout=*/std::nullopt);
}

absl::StatusOr<gnmi::GetResponse> GetSystemMemory(
    gnmi::gNMI::StubInterface& gnmi_stub) {
  ASSIGN_OR_RETURN(
      gnmi::GetRequest request,
      BuildGnmiGetRequest("system/memory", gnmi::GetRequest::STATE));
  LOG(INFO) << "Sending GET request: " << request.ShortDebugString();
  return SendGnmiGetRequest(&gnmi_stub, request, /*timeout=*/std::nullopt);
}

absl::string_view StripQuotes(absl::string_view string) {
  return absl::StripPrefix(absl::StripSuffix(string, "\""), "\"");
}

absl::string_view StripBrackets(absl::string_view string) {
  return absl::StripPrefix(absl::StripSuffix(string, "]"), "[");
}

absl::StatusOr<absl::btree_set<std::string>>
GetP4rtIdOfInterfacesInAsicMacLocalLoopbackMode(
    gnmi::gNMI::StubInterface& gnmi_stub) {
  ASSIGN_OR_RETURN(
      std::string response,
      pins_test::GetGnmiStatePathInfo(&gnmi_stub, "interfaces",
                                      "openconfig-interfaces:interfaces"));

  json response_json = json::parse(response);
  ASSIGN_OR_RETURN(json interfaces, GetField(response_json, "interface"));

  absl::btree_set<std::string> loopback_mode_set;
  for (const auto& interface : interfaces.items()) {
    ASSIGN_OR_RETURN(json state, GetField(interface.value(), "state"));

    // Skip if the state doesn't have loopback-mode.
    if (state.find("loopback-mode") == state.end()) {
      continue;
    }
    ASSIGN_OR_RETURN(json loopback_mode, GetField(state, "loopback-mode"));
    if (loopback_mode.get<std::string>() == "ASIC_MAC_LOCAL") {
      if (state.find("openconfig-p4rt:id") == state.end()) {
        return gutil::InternalErrorBuilder().LogError()
               << "openconfig-p4rt:id is missing in gNMI configuration and is "
                  "required for ASIC_MAC_LOCAL loopback mode.";
      }
      ASSIGN_OR_RETURN(json port, GetField(state, "openconfig-p4rt:id"));
      P4rtPortId p4rt_port_id =
          P4rtPortId::MakeFromOpenConfigEncoding(port.get<int>());
      loopback_mode_set.insert(p4rt_port_id.GetP4rtEncoding());
    }
  }
  return loopback_mode_set;
}

absl::StatusOr<bool> GetTransceiverQualifiedForInterface(
    gnmi::gNMI::StubInterface& gnmi_stub, absl::string_view interface_name) {
  std::string state_path =
      absl::StrCat("interfaces/interface[name=", interface_name,
                   "]/ethernet/state/transceiver-qualified");
  ASSIGN_OR_RETURN(std::string response,
                   pins_test::GetGnmiStatePathInfo(&gnmi_stub, state_path));
  json response_json = json::parse(response);
  ASSIGN_OR_RETURN(
      json transceiver_qualified,
      GetField(response_json, "google-pins-interfaces:transceiver-qualified"));
  return transceiver_qualified.get<bool>();
}

absl::StatusOr<absl::flat_hash_map<std::string, std::string>>
GetInterfaceToTransceiverMap(gnmi::gNMI::StubInterface& gnmi_stub) {
  ASSIGN_OR_RETURN(
      std::string response,
      pins_test::GetGnmiStatePathInfo(&gnmi_stub, "interfaces",
                                      "openconfig-interfaces:interfaces"));
  json response_json = json::parse(response);
  ASSIGN_OR_RETURN(json interfaces, GetField(response_json, "interface"));

  absl::flat_hash_map<std::string, std::string> interface_to_transceiver;
  for (const auto& interface : interfaces.items()) {
    ASSIGN_OR_RETURN(json name, GetField(interface.value(), "name"));
    if (!absl::StartsWith(name.get<std::string>(), "Ethernet")) {
      continue;
    }

    ASSIGN_OR_RETURN(json state, GetField(interface.value(), "state"));
    ASSIGN_OR_RETURN(
        json transceiver,
        GetField(state, "openconfig-platform-transceiver:transceiver"));
    interface_to_transceiver[name.get<std::string>()] =
        transceiver.get<std::string>();
  }
  return interface_to_transceiver;
}

absl::StatusOr<bool> GetModuleIsPopulatedForInterface(
    gnmi::gNMI::StubInterface& gnmi_stub, absl::string_view interface_name) {
  std::string state_path = absl::StrCat(
      "components/component[name=", interface_name, "]/state/empty");
  ASSIGN_OR_RETURN(std::string response,
                   pins_test::GetGnmiStatePathInfo(&gnmi_stub, state_path));
  json response_json = json::parse(response);
  ASSIGN_OR_RETURN(json empty,
                   GetField(response_json, "openconfig-platform:empty"));
  return !empty.get<bool>();
}

absl::StatusOr<absl::flat_hash_map<std::string, TransceiverPart>>
GetTransceiverPartInformation(gnmi::gNMI::StubInterface& gnmi_stub) {
  ASSIGN_OR_RETURN(std::string response, pins_test::GetGnmiStatePathInfo(
                                             &gnmi_stub, "components",
                                             "openconfig-platform:components"));
  json response_json = json::parse(response);
  ASSIGN_OR_RETURN(json components, GetField(response_json, "component"));

  absl::flat_hash_map<std::string, TransceiverPart> part_information;
  for (const auto& component : components.items()) {
    ASSIGN_OR_RETURN(json name, GetField(component.value(), "name"));
    if (!absl::StartsWith(name.get<std::string>(), "Ethernet")) {
      continue;
    }

    ASSIGN_OR_RETURN(json state, GetField(component.value(), "state"));
    ASSIGN_OR_RETURN(json empty, GetField(state, "empty"));
    if (empty.get<bool>()) {
      continue;
    }

    // TODO: vendor-name may not be present.
    std::string vendor = state.value("openconfig-platform-ext:vendor-name", "");
    ASSIGN_OR_RETURN(json part_number, GetField(state, "part-no"));
    ASSIGN_OR_RETURN(json manufactuer_name, GetField(state, "mfg-name"));
    ASSIGN_OR_RETURN(json serial_number, GetField(state, "serial-no"));
    ASSIGN_OR_RETURN(json rev, GetField(state, "firmware-version"));
    part_information[name.get<std::string>()] = TransceiverPart{
	.vendor = std::move(vendor),
        .part_number = part_number.get<std::string>(),
        .manufacturer_name = manufactuer_name.get<std::string>(),
        .serial_number = serial_number.get<std::string>(),
        .rev = rev.get<std::string>(),
    };
  }
  return part_information;
}

// We cannot "replace" the node-id value directly because if the
// "integrated_circuit0" component doesn't exist the gNMI set path will reject
// the request. Instead we "update" just the node-id, but include the entire
// "integrated_circuit0" component as part of the value. This way if it doesn't
// exist gNMI will create a new component and set the node-id. If it does exist
// gNMI will simply update the value in the existing component.
absl::Status SetDeviceId(gnmi::gNMI::StubInterface& gnmi_stub,
                         uint32_t device_id) {
  std::string config_value = absl::Substitute(
      R"json({
        "component" : [
          {
            "integrated-circuit" : {
              "config" : {
                "openconfig-p4rt:node-id" : "$0"
              }
            },
            "name" : "integrated_circuit0"
          }
        ]
      })json",
      device_id);
  RETURN_IF_ERROR(SetGnmiConfigPath(&gnmi_stub,
                                    /*config_path=*/"components/component",
                                    GnmiSetType::kUpdate, config_value));
  return absl::OkStatus();
}

absl::StatusOr<uint64_t> GetDeviceId(gnmi::gNMI::StubInterface& gnmi_stub) {

  // If the gnmi does not support getting the node-id, return device id as 1
  // TODO(PINS): To be removed when get device id is supported
  if (!absl::GetFlag(FLAGS_gnmi_deviceid_support)) {
    return (uint64_t) 1;
  }

  ASSIGN_OR_RETURN(
      gnmi::GetRequest request,
      BuildGnmiGetRequest("components/component[name=integrated_circuit0]/"
                          "integrated-circuit/state/node-id",
                          gnmi::GetRequest::STATE));
  LOG(INFO) << "Sending GET request: " << request.ShortDebugString();
  ASSIGN_OR_RETURN(
      gnmi::GetResponse response,
      SendGnmiGetRequest(&gnmi_stub, request, /*timeout=*/std::nullopt));
  LOG(INFO) << "Received GET response: " << response.ShortDebugString();
  ASSIGN_OR_RETURN(
      std::string p4rt_str,
      pins_test::ParseGnmiGetResponse(response, "openconfig-p4rt:node-id"));
  StripSymbolFromString(p4rt_str, '\"');
  uint64_t p4rt_id;
  if (absl::SimpleAtoi(p4rt_str, &p4rt_id) != true) {
    return gutil::InternalErrorBuilder().LogError()
           << absl::StrCat("P4RT node-id conversion failed for:", p4rt_str);
  }
  return p4rt_id;
}

std::string BreakoutSpeedToString(BreakoutSpeed breakout_speed) {
  switch (breakout_speed) {
    case BreakoutSpeed::k100GB:
      return "100GB";
    case BreakoutSpeed::k200GB:
      return "200GB";
    case BreakoutSpeed::k400GB:
      return "400GB";
    default:
      return absl::StrCat("Unknown breakout speed: ",
                          static_cast<int>(breakout_speed));
  }
}

struct BreakoutSpeedFormatter {
  void operator()(std::string* out, BreakoutSpeed breakout_speed) const {
    out->append(BreakoutSpeedToString(breakout_speed));
  }
};

std::ostream& operator<<(std::ostream& os, const BreakoutMode& breakout) {
  os << absl::StrCat(
      "{", absl::StrJoin(breakout, ", ", BreakoutSpeedFormatter()), "}");
  return os;
}

absl::StatusOr<int> FindPortWithBreakoutMode(
    absl::string_view json_config, const BreakoutMode& breakout,
    const absl::flat_hash_set<int>& ignore_ports) {
  //  Parse the open config as JSON value.
  auto config_json = json::parse(json_config);
  ASSIGN_OR_RETURN(
      const auto& component_array,
      AccessJsonValue(config_json,
                      {"openconfig-platform:components", "component"}));
  LOG(INFO) << "Will search breakout mode to match: " << breakout;
  return FindBreakoutModeFromComponentJsonArray(breakout, component_array,
                                                ignore_ports);
}

absl::StatusOr<std::vector<std::string>> GetInterfacesOnPort(
    absl::string_view json_config, int port_number) {
  //  Parse the open config as JSON value.
  auto config_json = json::parse(json_config);
  ASSIGN_OR_RETURN(
      const auto& interface_array,
      AccessJsonValue(config_json,
                      {"openconfig-interfaces:interfaces", "interface"}));
  LOG(INFO) << "Will search interfaces name with port number: " << port_number;
  return FindInterfacesNameFromInterfaceJsonArray(port_number, interface_array);
}

std::string UpdateDeviceIdInJsonConfig(absl::string_view gnmi_config,
                                       const std::string& device_id) {
  LOG(INFO) << "Forcing P4RT device ID to be '" << device_id << "'.";

  absl::StatusOr<nlohmann::json> json = json_yang::ParseJson(gnmi_config);
  if (!json.ok()) {
    LOG(FATAL) << "unable to parse gNMI config: " << gnmi_config;  // Crash ok
  }
  auto oc_component =
      json->emplace("openconfig-platform:components", json::object()).first;
  auto component_list =
      oc_component->emplace("component", nlohmann::json::array()).first;

  // The Device ID should always be written to integrated_circuit0. If this
  // component exist then we update that field.
  bool found_integrated_circuit = false;
  for (nlohmann::basic_json<>& component : *component_list) {
    if (component["name"] == "integrated_circuit0") {
      found_integrated_circuit = true;
      component["integrated-circuit"]["config"]["openconfig-p4rt:node-id"] =
          device_id;
    }
  }

  // If the integrated_circuit0 object does not exist then we will create it.
  if (!found_integrated_circuit) {
    nlohmann::basic_json<> component = json::object();
    component["name"] = "integrated_circuit0";
    component["integrated-circuit"]["config"]["openconfig-p4rt:node-id"] =
        device_id;
    component_list->insert(component_list->end(), component);
  }
  return json->dump();
}

absl::StatusOr<absl::flat_hash_map<std::string, std::string>>
GetTransceiverToEthernetPmdMap(gnmi::gNMI::StubInterface& gnmi_stub) {
  ASSIGN_OR_RETURN(std::string response, pins_test::GetGnmiStatePathInfo(
                                             &gnmi_stub, "components",
                                             "openconfig-platform:components"));
  json response_json = json::parse(response);
  ASSIGN_OR_RETURN(json components, GetField(response_json, "component"));

  absl::flat_hash_map<std::string, std::string> pmd_types;
  for (const auto& component : components.items()) {
    ASSIGN_OR_RETURN(json name, GetField(component.value(), "name"));
    if (!absl::StartsWith(name.get<std::string>(), "Ethernet")) {
      continue;
    }

    ASSIGN_OR_RETURN(json state, GetField(component.value(), "state"));
    ASSIGN_OR_RETURN(json empty, GetField(state, "empty"));
    if (empty.get<bool>()) {
      continue;
    }

    ASSIGN_OR_RETURN(json transceiver,
                     GetField(component.value(),
                              "openconfig-platform-transceiver:transceiver"));
    ASSIGN_OR_RETURN(json xcvr_state, GetField(transceiver, "state"));
    ASSIGN_OR_RETURN(json ethernet_pmd, GetField(xcvr_state, "ethernet-pmd"));
    pmd_types[name.get<std::string>()] = ethernet_pmd.get<std::string>();
  }
  return pmd_types;
}

absl::StatusOr<absl::flat_hash_map<std::string, std::string>>
GetTransceiverToFormFactorMap(gnmi::gNMI::StubInterface& gnmi_stub) {
  ASSIGN_OR_RETURN(std::string response, pins_test::GetGnmiStatePathInfo(
                                             &gnmi_stub, "components",
                                             "openconfig-platform:components"));
  json response_json = json::parse(response);
  ASSIGN_OR_RETURN(json components, GetField(response_json, "component"));

  absl::flat_hash_map<std::string, std::string> form_factor_types;
  for (const auto& component : components.items()) {
    ASSIGN_OR_RETURN(json name, GetField(component.value(), "name"));
    if (!absl::StartsWith(name.get<std::string>(), "Ethernet")) {
      continue;
    }

    ASSIGN_OR_RETURN(json state, GetField(component.value(), "state"));
    ASSIGN_OR_RETURN(json empty, GetField(state, "empty"));
    if (empty.get<bool>()) {
      continue;
    }

    ASSIGN_OR_RETURN(json transceiver,
                     GetField(component.value(),
                              "openconfig-platform-transceiver:transceiver"));
    ASSIGN_OR_RETURN(json xcvr_state, GetField(transceiver, "state"));
    ASSIGN_OR_RETURN(json form_factor, GetField(xcvr_state, "form-factor"));
    form_factor_types[name.get<std::string>()] = form_factor.get<std::string>();
  }
  return form_factor_types;
}

absl::StatusOr<absl::flat_hash_map<std::string, int>>
GetInterfaceToLaneSpeedMap(gnmi::gNMI::StubInterface& gnmi_stub,
                           absl::flat_hash_set<std::string>& interface_names) {
  // Map of Openconfig SPEED enum strings to integer speed in Kbps (this ensures
  // all speeds are divisible by 8).
  const absl::flat_hash_map<std::string, int> kOcSpeedToInt = {
      {"openconfig-if-ethernet:SPEED_10MB", 10'000},
      {"openconfig-if-ethernet:SPEED_100MB", 100'000},
      {"openconfig-if-ethernet:SPEED_1GB", 1'000'000},
      {"openconfig-if-ethernet:SPEED_2500MB", 2'500'000},
      {"openconfig-if-ethernet:SPEED_5GB", 5'000'000},
      {"openconfig-if-ethernet:SPEED_10GB", 10'000'000},
      {"openconfig-if-ethernet:SPEED_25GB", 25'000'000},
      {"openconfig-if-ethernet:SPEED_40GB", 40'000'000},
      {"openconfig-if-ethernet:SPEED_50GB", 50'000'000},
      {"openconfig-if-ethernet:SPEED_100GB", 100'000'000},
      {"openconfig-if-ethernet:SPEED_200GB", 200'000'000},
      {"openconfig-if-ethernet:SPEED_400GB", 400'000'000},
      {"openconfig-if-ethernet:SPEED_600GB", 600'000'000},
      {"openconfig-if-ethernet:SPEED_800GB", 800'000'000},
  };
  ASSIGN_OR_RETURN(
      std::string response,
      pins_test::GetGnmiStatePathInfo(&gnmi_stub, "interfaces",
                                      "openconfig-interfaces:interfaces"));
  json response_json = json::parse(response);
  ASSIGN_OR_RETURN(json interfaces, GetField(response_json, "interface"));

  absl::flat_hash_map<std::string, int> interface_to_lane_speed;
  for (const auto& interface : interfaces.items()) {
    ASSIGN_OR_RETURN(json name, GetField(interface.value(), "name"));
    if (!interface_names.contains(name.get<std::string>())) {
      continue;
    }
    ASSIGN_OR_RETURN(
        json ethernet,
        GetField(interface.value(), "openconfig-if-ethernet:ethernet"));

    ASSIGN_OR_RETURN(json ethernet_state, GetField(ethernet, "state"));
    ASSIGN_OR_RETURN(json oc_port_speed,
                     GetField(ethernet_state, "port-speed"));
    ASSIGN_OR_RETURN(json state, GetField(interface.value(), "state"));
    ASSIGN_OR_RETURN(
        json physical_channel,
        GetField(state, "openconfig-platform-transceiver:physical-channel"));
    int lanes = physical_channel.size();
    if (lanes == 0) {
      LOG(WARNING) << "Interface " << name.get<std::string>()
                   << " has physical-channel size of 0, skipping.";
      continue;
    }
    auto total_speed_it = kOcSpeedToInt.find(oc_port_speed.get<std::string>());
    if (total_speed_it == kOcSpeedToInt.end()) {
      LOG(WARNING) << "Interface " << name.get<std::string>()
                   << " has unknown speed: "
                   << oc_port_speed.get<std::string>();
      continue;
    }
    int total_speed = total_speed_it->second;
    interface_to_lane_speed[name.get<std::string>()] = total_speed / lanes;
  }
  return interface_to_lane_speed;
}

bool InterfaceSupportsBert(
    absl::string_view interface,
    const absl::flat_hash_map<std::string, int>& interface_to_lane_speed) {
  auto speed_it = interface_to_lane_speed.find(interface);
  if (speed_it == interface_to_lane_speed.end()) {
    LOG(WARNING) << "Interface "
                 << interface << " not found in interface to speed map.";
    return false;
  }

  // Skip BERT if per-lane speed >= 50G.
  int lane_speed = speed_it->second;
  constexpr int k50GSpeedInKbps = 50'000'000;
  if (lane_speed >= k50GSpeedInKbps) {
    LOG(INFO)
        << "Interface "
        << interface << " does not support BERT because per-lane speed is "
        << lane_speed << " kbps.";
    return false;
  }

  // TODO - Remove this once the bug is fixed.
  // Skip BERT for ports 33 and 34.
  if (absl::StrContains(interface, "1/33") ||
      absl::StrContains(interface, "1/34")) {
    return false;
  }

  return true;
}

absl::Status SetPortSpeedInBitsPerSecond(const std::string& port_speed,
                                         const std::string& interface_name,
                                         gnmi::gNMI::StubInterface& gnmi_stub) {
  std::string ops_config_path =
      absl::StrCat("interfaces/interface[name=", interface_name,
                   "]/ethernet/config/port-speed");
  std::string ops_val =
      absl::StrCat("{\"openconfig-if-ethernet:port-speed\":", port_speed, "}");

  RETURN_IF_ERROR(pins_test::SetGnmiConfigPath(&gnmi_stub, ops_config_path,
                                               GnmiSetType::kUpdate, ops_val));

  return absl::OkStatus();
}

absl::Status SetPortSpeedInBitsPerSecond(PortSpeed port_speed,
                                         const std::string& interface_name,
                                         gnmi::gNMI::StubInterface& gnmi_stub) {
  // Map keyed on openconfig speed string to value in bits per second.
  // http://ops.openconfig.net/branches/models/master/docs/openconfig-interfaces.html#mod-openconfig-if-ethernet
  const auto kPortSpeedTable =
      absl::flat_hash_map<uint64_t, absl::string_view>({
          {100000000000, "openconfig-if-ethernet:SPEED_100GB"},
          {200000000000, "openconfig-if-ethernet:SPEED_200GB"},
          {400000000000, "openconfig-if-ethernet:SPEED_400GB"},
      });

  auto oc_speed = kPortSpeedTable.find(static_cast<int64_t>(port_speed));
  if (oc_speed == kPortSpeedTable.end()) {
    return absl::InvalidArgumentError(
        absl::StrCat("Port speed ", port_speed, " not found"));
  }

  std::string ops_val = absl::StrCat(
      "{\"openconfig-if-ethernet:port-speed\": \"", oc_speed->second, "\"}");

  std::string ops_config_path =
      absl::StrCat("interfaces/interface[name=", interface_name,
                   "]/ethernet/config/port-speed");
  RETURN_IF_ERROR(pins_test::SetGnmiConfigPath(&gnmi_stub, ops_config_path,
                                               GnmiSetType::kUpdate, ops_val));

  return absl::OkStatus();
}

absl::StatusOr<int64_t> GetPortSpeedInBitsPerSecond(
    const std::string& interface_name, gnmi::gNMI::StubInterface& gnmi_stub) {
  // Map keyed on openconfig speed string to value in bits per second.
  // http://ops.openconfig.net/branches/models/master/docs/openconfig-interfaces.html#mod-openconfig-if-ethernet
  const auto kPortSpeedTable =
      absl::flat_hash_map<absl::string_view, uint64_t>({
          {"openconfig-if-ethernet:SPEED_100GB", 100000000000},
          {"openconfig-if-ethernet:SPEED_200GB", 200000000000},
          {"openconfig-if-ethernet:SPEED_400GB", 400000000000},
      });
  std::string speed_state_path =
      absl::StrCat("interfaces/interface[name=", interface_name,
                   "]/ethernet/state/port-speed");

  std::string parse_str = "openconfig-if-ethernet:port-speed";
  ASSIGN_OR_RETURN(
      std::string response,
      GetGnmiStatePathInfo(&gnmi_stub, speed_state_path, parse_str));

  auto speed = kPortSpeedTable.find(StripQuotes(response));
  if (speed == kPortSpeedTable.end()) {
    return absl::NotFoundError(response);
  }
  return speed->second;
}

absl::Status SetPortMtu(int port_mtu, const std::string& interface_name,
                        gnmi::gNMI::StubInterface& gnmi_stub) {
  std::string config_path = absl::StrCat(
      "interfaces/interface[name=", interface_name, "]/config/mtu");
  std::string value = absl::StrCat("{\"config:mtu\":", port_mtu, "}");

  RETURN_IF_ERROR(pins_test::SetGnmiConfigPath(&gnmi_stub, config_path,
                                               GnmiSetType::kUpdate, value));

  return absl::OkStatus();
}

absl::StatusOr<bool> CheckLinkUp(const std::string& interface_name,
                                 gnmi::gNMI::StubInterface& gnmi_stub) {
  std::string oper_status_state_path = absl::StrCat(
      "interfaces/interface[name=", interface_name, "]/state/oper-status");

  std::string parse_str = "openconfig-interfaces:oper-status";
  ASSIGN_OR_RETURN(
      std::string ops_response,
      GetGnmiStatePathInfo(&gnmi_stub, oper_status_state_path, parse_str));

  return ops_response == "\"UP\"";
}

absl::Status SetPortLoopbackMode(bool port_loopback,
                                 absl::string_view interface_name,
                                 gnmi::gNMI::StubInterface& gnmi_stub) {
  std::string config_path = absl::StrCat(
      "interfaces/interface[name=", interface_name, "]/config/loopback-mode");
  std::string config_json;
  if (port_loopback) {
    config_json =
        "{\"openconfig-interfaces:loopback-mode\":\"ASIC_MAC_LOCAL\"}";
  } else {
    config_json = "{\"openconfig-interfaces:loopback-mode\":\"NONE\"}";
  }
  return pins_test::SetGnmiConfigPath(&gnmi_stub, config_path,
                                      GnmiSetType::kUpdate, config_json);
}

absl::StatusOr<std::string> GetPortPfcRxEnable(
    const absl::string_view interface_name,
    gnmi::gNMI::StubInterface& gnmi_stub) {
  std::string config_path =
      absl::StrCat("interfaces/interface[name=", interface_name,
                   "]/ethernet/state/pins-interfaces:enable-pfc-rx");
  const std::string parse_str = "pins-interfaces:enable-pfc-rx";

  ASSIGN_OR_RETURN(std::string enable_pfc_rx,
                   GetGnmiStatePathInfo(&gnmi_stub, config_path, parse_str));
  return enable_pfc_rx;
}

absl::Status SetPortPfcRxEnable(const absl::string_view interface_name,
                                std::string port_pfc_rx_enable,
                                gnmi::gNMI::StubInterface& gnmi_stub) {
  std::string config_path =
      absl::StrCat("interfaces/interface[name=", interface_name,
                   "]/ethernet/config/enable-pfc-rx");
  std::string config_json = absl::StrCat(
      "{\"openconfig-interfaces:enable-pfc-rx\":", port_pfc_rx_enable, "}");

  return pins_test::SetGnmiConfigPath(&gnmi_stub, config_path,
                                      GnmiSetType::kUpdate, config_json);
}

absl::StatusOr<absl::flat_hash_map<std::string, Counters>>
GetAllInterfaceCounters(gnmi::gNMI::StubInterface& gnmi_stub) {
  ASSIGN_OR_RETURN(
      gnmi::GetRequest request,
      BuildGnmiGetRequest("interfaces/interface", gnmi::GetRequest::STATE));
  ASSIGN_OR_RETURN(
      gnmi::GetResponse response,
      SendGnmiGetRequest(&gnmi_stub, request, /*timeout=*/std::nullopt));
  ASSIGN_OR_RETURN(
      std::string interface_info,
      ParseGnmiGetResponse(response, "openconfig-interfaces:interface"));
  uint64_t timestamp = response.notification(0).timestamp();
  ASSIGN_OR_RETURN(json interfaces, json_yang::ParseJson(interface_info));
  absl::flat_hash_map<std::string, Counters> counters;
  for (const json& interface : interfaces) {
    ASSIGN_OR_RETURN(json name, GetField(interface, "name"));
    if (!absl::StrContains(name.get<std::string>(), "Ethernet")) {
      continue;
    }
    Counters& port_counters = counters[name.get<std::string>()];
    ASSIGN_OR_RETURN(port_counters, GetCountersForInterface(interface),
                     _.SetPrepend() << name.get<std::string>() << " -> ");
    port_counters.timestamp_ns = timestamp;
  }
  return counters;
}

Counters Counters::operator-(const Counters& other) const {
  return Counters{
      in_pkts - other.in_pkts,
      out_pkts - other.out_pkts,
      in_octets - other.in_octets,
      out_octets - other.out_octets,
      in_unicast_pkts - other.in_unicast_pkts,
      out_unicast_pkts - other.out_unicast_pkts,
      in_multicast_pkts - other.in_multicast_pkts,
      out_multicast_pkts - other.out_multicast_pkts,
      in_broadcast_pkts - other.in_broadcast_pkts,
      out_broadcast_pkts - other.out_broadcast_pkts,
      in_errors - other.in_errors,
      out_errors - other.out_errors,
      in_discards - other.in_discards,
      out_discards - other.out_discards,
      in_buffer_discards - other.in_buffer_discards,
      in_maxsize_exceeded - other.in_maxsize_exceeded,
      in_fcs_errors - other.in_fcs_errors,
      in_ipv4_pkts - other.in_ipv4_pkts,
      out_ipv4_pkts - other.out_ipv4_pkts,
      in_ipv6_pkts - other.in_ipv6_pkts,
      out_ipv6_pkts - other.out_ipv6_pkts,
      in_ipv6_discarded_pkts - other.in_ipv6_discarded_pkts,
      out_ipv6_discarded_pkts - other.out_ipv6_discarded_pkts,
      timestamp_ns - other.timestamp_ns,
  };
}

absl::StatusOr<Counters> GetCountersForInterface(
    absl::string_view interface_name, gnmi::gNMI::StubInterface& gnmi_stub) {
  ASSIGN_OR_RETURN(
      std::string interface_info,
      GetGnmiStatePathInfo(
          &gnmi_stub,
          absl::StrCat("interfaces/interface[name=", interface_name, "]"),
          "openconfig-interfaces:interface"));
  ASSIGN_OR_RETURN(json interface_json, json_yang::ParseJson(interface_info));
  if (!interface_json.is_array() || interface_json.empty()) {
    return absl::InternalError(absl::StrCat(
        "Expecting counters for interface ", interface_name,
        " to have a non-zero JSON array, but got: ", interface_info));
  }
  return GetCountersForInterface(interface_json[0]);
}

absl::StatusOr<uint64_t> GetBadIntervalsCounter(
    absl::string_view interface_name, gnmi::gNMI::StubInterface& gnmi_stub) {
  ASSIGN_OR_RETURN(json port_counters_json,
                   GetBlackholePortCountersJson(interface_name, gnmi_stub));
  return ParseJsonValueAsUint(port_counters_json, {"bad-intervals"});
}

absl::StatusOr<BlackholePortCounters> GetBlackholePortCounters(
    absl::string_view interface_name, gnmi::gNMI::StubInterface& gnmi_stub) {
  ASSIGN_OR_RETURN(json port_counters_json,
                   GetBlackholePortCountersJson(interface_name, gnmi_stub));
  return ParseBlackholePortCounters(port_counters_json);
}

absl::StatusOr<BlackholeSwitchCounters> GetBlackholeSwitchCounters(
    gnmi::gNMI::StubInterface& gnmi_stub) {
  const std::string ops_state_path =
      "components/component[name=integrated_circuit0]/integrated-circuit/state";
  const std::string ops_parse_str = "openconfig-platform:state";
  ASSIGN_OR_RETURN(
      std::string switch_state_info,
      GetGnmiStatePathInfo(&gnmi_stub, ops_state_path, ops_parse_str));

  ASSIGN_OR_RETURN(json switch_state_json,
                   json_yang::ParseJson(switch_state_info));
  ASSIGN_OR_RETURN(BlackholeSwitchCounters switch_counters,
                   ParseBlackholeSwitchCounters(switch_state_json));
  return switch_counters;
}

absl::StatusOr<absl::flat_hash_map<std::string,
                                   absl::flat_hash_map<std::string, uint64_t>>>
GetCongestionQueueCounters(gnmi::gNMI::StubInterface& gnmi_stub) {
  ASSIGN_OR_RETURN(
      gnmi::GetRequest request,
      BuildGnmiGetRequest("qos/interfaces/interface", gnmi::GetRequest::STATE));
  ASSIGN_OR_RETURN(
      gnmi::GetResponse response,
      SendGnmiGetRequest(&gnmi_stub, request, /*timeout=*/std::nullopt));
  ASSIGN_OR_RETURN(std::string interface_info,
                   ParseGnmiGetResponse(response, "openconfig-qos:interface"));
  ASSIGN_OR_RETURN(json interfaces, json_yang::ParseJson(interface_info));
  absl::flat_hash_map<std::string, absl::flat_hash_map<std::string, uint64_t>>
      counters;
  for (const json& interface : interfaces) {
    ASSIGN_OR_RETURN(json pname, GetField(interface, "interface-id"));
    if (!absl::StrContains(pname.get<std::string>(), "Ethernet")) {
      continue;
    }
    ASSIGN_OR_RETURN(json queues,
                     AccessJsonValue(interface, {"output", "queues", "queue"}));
    for (const json& queue : queues) {
      ASSIGN_OR_RETURN(json qname, GetField(queue, "name"));
      absl::StatusOr<uint64_t> counter_val = ParseJsonValueAsUint(
          queue, {"state", "pins-qos:diag", "dropped-packet-events"});

      // Note that the per-queue congestion counter may not be available if
      // the switch is running an older version of the stack, or congestion
      // counters are not enabled, or if the queue is not enabled for congestion
      // counters.
      if (counter_val.ok()) {
        counters[pname.get<std::string>()][qname.get<std::string>()] =
            counter_val.value();
      }
    }
  }
  return counters;
}

absl::StatusOr<uint64_t> GetCongestionQueueCounter(
    absl::string_view interface_name, absl::string_view queue_name,
    gnmi::gNMI::StubInterface& gnmi_stub) {
  const std::string ops_state_path = absl::StrFormat(
      "qos/interfaces/interface[interface-id=%s]/output/queues/queue[name=%s]/"
      "state",
      interface_name, queue_name);
  const std::string kOpsParseStr = "openconfig-qos:state";
  ASSIGN_OR_RETURN(
      std::string queue_state_info,
      GetGnmiStatePathInfo(&gnmi_stub, ops_state_path, kOpsParseStr));

  ASSIGN_OR_RETURN(json queue_state_json,
                   json_yang::ParseJson(queue_state_info));
  ASSIGN_OR_RETURN(
      uint64_t dropped_packet_events,
      ParseJsonValueAsUint(queue_state_json,
                           {"pins-qos:diag", "dropped-packet-events"}));
  return dropped_packet_events;
}

absl::StatusOr<uint64_t> GetCongestionSwitchCounter(
    gnmi::gNMI::StubInterface& gnmi_stub) {
  const std::string kOpsStatePath =
      "components/component[name=integrated_circuit0]/integrated-circuit/state";
  const std::string kOpsParseStr = "openconfig-platform:state";
  const std::string kCongestionSwitchCounterParseKey =
      "pins-platform:congestion";
  ASSIGN_OR_RETURN(
      std::string switch_state_info,
      GetGnmiStatePathInfo(&gnmi_stub, kOpsStatePath, kOpsParseStr));

  ASSIGN_OR_RETURN(json switch_state_json,
                   json_yang::ParseJson(switch_state_info));
  ASSIGN_OR_RETURN(
      uint64_t congestion_events,
      ParseJsonValueAsUint(switch_state_json, {kCongestionSwitchCounterParseKey,
                                               "congestion-events"}));
  return congestion_events;
}

absl::StatusOr<std::string> ParseJsonValue(absl::string_view json) {
  nlohmann::json parsed_json = nlohmann::json::parse(json, nullptr, false);
  if (parsed_json.is_discarded()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Invalid JSON syntax for '" << json << "'";
  }
  if (parsed_json.empty()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Cannot parse empty JSON '" << json << "'";
  }
  return parsed_json.begin().value();
}

absl::StatusOr<uint64_t> GetGnmiSystemUpTime(gnmi::gNMI::StubInterface& stub) {
  ASSIGN_OR_RETURN(auto uptime_str, pins_test::GetGnmiStatePathInfo(
                                        &stub, "/system/state/up-time",
                                        "openconfig-system:up-time"));
  uint64_t uptime;
  if (!absl::SimpleAtoi(std::string(pins_test::StripQuotes(uptime_str)),
                        &uptime)) {
    return absl::InternalError(absl::StrCat("Unable to parse up-time: ", uptime,
                                            ". Not a valid integer."));
  }
  return uptime;
}

absl::StatusOr<std::string> GetOcOsNetworkStackGnmiStatePathInfo(
    gnmi::gNMI::StubInterface& stub, absl::string_view key,
    absl::string_view field) {
  return pins_test::GetGnmiStatePathInfo(
      &stub,
      absl::Substitute("/components/component[name=$0]/state/$1", key, field),
      absl::Substitute("openconfig-platform:$0", field));
}

absl::StatusOr<uint64_t> GetInterfaceCounter(
    absl::string_view stat_name, absl::string_view interface,
    gnmi::gNMI::StubInterface* gnmi_stub) {
  std::string ops_state_path;
  std::string ops_parse_str;

  ops_state_path = absl::StrCat("interfaces/interface[name=", interface,
                                "]/state/counters/", stat_name);
  ops_parse_str = absl::StrCat("openconfig-interfaces:", stat_name);

  ASSIGN_OR_RETURN(
      std::string ops_response,
      GetGnmiStatePathInfo(gnmi_stub, ops_state_path, ops_parse_str));

  uint64_t stat;
  // Skip over the quotes.
  if (!absl::SimpleAtoi(StripQuotes(ops_response), &stat)) {
    return absl::InternalError(
        absl::StrCat("Unable to parse counter from ", ops_response));
  }
  return stat;
}

absl::StatusOr<absl::flat_hash_map<std::string, std::string>>
GetPortNamePerPortId(gnmi::gNMI::StubInterface& gnmi_stub) {
  absl::flat_hash_map<std::string, std::string> port_name_per_port_id;
  ASSIGN_OR_RETURN(auto port_id_per_port_name,
                   pins_test::GetAllInterfaceNameToPortId(gnmi_stub));
  for (const auto& [name, port_id] : port_id_per_port_name) {
    port_name_per_port_id[port_id] = name;
  }
  return port_name_per_port_id;
}

absl::Status SetInterfaceEnabledState(gnmi::gNMI::StubInterface& gnmi_stub,
                                      absl::string_view if_name, bool enabled) {
  const std::string config_value = enabled ? "true" : "false";
  const std::string if_admin_config_path =
      absl::StrCat("interfaces/interface[name=", if_name, "]/config/enabled");
  return SetGnmiConfigPath(&gnmi_stub, if_admin_config_path,
                           pins_test::GnmiSetType::kUpdate,
                           absl::Substitute("{\"enabled\":$0}", config_value));
}

absl::Status VerifyInterfaceOperState(gnmi::gNMI::StubInterface& gnmi_stub,
                                      absl::string_view if_name,
                                      OperStatus desired_state,
                                      absl::Duration timeout) {
  absl::Time end_time = absl::Now() + timeout;
  OperStatus current_state;
  do {
    if (absl::Now() > end_time) {
      return absl::DeadlineExceededError(
          absl::Substitute("Unable to validate interface: $0 to state: $1",
                           if_name, desired_state));
    }
    absl::SleepFor(absl::Seconds(1));
    ASSIGN_OR_RETURN(current_state,
                     GetInterfaceOperStatusOverGnmi(gnmi_stub, if_name));
  } while (current_state != desired_state);
  return absl::OkStatus();
}
}  // namespace pins_test
