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

#include "tests/sflow/sflow_util.h"

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/time.h"
#include "gutil/status.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/utils/json_utils.h"
#include "lib/validator/validator_lib.h"

namespace pins {
namespace {

// --- Sflow gnmi config paths ---

constexpr absl::string_view kSflowGnmiConfigSampleSizePath =
    "/sampling/sflow/config/sample-size";
constexpr absl::string_view kSflowGnmiConfigEnablePath =
    "/sampling/sflow/config/enabled";
constexpr absl::string_view kSflowGnmiConfigInterfaceSampleRatePath =
    "/sampling/sflow/interfaces/interface[name=$0]/config/"
    "ingress-sampling-rate";

// --- Sflow gnmi state paths ---

constexpr absl::string_view kSflowGnmiStateSampleSizePath =
    "/sampling/sflow/state/sample-size";
constexpr absl::string_view kSflowGnmiStateEnablePath =
    "/sampling/sflow/state/enabled";
constexpr absl::string_view kSflowGnmiStateAgentIpPath =
    "/sampling/sflow/state/agent-id-ipv6";
constexpr absl::string_view kSflowGnmiStateInterfaceSampleRatePath =
    "/sampling/sflow/interfaces/interface[name=$0]/state/"
    "ingress-sampling-rate";
constexpr absl::string_view kSflowGnmiStateInterfaceEnablePath =
    "/sampling/sflow/interfaces/interface[name=$0]/state/enabled";
constexpr absl::string_view kSflowGnmiStateCollectorAddressPath =
    "/sampling/sflow/collectors/collector[address=$0][port=$1]/state/address";
constexpr absl::string_view kSflowGnmiStateCollectorPortPath =
    "/sampling/sflow/collectors/collector[address=$0][port=$1]/state/port";

}  // namespace

absl::Status VerifyGnmiStateConverged(gnmi::gNMI::StubInterface* gnmi_stub,
                                      absl::string_view state_path,
                                      absl::string_view expected_value) {
  ASSIGN_OR_RETURN(std::string state_value,
                   pins_test::GetGnmiStatePathInfo(gnmi_stub, state_path));
  if (expected_value == state_value) {
    return absl::OkStatus();
  }
  return absl::FailedPreconditionError(
      absl::StrCat(state_path, " value is ", state_value,
                   ", which is not equal to ", expected_value));
}

absl::Status SetSflowSamplingSize(gnmi::gNMI::StubInterface* gnmi_stub,
                                  int sampling_size, absl::Duration timeout) {
  std::string ops_val = absl::StrCat(
      "{\"openconfig-sampling-sflow:sample-size\":", sampling_size, "}");

  RETURN_IF_ERROR(SetGnmiConfigPath(gnmi_stub, kSflowGnmiConfigSampleSizePath,
                                    pins_test::GnmiSetType::kUpdate, ops_val));

  return pins_test::WaitForCondition(VerifyGnmiStateConverged, timeout,
                                     gnmi_stub, kSflowGnmiStateSampleSizePath,
                                     ops_val);
}

absl::Status SetSflowConfigEnabled(gnmi::gNMI::StubInterface* gnmi_stub,
                                   bool enabled, absl::Duration timeout) {
  std::string ops_val = absl::StrCat("{\"openconfig-sampling-sflow:enabled\":",
                                     (enabled ? "true" : "false"), "}");
  RETURN_IF_ERROR(SetGnmiConfigPath(gnmi_stub, kSflowGnmiConfigEnablePath,
                                    pins_test::GnmiSetType::kUpdate, ops_val));

  return pins_test::WaitForCondition(VerifyGnmiStateConverged, timeout,
                                     gnmi_stub, kSflowGnmiStateEnablePath,
                                     ops_val);
}

absl::Status SetSflowIngressSamplingRate(gnmi::gNMI::StubInterface* gnmi_stub,
                                         absl::string_view interface,
                                         int sampling_rate,
                                         absl::Duration timeout) {
  std::string ops_val = absl::StrCat(
      "{\"openconfig-sampling-sflow:ingress-sampling-rate\":", sampling_rate,
      "}");

  RETURN_IF_ERROR(SetGnmiConfigPath(
      gnmi_stub,
      absl::Substitute(kSflowGnmiConfigInterfaceSampleRatePath, interface),
      pins_test::GnmiSetType::kUpdate, ops_val));

  return pins_test::WaitForCondition(
      VerifyGnmiStateConverged, timeout, gnmi_stub,
      absl::Substitute(kSflowGnmiStateInterfaceSampleRatePath, interface),
      ops_val);
}

absl::Status VerifySflowStatesConverged(
    gnmi::gNMI::StubInterface* gnmi_stub, absl::string_view agent_addr_ipv6,
    const int sampling_rate, const int sampling_header_size,
    const std::vector<std::pair<std::string, int>>& collector_address_and_port,
    const absl::flat_hash_set<std::string>& sflow_enabled_interfaces) {
  // Verify sFlow global states.
  RETURN_IF_ERROR(VerifyGnmiStateConverged(
      gnmi_stub, kSflowGnmiStateEnablePath,
      /*expected_value=*/
      R"({"openconfig-sampling-sflow:enabled":true})"));
  RETURN_IF_ERROR(VerifyGnmiStateConverged(
      gnmi_stub, kSflowGnmiStateAgentIpPath,
      /*expected_value=*/
      absl::Substitute(R"({"openconfig-sampling-sflow:agent-id-ipv6":"$0"})",
                       agent_addr_ipv6)));
  RETURN_IF_ERROR(VerifyGnmiStateConverged(
      gnmi_stub, kSflowGnmiStateSampleSizePath,
      /*expected_value=*/
      absl::Substitute(R"({"openconfig-sampling-sflow:sample-size":$0})",
                       sampling_header_size)));

  // Verify sFlow collector states.
  for (const auto& [ip_address, port] : collector_address_and_port) {
    const std::string state_address_path =
        absl::Substitute(kSflowGnmiStateCollectorAddressPath, ip_address, port);
    const std::string state_port_path =
        absl::Substitute(kSflowGnmiStateCollectorPortPath, ip_address, port);
    RETURN_IF_ERROR(VerifyGnmiStateConverged(
        gnmi_stub, state_address_path,
        /*expected_value=*/
        absl::Substitute(R"({"openconfig-sampling-sflow:address":"$0"})",
                         ip_address)));
    RETURN_IF_ERROR(VerifyGnmiStateConverged(
        gnmi_stub, state_port_path,
        /*expected_value=*/
        absl::Substitute(R"({"openconfig-sampling-sflow:port":$0})", port)));
  }

  // Verify sFlow interface states.
  for (const auto& interface_name : sflow_enabled_interfaces) {
    const std::string state_enable_path = absl::Substitute(
        kSflowGnmiStateInterfaceEnablePath, interface_name, sampling_rate);
    const std::string state_sampling_rate_path = absl::Substitute(
        kSflowGnmiStateInterfaceSampleRatePath, interface_name, sampling_rate);
    RETURN_IF_ERROR(VerifyGnmiStateConverged(
        gnmi_stub, state_enable_path,
        /*expected_value=*/R"({"openconfig-sampling-sflow:enabled":true})"));
    RETURN_IF_ERROR(VerifyGnmiStateConverged(
        gnmi_stub, state_sampling_rate_path,
        /*expected_value=*/
        absl::Substitute(
            R"({"openconfig-sampling-sflow:ingress-sampling-rate":$0})",
            sampling_rate)));
  }
  return absl::OkStatus();
}

absl::StatusOr<std::string> AppendSflowConfig(
    absl::string_view gnmi_config, absl::string_view agent_addr_ipv6,
    const std::vector<std::pair<std::string, int>>& collector_address_and_port,
    const absl::flat_hash_set<std::string>& sflow_enabled_interfaces,
    const int sampling_rate, const int sampling_header_size) {
  ASSIGN_OR_RETURN(auto gnmi_config_json, json_yang::ParseJson(gnmi_config));
  if (agent_addr_ipv6.empty()) {
    return absl::InvalidArgumentError(
        "loopback_address parameter cannot be empty.");
  }
  if (sflow_enabled_interfaces.empty()) {
    return absl::InvalidArgumentError(
        "sflow_enabled_interfaces parameter cannot be empty.");
  }
  gnmi_config_json["openconfig-sampling:sampling"]
                  ["openconfig-sampling-sflow:sflow"]["config"]["enabled"] =
                      true;
  gnmi_config_json["openconfig-sampling:sampling"]
                  ["openconfig-sampling-sflow:sflow"]["config"]["sample-size"] =
                      sampling_header_size;
  gnmi_config_json["openconfig-sampling:sampling"]
                  ["openconfig-sampling-sflow:sflow"]["config"]
                  ["polling-interval"] = 0;
  gnmi_config_json["openconfig-sampling:sampling"]
                  ["openconfig-sampling-sflow:sflow"]["config"]
                  ["agent-id-ipv6"] = agent_addr_ipv6;
  // Sort collector IPs and interface names by string order to make sure the
  // generated config has a determinisitic order.
  std::vector<std::pair<std::string, int>> sorted_collector_address_and_port =
      collector_address_and_port;
  std::sort(sorted_collector_address_and_port.begin(),
            sorted_collector_address_and_port.end());
  for (const auto& [address, port] : sorted_collector_address_and_port) {
    nlohmann::basic_json<> sflow_collector_config;
    sflow_collector_config["address"] = address;
    sflow_collector_config["port"] = port;
    sflow_collector_config["config"]["address"] = address;
    sflow_collector_config["config"]["port"] = port;
    gnmi_config_json["openconfig-sampling:sampling"]
                    ["openconfig-sampling-sflow:sflow"]["collectors"]
                    ["collector"]
                        .push_back(sflow_collector_config);
  }
  absl::btree_set<std::string> sorted_interface_names(
      sflow_enabled_interfaces.begin(), sflow_enabled_interfaces.end());
  for (const auto& interface_name : sorted_interface_names) {
    nlohmann::basic_json<> sflow_interface_config;
    sflow_interface_config["name"] = interface_name;
    sflow_interface_config["config"]["name"] = interface_name;
    sflow_interface_config["config"]["enabled"] = true;
    sflow_interface_config["config"]["ingress-sampling-rate"] = sampling_rate;
    gnmi_config_json["openconfig-sampling:sampling"]
                    ["openconfig-sampling-sflow:sflow"]["interfaces"]
                    ["interface"]
                        .push_back(sflow_interface_config);
  }
  return json_yang::DumpJson(gnmi_config_json);
}

}  // namespace pins
