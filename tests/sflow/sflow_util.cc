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

#include <cstdint>
#include <string>
#include <vector>

#include "absl/container/btree_map.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/ascii.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "glog/logging.h"
#include "gutil/gutil/status.h"
#include "include/nlohmann/json.hpp"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/utils/json_utils.h"
#include "lib/validator/validator_lib.h"
#include "p4_infra/netaddr/ipv4_address.h"
#include "p4_infra/netaddr/ipv6_address.h"
#include "re2/re2.h"
#include "thinkit/ssh_client.h"

namespace pins {
namespace {

// --- Sflow gnmi config paths ---

constexpr absl::string_view kSflowGnmiConfigSampleSizePath =
    "/sampling/sflow/config/sample-size";
constexpr absl::string_view kSflowGnmiConfigEnablePath =
    "/sampling/sflow/config/enabled";
constexpr absl::string_view kSflowGnmiConfigInterfacePath =
    "/sampling/sflow/interfaces/interface[name=$0]/config/";
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
constexpr absl::string_view kSflowGnmiStateInterfacePath =
    "/sampling/sflow/interfaces/interface[name=$0]/state/";
constexpr absl::string_view kSflowGnmiStateInterfaceSampleRatePath =
    "/sampling/sflow/interfaces/interface[name=$0]/state/"
    "ingress-sampling-rate";
constexpr absl::string_view kSflowGnmiStateInterfaceActualSampleRatePath =
    "/sampling/sflow/interfaces/interface[name=$0]/state/"
    "actual-ingress-sampling-rate";
constexpr absl::string_view kSflowGnmiStateInterfaceEnablePath =
    "/sampling/sflow/interfaces/interface[name=$0]/state/enabled";
constexpr absl::string_view kSflowGnmiStateCollectorAddressPath =
    "/sampling/sflow/collectors/collector[address=$0][port=$1]/state/address";
constexpr absl::string_view kSflowGnmiStateCollectorPortPath =
    "/sampling/sflow/collectors/collector[address=$0][port=$1]/state/port";

// ToS is present in tcp dump like
// ... (class 0x80, ....)
constexpr LazyRE2 kPacketTosMatchPattern{R"(class 0x([a-f0-9]+),)"};

constexpr int kSonicMaxCollector = 2;

}  // namespace

absl::StatusOr<bool> IsSflowConfigEnabled(absl::string_view gnmi_config) {
  ASSIGN_OR_RETURN(auto gnmi_config_json, json_yang::ParseJson(gnmi_config));
  return gnmi_config_json.find("openconfig-sampling:sampling") !=
             gnmi_config_json.end() &&
         gnmi_config_json["openconfig-sampling:sampling"]
                         ["openconfig-sampling-sflow:sflow"]["config"]
                         ["enabled"];
}

absl::Status VerifyGnmiStateConverged(gnmi::gNMI::StubInterface* gnmi_stub,
                                      absl::string_view state_path,
                                      absl::string_view expected_value,
                                      absl::string_view resp_parse_str) {
  ASSIGN_OR_RETURN(
      std::string state_value,
      pins_test::GetGnmiStatePathInfo(gnmi_stub, state_path, resp_parse_str));
  if (expected_value == state_value) {
    return absl::OkStatus();
  }
  return absl::FailedPreconditionError(
      absl::StrCat("State path: [", state_path, "] actual value is ",
                   state_value, ", expected value is ", expected_value));
}

absl::Status SetSflowSamplingSize(gnmi::gNMI::StubInterface* gnmi_stub,
                                  int sampling_size, absl::Duration timeout) {
  std::string ops_val = absl::StrCat(
      "{\"openconfig-sampling-sflow:sample-size\":", sampling_size, "}");

  RETURN_IF_ERROR(SetGnmiConfigPath(gnmi_stub, kSflowGnmiConfigSampleSizePath,
                                    pins_test::GnmiSetType::kUpdate, ops_val));

  return pins_test::WaitForCondition(VerifyGnmiStateConverged, timeout,
                                     gnmi_stub, kSflowGnmiStateSampleSizePath,
                                     ops_val, /*resp_parse_str=*/"");
}

absl::Status SetSflowConfigEnabled(gnmi::gNMI::StubInterface* gnmi_stub,
                                   bool enabled, absl::Duration timeout) {
  std::string ops_val = absl::StrCat("{\"openconfig-sampling-sflow:enabled\":",
                                     (enabled ? "true" : "false"), "}");
  RETURN_IF_ERROR(SetGnmiConfigPath(gnmi_stub, kSflowGnmiConfigEnablePath,
                                    pins_test::GnmiSetType::kUpdate, ops_val));

  return pins_test::WaitForCondition(VerifyGnmiStateConverged, timeout,
                                     gnmi_stub, kSflowGnmiStateEnablePath,
                                     ops_val, /*resp_parse_str=*/"");
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
      ops_val, /*resp_parse_str=*/"");
}

absl::Status SetSflowInterfaceConfig(gnmi::gNMI::StubInterface* gnmi_stub,
                                     absl::string_view interface, bool enabled,
                                     int samping_rate, absl::Duration timeout) {
  RETURN_IF_ERROR(
      SetSflowInterfaceConfigEnable(gnmi_stub, interface, enabled, timeout));
  return SetSflowIngressSamplingRate(gnmi_stub, interface, samping_rate,
                                     timeout);
}

absl::Status SetSflowInterfaceConfigEnable(gnmi::gNMI::StubInterface* gnmi_stub,
                                           absl::string_view interface,
                                           bool enabled,
                                           absl::Duration timeout) {
  const std::string ops_val = absl::Substitute(
      absl::Substitute(R"({"openconfig-sampling-sflow:enabled":$0})",
                       (enabled ? "true" : "false")));
  RETURN_IF_ERROR(SetGnmiConfigPath(
      gnmi_stub,
      absl::Substitute("/sampling/sflow/interfaces/interface[name=$0]/config/"
                       "enabled",
                       interface),
      pins_test::GnmiSetType::kUpdate, ops_val));

  const std::string state_val =
      absl::Substitute(R"({"openconfig-sampling-sflow:enabled":$0})",
                       (enabled ? "true" : "false"));
  return pins_test::WaitForCondition(
      VerifyGnmiStateConverged, timeout, gnmi_stub,
      absl::Substitute(kSflowGnmiStateInterfaceEnablePath, interface),
      state_val,
      /*resp_parse_str=*/"");
}

absl::Status VerifySflowStatesConverged(
    gnmi::gNMI::StubInterface* gnmi_stub, absl::string_view agent_addr_ipv6,
    const int sampling_rate, const int sampling_header_size,
    const std::vector<std::pair<std::string, int>>& collector_address_and_port,
    const absl::flat_hash_map<std::string, bool>& sflow_interfaces) {
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
  for (const auto& [interface_name, enabled] : sflow_interfaces) {
    const std::string state_enable_path =
        absl::Substitute(kSflowGnmiStateInterfaceEnablePath, interface_name);
    const std::string state_sampling_rate_path = absl::Substitute(
        kSflowGnmiStateInterfaceSampleRatePath, interface_name, sampling_rate);
    RETURN_IF_ERROR(VerifyGnmiStateConverged(
        gnmi_stub, state_enable_path,
        /*expected_value=*/
        absl::Substitute(R"({"openconfig-sampling-sflow:enabled":$0})",
                         (enabled ? "true" : "false"))));
    RETURN_IF_ERROR(VerifyGnmiStateConverged(
        gnmi_stub, state_sampling_rate_path,
        /*expected_value=*/
        absl::Substitute(
            R"({"openconfig-sampling-sflow:ingress-sampling-rate":$0})",
            sampling_rate)));
  }
  return absl::OkStatus();
}

absl::StatusOr<std::string> UpdateSflowConfig(
    absl::string_view gnmi_config, absl::string_view agent_addr_ipv6,
    const std::vector<std::pair<std::string, int>>& collector_address_and_port,
    const absl::flat_hash_map<std::string, bool>& sflow_interfaces,
    const int sampling_rate, const int sampling_header_size) {
  ASSIGN_OR_RETURN(auto gnmi_config_json, json_yang::ParseJson(gnmi_config));
  if (agent_addr_ipv6.empty()) {
    return absl::InvalidArgumentError(
        "agent_addr_ipv6 parameter cannot be empty.");
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

  gnmi_config_json["openconfig-sampling:sampling"]
                  ["openconfig-sampling-sflow:sflow"]
                      .erase("collectors");
  if (!collector_address_and_port.empty()) {
    if (collector_address_and_port.size() > kSonicMaxCollector) {
      return absl::InvalidArgumentError(
          absl::StrCat("Number of collectors exceeds max allowed value of ",
                       kSonicMaxCollector));
    }
    nlohmann::json& collector_json_array =
        gnmi_config_json["openconfig-sampling:sampling"]
                        ["openconfig-sampling-sflow:sflow"]["collectors"]
                        ["collector"];
    for (const auto& [address, port] : collector_address_and_port) {
      nlohmann::basic_json<> sflow_collector_config;
      sflow_collector_config["address"] = address;
      sflow_collector_config["port"] = port;
      sflow_collector_config["config"]["address"] = address;
      sflow_collector_config["config"]["port"] = port;
      collector_json_array.push_back(sflow_collector_config);
    }

    if (collector_json_array.size() > kSonicMaxCollector) {
      return absl::InvalidArgumentError(
          absl::StrCat("Number of collectors exceeds max allowed value of ",
                       kSonicMaxCollector));
    }
  }

  absl::btree_map<std::string, nlohmann::json> interface_name_to_config_json;
  for (const auto& [interface_name, enabled] : sflow_interfaces) {
    nlohmann::basic_json<> sflow_interface_config;
    sflow_interface_config["name"] = interface_name;
    sflow_interface_config["enabled"] = enabled;
    sflow_interface_config["ingress-sampling-rate"] = sampling_rate;
    interface_name_to_config_json[interface_name] = sflow_interface_config;
  }
  nlohmann::json& interface_json_array =
      gnmi_config_json["openconfig-sampling:sampling"]
                      ["openconfig-sampling-sflow:sflow"]["interfaces"]
                      ["interface"];
  if (!interface_json_array.empty() &&
      interface_json_array.type() != nlohmann::json::value_t::array) {
    return absl::InvalidArgumentError(
        "json interface field already exists and is not an array.");
  }

  // Modify all existing interface config.
  for (nlohmann::json& interface_json : interface_json_array) {
    std::string interface_name =
        json_yang::GetSimpleJsonValueAsString(interface_json["name"]);
    auto it = interface_name_to_config_json.find(interface_name);
    if (it != interface_name_to_config_json.end()) {
      interface_json["config"] = it->second;
      interface_name_to_config_json.erase(it);
    }
  }

  // Append interface config if any.
  for (const auto& [interface_name, interface_config_json] :
       interface_name_to_config_json) {
    nlohmann::basic_json<> sflow_interface_json;
    sflow_interface_json["name"] = interface_name;
    sflow_interface_json["config"] = interface_config_json;
    interface_json_array.push_back(sflow_interface_json);
  }
  return json_yang::DumpJson(gnmi_config_json);
}

absl::StatusOr<std::string> UpdateQueueLimit(absl::string_view gnmi_config,
                                             absl::string_view queue_name,
                                             int queue_limit) {
  ASSIGN_OR_RETURN(auto config, json_yang::ParseJson(gnmi_config));

  auto& qos_interfaces =
      config["openconfig-qos:qos"]["interfaces"]["interface"];
  std::string cpu_scheduler_policy;
  for (auto& interface : qos_interfaces) {
    if (interface["interface-id"].get<std::string>() == "CPU") {
      cpu_scheduler_policy =
          interface["output"]["scheduler-policy"]["config"]["name"]
              .get<std::string>();
      break;
    }
  }
  if (cpu_scheduler_policy.empty()) {
    return absl::InvalidArgumentError(
        "Gnmi config does not have any cpu scheduler policy.");
  }

  auto& scheduler_policies =
      config["openconfig-qos:qos"]["scheduler-policies"]["scheduler-policy"];
  for (auto& policy : scheduler_policies) {
    if (policy["name"].get<std::string>() == cpu_scheduler_policy) {
      for (auto& scheduler : policy["schedulers"]["scheduler"]) {
        std::string current_queue_name =
            scheduler["inputs"]["input"][0]["config"]["queue"]
                .get<std::string>();
        if (current_queue_name == queue_name) {
          std::string peak_rate = scheduler["two-rate-three-color"]["config"]
                                           ["google-pins-qos:pir-pkts"]
                                               .get<std::string>();
          LOG(INFO) << "Re-configuring Queue[" << current_queue_name
                    << "] rate from <" << peak_rate << "> to <" << queue_limit
                    << ">.";
          scheduler["two-rate-three-color"]["config"]
                   ["google-pins-qos:pir-pkts"] = absl::StrCat(queue_limit);
          break;
        }
      }
    }
  }
  return json_yang::DumpJson(config);
}

absl::StatusOr<absl::flat_hash_map<std::string, int>>
GetSflowSamplingRateForInterfaces(
    gnmi::gNMI::StubInterface* gnmi_stub,
    const absl::flat_hash_set<std::string>& interfaces) {
  absl::flat_hash_map<std::string, int> interface_to_sample_rate;
  const std::string parse_ops_str =
      "openconfig-sampling-sflow:ingress-sampling-rate";
  for (const auto& interface : interfaces) {
    ASSIGN_OR_RETURN(
        std::string sample_rate_str,
        pins_test::GetGnmiStatePathInfo(
            gnmi_stub,
            absl::Substitute(kSflowGnmiStateInterfaceSampleRatePath, interface),
            parse_ops_str));
    int sample_rate;
    if (!absl::SimpleAtoi(sample_rate_str, &sample_rate)) {
      return absl::InternalError(absl::StrCat(
          interface, " has invalid ingress-sampling-rate ", sample_rate_str));
    }
    interface_to_sample_rate[interface] = sample_rate;
  }
  return interface_to_sample_rate;
}

absl::StatusOr<absl::flat_hash_map<std::string, int>>
GetSflowActualSamplingRateForInterfaces(
    gnmi::gNMI::StubInterface* gnmi_stub,
    const absl::flat_hash_set<std::string>& interfaces) {
  absl::flat_hash_map<std::string, int> interface_to_sample_rate;
  const std::string parse_ops_str =
      "pins-sampling-sflow:actual-ingress-sampling-rate";
  for (const auto& interface : interfaces) {
    ASSIGN_OR_RETURN(
        std::string sample_rate_str,
        pins_test::GetGnmiStatePathInfo(
            gnmi_stub,
            absl::Substitute(kSflowGnmiStateInterfaceActualSampleRatePath,
                             interface),
            parse_ops_str));
    int sample_rate;
    if (!absl::SimpleAtoi(sample_rate_str, &sample_rate)) {
      return absl::InternalError(
          absl::StrCat(interface, " has invalid actual-ingress-sampling-rate ",
                       sample_rate_str));
    }
    interface_to_sample_rate[interface] = sample_rate;
  }
  return interface_to_sample_rate;
}

absl::Status VerifySflowQueueLimitState(gnmi::gNMI::StubInterface* gnmi_stub,
                                        int queue_number,
                                        int expected_queue_limit,
                                        absl::Duration timeout) {
  const std::string kQueueLimitStatePath = absl::Substitute(
      R"(/qos/scheduler-policies/scheduler-policy[name=cpu_scheduler]/schedulers/scheduler[sequence=$0]/two-rate-three-color/state)",
      queue_number);
  auto verify_queue_limit = [&]() -> absl::Status {
    ASSIGN_OR_RETURN(
        std::string state_value,
        pins_test::GetGnmiStatePathInfo(gnmi_stub, kQueueLimitStatePath,
                                        "openconfig-qos:state"));
    ASSIGN_OR_RETURN(const auto resp_json, json_yang::ParseJson(state_value));
    if (resp_json["google-pins-qos:pir-pkts"] ==
        absl::StrCat(expected_queue_limit)) {
      return absl::OkStatus();
    }
    return absl::FailedPreconditionError(absl::StrCat(
        "State path: [", kQueueLimitStatePath, "] actual value is ",
        state_value, ", expected value is ", expected_queue_limit));
  };
  return pins_test::WaitForCondition(verify_queue_limit, timeout);
}

absl::StatusOr<int> ExtractTosFromTcpdumpResult(
    absl::string_view tcpdump_result) {
  std::string tos;
  int tos_int = -1;
  while (RE2::FindAndConsume(&tcpdump_result, *kPacketTosMatchPattern, &tos)) {
    int current_tos_int;
    if (!absl::SimpleHexAtoi(tos, &current_tos_int)) {
      return absl::InvalidArgumentError(
          absl::StrCat("Failed to convert ", tos, " to int value."));
    }
    if (tos_int != -1 && current_tos_int != tos_int) {
      return absl::InvalidArgumentError(
          absl::StrCat("Tos values are not identical. ", tos_int,
                       " not equal to ", current_tos_int));
    }
    tos_int = current_tos_int;
  }
  if (tos_int != -1) {
    return tos_int;
  }
  return absl::InvalidArgumentError(
      "Failed to find ToS value in tcpdump result.");
}

absl::StatusOr<int64_t> GetSflowInterfacePacketsSampledCounter(
    gnmi::gNMI::StubInterface* gnmi_stub, absl::string_view interface_name) {
  const std::string gnmi_state_path = absl::Substitute(
      "/sampling/sflow/interfaces/interface[name=$0]/state/packets-sampled",
      interface_name);
  const std::string parse_ops_str = "openconfig-sampling-sflow:packets-sampled";
  ASSIGN_OR_RETURN(std::string counter_str,
                   pins_test::GetGnmiStatePathInfo(gnmi_stub, gnmi_state_path,
                                                   parse_ops_str));
  LOG(INFO) << "Gnmi path: " << gnmi_state_path << " value is: " << counter_str;
  int64_t counter;
  // skip over the quote '"'
  if (!absl::SimpleAtoi(counter_str.substr(1, counter_str.size() - 2),
                        &counter)) {
    return absl::InternalError(absl::StrCat(
        interface_name, " has invalid packets-sampled value: ", counter_str));
  }
  return counter;
}

absl::StatusOr<int64_t> GetSflowCollectorPacketsSentCounter(
    gnmi::gNMI::StubInterface* gnmi_stub, absl::string_view collector_ip,
    int port_num) {
  const std::string gnmi_state_path = absl::Substitute(
      "/sampling/sflow/collectors/"
      "collector[address=$0][port=$1]/state/packets-sent",
      collector_ip, port_num);
  const std::string parse_ops_str = "openconfig-sampling-sflow:packets-sent";
  ASSIGN_OR_RETURN(std::string counter_str,
                   pins_test::GetGnmiStatePathInfo(gnmi_stub, gnmi_state_path,
                                                   parse_ops_str));
  LOG(INFO) << "Gnmi path: " << gnmi_state_path << " value is: " << counter_str;
  int64_t counter;
  // skip over the quote '"'
  if (!absl::SimpleAtoi(counter_str.substr(1, counter_str.size() - 2),
                        &counter)) {
    return absl::InternalError(absl::StrCat(
        collector_ip, " has invalid packets-sent value: ", counter_str));
  }
  return counter;
}

absl::StatusOr<bool> IsSameIpAddressStr(const std::string& ip1,
                                        const std::string& ip2) {
  // Ipv4 address only has one format.
  if (absl::StatusOr<netaddr::Ipv4Address> ipv4_address_1 =
          netaddr::Ipv4Address::OfString(ip1);
      ipv4_address_1.ok()) {
    return ip1 == ip2;
  }
  ASSIGN_OR_RETURN(netaddr::Ipv6Address ipv6_adddress_1,
                   netaddr::Ipv6Address::OfString(ip1));
  ASSIGN_OR_RETURN(netaddr::Ipv6Address ipv6_adddress_2,
                   netaddr::Ipv6Address::OfString(ip2));

  return ipv6_adddress_1 == ipv6_adddress_2;
}

int GetSflowCollectorPort() { return kSflowStandaloneCollectorPort; }

absl::Status CheckStateDbPortIndexTableExists(
    thinkit::SSHClient& ssh_client, absl::string_view device_name,
    absl::Span<const std::string> interfaces) {
  ASSIGN_OR_RETURN(
      std::string ssh_result,
      ssh_client.RunCommand(
          device_name,
          /*command=*/"/usr/tools/bin/redis-cli -n 6 keys PORT_INDEX_TABLE*",
          /*timeout=*/absl::Seconds(5)));
  LOG(INFO) << "ssh_result: " << ssh_result;
  absl::flat_hash_set<std::string> port_index_table_interfaces;
  for (absl::string_view interface_str :
       absl::StrSplit(ssh_result, "PORT_INDEX_TABLE")) {
    interface_str = absl::StripAsciiWhitespace(interface_str);
    auto pos = interface_str.find("Ethernet");
    if (pos == std::string::npos) {
      continue;
    }
    port_index_table_interfaces.insert(std::string(interface_str.substr(pos)));
  }
  std::vector<std::string> missing_interfaces;
  for (const auto& interface : interfaces) {
    if (!port_index_table_interfaces.contains(interface)) {
      missing_interfaces.push_back(interface);
    }
  }
  if (missing_interfaces.empty()) {
    return absl::OkStatus();
  }
  return absl::FailedPreconditionError(
      absl::StrCat("Failed to find PORT_INDEX_TABLE for interface ",
                   absl::StrJoin(missing_interfaces, ", ")));
}

}  // namespace pins
