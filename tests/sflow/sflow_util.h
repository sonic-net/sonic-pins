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

#ifndef PINS_TESTS_SFLOW_SFLOW_UTIL_H_
#define PINS_TESTS_SFLOW_SFLOW_UTIL_H_

#include <cstdint>
#include <string>
#include <utility>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/types/span.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "thinkit/ssh_client.h"

namespace pins {
// Sflow collector port used in standalone test.
constexpr int kSflowStandaloneCollectorPort = 6344;

// Returns true iff
// ["openconfig-sampling:sampling"]["openconfig-sampling-sflow:sflow"]["config"]["enabled"]
// exists and equals true. Returns a InvalidArgumentError if failed to parse
// config.
absl::StatusOr<bool> IsSflowConfigEnabled(absl::string_view gnmi_config);

// Reads value from `state_path` and verifies it is the same with
// `expected_value`. Returns a FailedPreconditionError if not matched.
absl::Status VerifyGnmiStateConverged(gnmi::gNMI::StubInterface* gnmi_stub,
                                      absl::string_view state_path,
                                      absl::string_view expected_value,
                                      absl::string_view resp_parse_str = "");

// Sets sFLow sampling size to `sampling_size` and checks if it's applied to
// corresponding state path in `timeout`. Returns error if failed.
absl::Status SetSflowSamplingSize(gnmi::gNMI::StubInterface* gnmi_stub,
                                  int sampling_size,
                                  absl::Duration timeout = absl::Seconds(5));

// Sets sFlow config to `enabled` and checks if it's applied to state path in
// `timeout`. Returns error if failed.
absl::Status SetSflowConfigEnabled(gnmi::gNMI::StubInterface* gnmi_stub,
                                   bool enabled,
                                   absl::Duration timeout = absl::Seconds(5));

// Sets gNPSI config to `enabled` and checks if it's applied to state path in
// `timeout`. Returns error if failed.
absl::Status SetGnpsiConfigEnabled(gnmi::gNMI::StubInterface* gnmi_stub,
                                   bool enabled,
                                   absl::Duration timeout = absl::Seconds(5));

// Sets sFlow ingress sampling rate of `interface` to `sampling_rate` and checks
// if it's applied to corresponding state path in `timeout`. Returns error if
// failed.
absl::Status SetSflowIngressSamplingRate(
    gnmi::gNMI::StubInterface* gnmi_stub, absl::string_view interface,
    int sampling_rate, absl::Duration timeout = absl::Seconds(5));

// Sets sFlow interface enable and sample config and waits until it's converged
// in state path. `interface` must be present.
absl::Status SetSflowInterfaceConfig(
    gnmi::gNMI::StubInterface* gnmi_stub, absl::string_view interface,
    bool enabled, int samping_rate, absl::Duration timeout = absl::Seconds(30));

// Sets sFlow interface config and waits until it's converged in state path.
// `interface` must be present.
absl::Status SetSflowInterfaceConfigEnable(
    gnmi::gNMI::StubInterface* gnmi_stub, absl::string_view interface,
    bool enabled, absl::Duration timeout = absl::Seconds(5));

// Verifies all sFlow-related config is consumed by switch by reading
// corresponding gNMI state paths. Returns an FailedPreconditionError if
// `agent_addr_ipv6` is empty.
absl::Status VerifySflowStatesConverged(
    gnmi::gNMI::StubInterface* gnmi_stub, absl::string_view agent_addr_ipv6,
    const int sampling_rate, const int sampling_header_size,
    const std::vector<std::pair<std::string, int>>& collector_address_and_port,
    const absl::flat_hash_map<std::string, bool>& sflow_interfaces);

// Verifies gNPSI-related config is consumed by switch by reading corresponding
// gNMI state paths.
absl::Status VerifyGnpsiStateConverged(gnmi::gNMI::StubInterface* gnmi_stub,
                                       bool enable);

// Updates `gnmi_config` with sFlow-related config and returns modified config
// if success. It would remove existing sFlow collector config and then append
// `collector_address_and_port` to config. The modified interface config would
// be sorted by interface name order. Returns an InvalidArgumentError
// if `agent_addr_ipv6` is empty or `collector_address_and_port` size exceeds
// max allowed value.
absl::StatusOr<std::string> UpdateSflowConfig(

    absl::string_view gnmi_config, absl::string_view agent_addr_ipv6,
    const std::vector<std::pair<std::string, int>>& collector_address_and_port,
    const absl::flat_hash_map<std::string, bool>& sflow_interfaces,
    const int sampling_rate, const int sampling_header_size);

// Updates `gnmi_config` with gNPSI-related config and returns modified config
// if success.
absl::StatusOr<std::string> UpdateGnpsiConfig(absl::string_view gnmi_config,
                                              bool enable);

// Updates `gnmi_config` queue limit of `queue_name` to `queue_limit` and
// returns the updated config. Returns InvalidArgumentError if `gnmi_config`
// doesn't have any valid cpu scheduler policy config.
absl::StatusOr<std::string> UpdateQueueLimit(absl::string_view gnmi_config,
                                             absl::string_view queue_name,
                                             int queue_limit);
// Returns <interface name, state/ingress-sampling-rate> map of each
// interface in `interfaces`.
absl::StatusOr<absl::flat_hash_map<std::string, int>>
GetSflowSamplingRateForInterfaces(
    gnmi::gNMI::StubInterface* gnmi_stub,
    const absl::flat_hash_set<std::string>& interfaces);

// Returns <interface name, state/actual-ingress-sampling-rate> map of each
// interface in `interfaces`.
absl::StatusOr<absl::flat_hash_map<std::string, int>>
GetSflowActualSamplingRateForInterfaces(
    gnmi::gNMI::StubInterface* gnmi_stub,
    const absl::flat_hash_set<std::string>& interfaces);

// Verifies that cpu_scheduler limit for `queue_sequence` is set to
// `expected_queue_limit`.
absl::Status VerifySflowQueueLimitState(
    gnmi::gNMI::StubInterface* gnmi_stub, int queue_number,
    int expected_queue_limit, absl::Duration timeout = absl::Seconds(5));

// Extracts ToS value from `tcpdump_result`. Returns InvalidArgument error if
// ToS value are not identical or failed to find ToS value in `tcpdump_result`.
absl::StatusOr<int> ExtractTosFromTcpdumpResult(
    absl::string_view tcpdump_result);

// Reads and returns value from
// `/sampling/sflow/interfaces/interface[name=<interface_name>]/state/packets-sampled`.
absl::StatusOr<int64_t> GetSflowInterfacePacketsSampledCounter(
    gnmi::gNMI::StubInterface* gnmi_stub, absl::string_view interface_name);

// Read and returns value from
// /sampling/sflow/collectors/collector[address=<collector_ip>][port=<port_num>]/state/packets-sent
absl::StatusOr<int64_t> GetSflowCollectorPacketsSentCounter(
    gnmi::gNMI::StubInterface* gnmi_stub, absl::string_view collector_ip,
    int port_num);

// Returns true if `ip1` and `ip2` are same IP addresses. Returns error if fails
// to parse the string.
absl::StatusOr<bool> IsSameIpAddressStr(const std::string& ip1,
                                        const std::string& ip2);

// Returns kSflowStandaloneCollectorPort.
int GetSflowCollectorPort();

// Checks if state db port index table exists for `interfaces`.
absl::Status CheckStateDbPortIndexTableExists(
    thinkit::SSHClient& ssh_client, absl::string_view device_name,
    const std::string redis_cli_path, absl::Span<const std::string> interfaces);

}  // namespace pins
#endif  // PINS_TESTS_SFLOW_SFLOW_UTIL_H_
