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

#ifndef PINS_LIB_GNMI_GNMI_HELPER_H_
#define PINS_LIB_GNMI_GNMI_HELPER_H_

#include <cstdint>
#include <functional>
#include <ostream>
#include <string>
#include <tuple>
#include <type_traits>
#include <utility>
#include <vector>

#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/functional/any_invocable.h"
#include "absl/numeric/int128.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "github.com/openconfig/gnoi/types/types.pb.h"
#include "lib/gnmi/openconfig.pb.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "proto/gnmi/gnmi.pb.h"
#include "thinkit/switch.h"

namespace pins_test {

inline constexpr char kOpenconfigStr[] = "openconfig";
inline constexpr char kTarget[] = "target";

// Breakout mode is represented as vector of breakout speed.
enum class BreakoutSpeed {
  k100GB,
  k200GB,
  k400GB,
};
std::string BreakoutSpeedToString(BreakoutSpeed speed);
using BreakoutMode = std::vector<BreakoutSpeed>;
std::ostream &operator<<(std::ostream &os, const BreakoutMode &breakout);

enum class GnmiSetType : char { kUpdate, kReplace, kDelete };

enum class OperStatus {
  kUnknown,
  kUp,
  kDown,
  kTesting,
};

enum class AdminStatus {
  kUnknown,
  kUp,
  kDown,
  kTesting,
};

enum class GnmiFieldType {
  kConfig,
  kState,
};

// Describes a single interface in a gNMI config.
struct OpenConfigInterfaceDescription {
  std::string port_name;
  int port_id;
};

// `TransceiverPart` holds the `vendor` and `part_number` of the physical
// transceiver.
struct TransceiverPart {
  std::string vendor;
  std::string part_number;
  std::string manufacturer_name;
  std::string serial_number;
  std::string rev;

  bool operator==(const TransceiverPart &other) const {
    return std::tie(vendor, part_number, manufacturer_name, serial_number,
                    rev) == std::tie(other.vendor, other.part_number,
                                     other.manufacturer_name,
                                     other.serial_number, other.rev);
  }
};

enum class InterfaceType {
  kAny,
  kLag,
  kSingleton,
  kLoopback,
};

// Interface counters exposed by gNMI.
struct Counters {
  uint64_t in_pkts = 0;
  uint64_t out_pkts = 0;
  uint64_t in_octets = 0;
  uint64_t out_octets = 0;
  uint64_t in_unicast_pkts = 0;
  uint64_t out_unicast_pkts = 0;
  uint64_t in_multicast_pkts = 0;
  uint64_t out_multicast_pkts = 0;
  uint64_t in_broadcast_pkts = 0;
  uint64_t out_broadcast_pkts = 0;
  uint64_t in_errors = 0;
  uint64_t out_errors = 0;
  uint64_t in_discards = 0;
  uint64_t out_discards = 0;
  uint64_t in_buffer_discards = 0;
  uint64_t in_maxsize_exceeded = 0;
  uint64_t in_fcs_errors = 0;
  uint64_t in_ipv4_pkts = 0;
  uint64_t out_ipv4_pkts = 0;
  uint64_t in_ipv6_pkts = 0;
  uint64_t out_ipv6_pkts = 0;
  uint64_t in_ipv6_discarded_pkts = 0;
  uint64_t out_ipv6_discarded_pkts = 0;
  std::optional<uint64_t> carrier_transitions;
  uint64_t timestamp_ns = 0;
};

std::string GnmiFieldTypeToString(GnmiFieldType field_type);

// Generates an OpenConfig JSON string using the given list of `interfaces` to
// define interfaces of the given `field_type`.
std::string OpenConfigWithInterfaces(
    GnmiFieldType field_type,
    absl::Span<const OpenConfigInterfaceDescription> interfaces);

// Generates a valid, empty OpenConfig JSON string.
std::string EmptyOpenConfig();

// Builds gNMI Set Request for a given OC path, set type and set value.
// The path should be in the following format below.
// "interfaces/interface[Ethernet0]/config/mtu".
// The set value should be in the format ex: {\"mtu\":2000}.
absl::StatusOr<gnmi::SetRequest>
BuildGnmiSetRequest(absl::string_view oc_path, GnmiSetType set_type,
                    absl::string_view json_val = {});

// Builds gNMI Get Request for a given OC path.
// The path should be in the following format below.
// "interfaces/interface[Ethernet0]/config/mtu".
absl::StatusOr<gnmi::GetRequest>
BuildGnmiGetRequest(absl::string_view oc_path,
                    gnmi::GetRequest::DataType req_type);

// Parses `response` to retrieve specific tag value, if `match_tag` is given, or
// the full response otherwise.
// Uses non-negative `indent` values to pretty-print the GetResponse with
// `indent` spaces of indentation. `-1` renders a single line of illegible, but
// correct, JSON.
// WARNING: Returns InternalError if each notification in the GetResponse does
// not have exactly 1 update.
absl::StatusOr<std::string>
ParseGnmiGetResponse(const gnmi::GetResponse &response,
                     absl::string_view match_tag = {}, int indent = -1);

absl::Status SetGnmiConfigPath(gnmi::gNMI::StubInterface *gnmi_stub,
                               absl::string_view config_path,
                               GnmiSetType operation, absl::string_view value);

// Send and update operation for a gNMI config leaf.
// The config path should not contain the /openconfig/ prefix.
// Example:
//   UpdateGnmiConfigLeaf(gnmi_stub, "system/config/boot-time", "12345678")
absl::Status UpdateGnmiConfigLeaf(gnmi::gNMI::StubInterface *gnmi_stub,
                                  absl::string_view config_path,
                                  absl::string_view value);

// Send and update operation for a gNMI config leaf and wait for the state value
// to update.
absl::Status UpdateAndVerifyGnmiConfigLeaf(
    gnmi::gNMI::StubInterface *gnmi_stub, absl::string_view config_path,
    absl::string_view value, absl::Duration timeout = absl::Minutes(2));

absl::StatusOr<std::string>
GetGnmiStatePathInfo(gnmi::gNMI::StubInterface *gnmi_stub,
                     absl::string_view state_path,
                     absl::string_view resp_parse_str = {});

// Return the string value of a gNMI state leaf.
absl::StatusOr<std::string>
GetGnmiStateLeafValue(gnmi::gNMI::StubInterface *gnmi_stub,
                      absl::string_view state_path);

struct ResultWithTimestamp {
  std::string response;
  int64_t timestamp;
};

absl::StatusOr<ResultWithTimestamp>
GetGnmiStatePathAndTimestamp(gnmi::gNMI::StubInterface *gnmi_stub,
                             absl::string_view path,
                             absl::string_view resp_parse_str);

absl::StatusOr<std::string> ReadGnmiPath(gnmi::gNMI::StubInterface *gnmi_stub,
                                         absl::string_view path,
                                         gnmi::GetRequest::DataType req_type,
                                         absl::string_view resp_parse_str = {});

template <class T>
std::string ConstructGnmiConfigSetString(std::string field, T value) {
  std::string result_str;
  if (std::is_integral<T>::value) {
    // result: "{\"field\":value}"
    result_str = absl::StrCat("{\"", field, "\":", value, "}");
  } else if (std::is_same<T, std::string>::value) {
    // result: "{\"field\":\"value\"};
    result_str = absl::StrCat("{\"", field, "\":\"", value, "\"}");
  }

  return result_str;
}

// Adding subtree to gNMI Subscription list.
void AddSubtreeToGnmiSubscription(absl::string_view subtree_root,
                                  gnmi::SubscriptionList &subscription_list,
                                  gnmi::SubscriptionMode mode,
                                  bool suppress_redundant,
                                  absl::Duration interval);

// Returns vector of elements in subscriber response.
absl::StatusOr<std::vector<absl::string_view>>
GnmiGetElementFromTelemetryResponse(const gnmi::SubscribeResponse &response);

// Pushes a given gNMI config to a given chassis. This method will automatically
// configure the arbitration settings for the request.
absl::Status
PushGnmiConfig(gnmi::gNMI::StubInterface &stub, const std::string &chassis_name,
               absl::string_view gnmi_config,
               absl::uint128 election_id = pdpi::TimeBasedElectionId());

// Pushes a given gNMI config to a thinkit switch. This method will make
// sensible changes to the config like:
//    * Update the P4RT device ID to match the chassis settings.
absl::Status PushGnmiConfig(thinkit::Switch &chassis,
                            absl::string_view gnmi_config);

absl::Status WaitForGnmiPortIdConvergence(gnmi::gNMI::StubInterface &stub,
                                          absl::string_view gnmi_config,
                                          const absl::Duration &timeout);
absl::Status WaitForGnmiPortIdConvergence(thinkit::Switch &chassis,
                                          absl::string_view gnmi_config,
                                          const absl::Duration &timeout);

// Waits until the interface <-> P4RT port id mappings in the config path of the
// switch are reflected in the state path.
absl::Status WaitForGnmiPortIdConvergence(gnmi::gNMI::StubInterface &stub,
                                          const absl::Duration &timeout);

absl::Status
CanGetAllInterfaceOverGnmi(gnmi::gNMI::StubInterface &stub,
                           absl::Duration timeout = absl::Seconds(60));

absl::StatusOr<gnmi::GetResponse>
GetAllInterfaceOverGnmi(gnmi::gNMI::StubInterface &stub,
                        absl::Duration timeout = absl::Seconds(60));

// Gets the interface to oper status map.
absl::StatusOr<absl::flat_hash_map<std::string, std::string>>
GetInterfaceToOperStatusMapOverGnmi(gnmi::gNMI::StubInterface &stub,
                                    absl::Duration timeout);

// Checks if given interfaces' oper-status is up/down. Passing in nothing for
// `interfaces` will check for all interfaces.
absl::Status
CheckInterfaceOperStateOverGnmi(gnmi::gNMI::StubInterface &stub,
                                absl::string_view interface_oper_state,
                                absl::Span<const std::string> interfaces = {},
                                bool skip_non_ethernet_interfaces = false,
                                absl::Duration timeout = absl::Seconds(60));

// Returns gNMI Path for OC strings.
gnmi::Path ConvertOCStringToPath(absl::string_view oc_path);

// Converts from a gNMI path to a gNOI path.
gnoi::types::Path GnmiToGnoiPath(gnmi::Path path);

// Gets all the EthernetXX interfaces whose operational status is UP.
absl::StatusOr<std::vector<std::string>>
GetUpInterfacesOverGnmi(gnmi::gNMI::StubInterface &stub,
                        InterfaceType type = InterfaceType::kAny,
                        absl::Duration timeout = absl::Seconds(60));

// Gets all the EthernetXX interfaces whose operational status is UP.
inline absl::StatusOr<std::vector<std::string>>
GetUpInterfacesOverGnmi(gnmi::gNMI::StubInterface &stub,
                        absl::Duration timeout) {
  return GetUpInterfacesOverGnmi(stub, InterfaceType::kAny, timeout);
}

// Returns a set of interfaces which are in the disabled state.
absl::StatusOr<absl::flat_hash_set<std::string>>
GetConfigDisabledInterfaces(gnmi::gNMI::StubInterface &stub);

// Gets the operational status of an interface.
absl::StatusOr<OperStatus>
GetInterfaceOperStatusOverGnmi(gnmi::gNMI::StubInterface &stub,
                               absl::string_view if_name);

// Gets the administrative status of an interface.
absl::StatusOr<AdminStatus>
GetInterfaceAdminStatusOverGnmi(gnmi::gNMI::StubInterface &stub,
                                absl::string_view if_name);

// GetAllInterfaceNameToPortId are helper methods that fetch the P4Runtime port
// name to ID mapping of a switch. The `field_type` argument can be used to
// fetch this mapping based on either the switch configuration or its state.
//
// A filter can be used to erase unintersing port name to ID mappings for a
// given test. By default we restrict only the CPU port which behaves
// differently than the front-panel ports most tests are interested in.
using PortIdByNameIterType = std::pair<std::string, std::string>;

inline bool GetAllPorts(const PortIdByNameIterType &) {
  return false; // do not filiter anything.
}
inline bool IgnoreCpuPortName(const PortIdByNameIterType &iter) {
  return iter.first == "CPU";
}

absl::StatusOr<absl::flat_hash_map<std::string, std::string>>
GetAllInterfaceNameToPortId(
    absl::string_view gnmi_config, absl::string_view field_type = "config",
    absl::AnyInvocable<bool(const PortIdByNameIterType &)> filter =
        IgnoreCpuPortName);
absl::StatusOr<absl::flat_hash_map<std::string, std::string>>
GetAllInterfaceNameToPortId(
    gnmi::gNMI::StubInterface &stub, absl::string_view field_type = "state",
    absl::AnyInvocable<bool(const PortIdByNameIterType &)> filter =
        IgnoreCpuPortName);

// Gets interfaces from the switch and returns them as a proto.
absl::StatusOr<openconfig::Interfaces>
GetInterfacesAsProto(gnmi::gNMI::StubInterface &stub,
                     gnmi::GetRequest::DataType type,
                     absl::Duration timeout = absl::Seconds(60));

// Gets gNMIConfig for the entire switch.
absl::StatusOr<std::string> GetGnmiConfig(gnmi::gNMI::StubInterface &gnmi_stub);

// Gets interfaces satisfying `predicate` from the switch and returns them as a
// proto.
absl::StatusOr<openconfig::Interfaces> GetMatchingInterfacesAsProto(
    gnmi::gNMI::StubInterface &stub, gnmi::GetRequest::DataType type,
    std::function<bool(const openconfig::Interfaces::Interface &)> predicate,
    absl::Duration timeout = absl::Seconds(60));

// Returns a sorted vector of P4RT port IDs mapped to matching interfaces in the
// switch's gNMI state.
absl::StatusOr<std::vector<P4rtPortId>> GetMatchingP4rtPortIds(
    gnmi::gNMI::StubInterface &stub,
    std::function<bool(const openconfig::Interfaces::Interface &)> predicate);

// Returns true if the interface is an enabled, Ethernet interface. For use with
// the GetMatching* functions above.
bool IsEnabledEthernetInterface(
    const openconfig::Interfaces::Interface &interface);

// Reads the gNMI config from the switch and returns a map of all enabled
// interfaces to their p4rt port id.
absl::StatusOr<absl::flat_hash_map<std::string, std::string>>
GetAllEnabledInterfaceNameToPortId(gnmi::gNMI::StubInterface &stub,
                                   absl::Duration timeout = absl::Seconds(60));

// Checks the switch's gNMI state for any ports that are UP, and returns a map
// of the port IDs by the port names. If a port is not UP or does not have an ID
// it will not be returned.
absl::StatusOr<absl::flat_hash_map<std::string, std::string>>
GetAllUpInterfacePortIdsByName(gnmi::gNMI::StubInterface &stub,
                               absl::Duration timeout = absl::Seconds(60));

// Checks the switch's gNMI state for any port that is UP with a Port ID. If no
// port is UP with a Port ID then an error is returned.
absl::StatusOr<std::string>
GetAnyUpInterfacePortId(gnmi::gNMI::StubInterface &stub,
                        absl::Duration timeout = absl::Seconds(60));

// Checks the switch's gNMI state for N ports that are both UP and have a Port
// ID. If the switch does not have enough ports meeting this condition then an
// error is returned.
absl::StatusOr<std::vector<std::string>>
GetNUpInterfacePortIds(gnmi::gNMI::StubInterface &stub, int num_interfaces,
                       absl::Duration timeout = absl::Seconds(60));

// Deterministically modifies the config of `gnmi_stub` to map all
// `desired_p4rt_ids` to interfaces on the switch that match the given
// `predicate`. If too few interfaces match the `predicate` to map all
// `desired_p4rt_ids`, the function will fail. Any matching interface already
// mapping a desired P4RT ID will be left unchanged. Any non-matching
// interface that maps a desired P4RT ID will have the mapping removed.
absl::Status MapP4rtIdsToMatchingInterfaces(
    gnmi::gNMI::StubInterface &gnmi_stub,
    const absl::btree_set<int> &desired_p4rt_ids,
    std::function<bool(const openconfig::Interfaces::Interface &)> predicate,
    absl::Duration timeout = absl::Seconds(60));

// Uses `gnmi_stub` to set the P4RT IDs of `interfaces`, deleting any of those
// P4RT IDs previously mapped on the switch since a P4RT ID can't be mapped to
// multiple interfaces. Any existing interface that already maps its desired
// P4RT ID is untouched. Each interface (as identified by name) in `interfaces`
// must already be present on the switch.
absl::Status SetInterfaceP4rtIds(gnmi::gNMI::StubInterface &gnmi_stub,
                                 const openconfig::Interfaces &interfaces);

// Returns the ordered set of all port ids mapped by the given gNMI config.
absl::StatusOr<absl::btree_set<std::string>>
GetAllPortIds(absl::string_view gnmi_config);

// Reads the gNMI state and returns the ordered set of all port ids mapped.
absl::StatusOr<absl::btree_set<std::string>>
GetAllPortIds(gnmi::gNMI::StubInterface &stub);

// Gets all system process id over gNMI.
absl::StatusOr<gnmi::GetResponse>
GetAllSystemProcesses(gnmi::gNMI::StubInterface &gnmi_stub);

// Gets system memory usage over gNMI.
absl::StatusOr<gnmi::GetResponse>
GetSystemMemory(gnmi::gNMI::StubInterface &gnmi_stub);

// Parses the alarms JSON array returned from a gNMI Get request to
// "openconfig-system:system/alarms/alarm". Returns the list of alarms.
absl::StatusOr<std::vector<std::string>>
ParseAlarms(const std::string &alarms_json);

// Gets alarms over gNMI.
absl::StatusOr<std::vector<std::string>>
GetAlarms(gnmi::gNMI::StubInterface &gnmi_stub);

// Strips the beginning and ending double-quotes from the `string`.
absl::string_view StripQuotes(absl::string_view string);

// Strips the beginning and ending brackets ('[', ']') from the `string`.
absl::string_view StripBrackets(absl::string_view string);

// Returns a map from interface names to their physical transceiver name.
absl::StatusOr<absl::flat_hash_map<std::string, std::string>>
GetInterfaceToTransceiverMap(gnmi::gNMI::StubInterface &gnmi_stub);

// Returns a map from physical transceiver names to their part information.
absl::StatusOr<absl::flat_hash_map<std::string, TransceiverPart>>
GetTransceiverPartInformation(gnmi::gNMI::StubInterface &gnmi_stub);

// Returns a map from physical transceiver names to their form factor.
absl::StatusOr<absl::flat_hash_map<std::string, std::string>>
GetTransceiverToFormFactorMap(gnmi::gNMI::StubInterface &gnmi_stub);

// Sets the device ID which is needed by P4RT App to establish a connection to
// the switch.
absl::Status SetDeviceId(gnmi::gNMI::StubInterface &gnmi_stub,
                         uint32_t device_id);

// Gets the device ID from Switch state Database.
absl::StatusOr<uint64_t> GetDeviceId(gnmi::gNMI::StubInterface &gnmi_stub);

// Takes a gNMI config in JSON format and updates the P4RT Device ID. Adding it
// when it doesn't exist, or updating the value if it does.
std::string UpdateDeviceIdInJsonConfig(absl::string_view gnmi_config,
                                       const std::string &device_id);

// Return the port id whose breakout mode matches the given input.
// Input: the configuration's open config as string format.
// Ignore ports is optional that is set as empty as default.
absl::StatusOr<int>
FindPortWithBreakoutMode(absl::string_view json_config,
                         const BreakoutMode &breakout,
                         const absl::flat_hash_set<int> &ignore_ports = {});

// Return the interfaces under the input port.
absl::StatusOr<std::vector<std::string>>
GetInterfacesOnPort(absl::string_view json_config, int port_number);

// Returns a map from physical transceiver names to ethernet PMD type.
absl::StatusOr<absl::flat_hash_map<std::string, std::string>>
GetTransceiverToEthernetPmdMap(gnmi::gNMI::StubInterface &gnmi_stub);

// Returns a map from interfaces names to the speed of each lane in the port,
// as an integer in Kbps.
// Example: for a 4-lane 200G interface, this mapping would give a lane speed of
// 50'000'000 (50G).
absl::StatusOr<absl::flat_hash_map<std::string, int>>
GetInterfaceToLaneSpeedMap(gnmi::gNMI::StubInterface &gnmi_stub,
                           absl::flat_hash_set<std::string> &interface_names);

// Return true only if interface supports BERT.
bool InterfaceSupportsBert(
    absl::string_view interface,
    const absl::flat_hash_map<std::string, int> &interface_to_lane_speed);

// Check if switch port link is up.
absl::StatusOr<bool> CheckLinkUp(const std::string &interface_name,
                                 gnmi::gNMI::StubInterface &gnmi_stub);
// Set port speed using gNMI.
absl::Status SetPortSpeedInBitsPerSecond(const std::string &port_speed,
                                         const std::string &interface_name,
                                         gnmi::gNMI::StubInterface &gnmi_stub);

enum class PortSpeed : int64_t {
  kSpeed100G = 100000000000,
  kSpeed200G = 200000000000,
  kSpeed400G = 400000000000
};

// Set port speed using gNMI.
// Currently following speed sets are supported:
// 100 Gbps, 200 Gbps, 400 Gbps.
// Function will return InvalidArgumentError for other speeds.
absl::Status SetPortSpeedInBitsPerSecond(PortSpeed port_speed,
                                         const std::string &interface_name,
                                         gnmi::gNMI::StubInterface &gnmi_stub);

// Get configured port speed.
absl::StatusOr<int64_t>
GetPortSpeedInBitsPerSecond(const std::string &interface_name,
                            gnmi::gNMI::StubInterface &gnmi_stub);

// Set port MTU using gNMI.
absl::Status SetPortMtu(int port_mtu, const std::string &interface_name,
                        gnmi::gNMI::StubInterface &gnmi_stub);

// Set a port in loopback mode.
absl::Status SetPortLoopbackMode(bool port_loopback,
                                 absl::string_view interface_name,
                                 gnmi::gNMI::StubInterface &gnmi_stub);

// Gets counters for all interfaces.
absl::StatusOr<absl::flat_hash_map<std::string, Counters>>
GetAllInterfaceCounters(gnmi::gNMI::StubInterface &gnmi_stub);

// Removes specified characters from Json object string.
void StripSymbolFromString(std::string &str, char symbol);

// Returns the 'value' section of a packed json with format:
//   {"field":"value"}
absl::StatusOr<std::string> ParseJsonValue(absl::string_view json);

} // namespace pins_test
#endif // PINS_LIB_GNMI_GNMI_HELPER_H_
