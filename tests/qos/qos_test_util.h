#ifndef PINS_TESTS_QOS_QOS_TEST_UTIL_H_
#define PINS_TESTS_QOS_QOS_TEST_UTIL_H_

#include <cstdint>
#include <optional>

#include "absl/container/flat_hash_map.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/gnmi/openconfig.pb.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "proto/gnmi/gnmi.pb.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/proto/generic_testbed.pb.h"

namespace pins_test {

// The maximum time the switch is allowed to take before queue counters read via
// gNMI have to be incremented after a packet hits a queue.
// Empirically, for PINS, queue counters currently seem to get updated every
// 10 seconds.
constexpr absl::Duration kMaxQueueCounterUpdateTime = absl::Seconds(25);

// These are the counters we track in these tests.
struct QueueCounters {
  int64_t num_packets_transmitted = 0;
  int64_t num_packets_dropped = 0;
};

// Operator to pretty print Queue Counters.
inline std::ostream &operator<<(std::ostream &os,
                                const QueueCounters &counters) {
  return os << absl::StreamFormat("QueueCounters{"
                                  ".num_packets_transmitted = %d, "
                                  ".num_packets_dropped = %d"
                                  "}",
                                  counters.num_packets_transmitted,
                                  counters.num_packets_dropped);
}

QueueCounters operator-(const QueueCounters &x, const QueueCounters &y);

// Get queue counters for a port queue.
absl::StatusOr<QueueCounters> GetGnmiQueueCounters(
    absl::string_view port, absl::string_view queue,
    gnmi::gNMI::StubInterface &gnmi_stub);

// Get queue counter with timestamp for a port queue.
absl::StatusOr<ResultWithTimestamp> GetGnmiQueueCounterWithTimestamp(
    absl::string_view port, absl::string_view queue,
    absl::string_view statistic, gnmi::gNMI::StubInterface &gnmi_stub);

// Get total packets (transmitted + dropped) for port queue.
int64_t TotalPacketsForQueue(const QueueCounters &counters);

// Set port speed using gNMI.
absl::Status SetPortSpeedInBitsPerSecond(const std::string &port_speed,
                                         const std::string &iface,
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

// Check if switch port link is up.
absl::StatusOr<bool> CheckLinkUp(const std::string &iface,
                                 gnmi::gNMI::StubInterface &gnmi_stub);

// Structure represents a link between SUT and Ixia.
// This is represented by Ixia interface name and the SUT's gNMI interface
// name.
struct IxiaLink {
  std::string ixia_interface;
  std::string sut_interface;
};

// Go over the connections and return vector of connections
// whose links are up.
absl::StatusOr<std::vector<IxiaLink>> GetReadyIxiaLinks(
    thinkit::GenericTestbed &generic_testbed,
    gnmi::gNMI::StubInterface &gnmi_stub);

// Parse IPv4 DSCP to queue mapping from gnmi configuration.
absl::StatusOr<absl::flat_hash_map<int, std::string>>
ParseIpv4DscpToQueueMapping(absl::string_view gnmi_config);

// Parse IPv6 DSCP to queue mapping from gnmi configuration.
absl::StatusOr<absl::flat_hash_map<int, std::string>>
ParseIpv6DscpToQueueMapping(absl::string_view gnmi_config);

// Get IPv4 DSCP to queue mapping from switch.
absl::StatusOr<absl::flat_hash_map<int, std::string>> GetIpv4DscpToQueueMapping(
    absl::string_view port, gnmi::gNMI::StubInterface &gnmi_stub);

// Get IPv6 DSCP to queue mapping from switch.
absl::StatusOr<absl::flat_hash_map<int, std::string>> GetIpv6DscpToQueueMapping(
    absl::string_view port, gnmi::gNMI::StubInterface &gnmi_stub);

// Get name of queue configured for the given DSCP.
absl::StatusOr<std::string>
GetQueueNameByDscpAndPort(int dscp, absl::string_view port,
                          gnmi::gNMI::StubInterface &gnmi_stub);

// Reads the name of the scheduler policy applied to the given egress port from
// the appropriate gNMI state path.
absl::StatusOr<std::string>
GetSchedulerPolicyNameByEgressPort(absl::string_view egress_port,
                                   gnmi::gNMI::StubInterface &gnmi);

// Reads the config path of the scheduler policy of the given name.
// The config is returned unparsed as a raw JSON string.
absl::StatusOr<std::string>
GetSchedulerPolicyConfig(absl::string_view scheduler_policy_name,
                         gnmi::gNMI::StubInterface &gnmi);

// Updates the config path of the scheduler policy of the given name.
absl::Status
UpdateSchedulerPolicyConfig(absl::string_view scheduler_policy_name,
                            absl::string_view config,
                            gnmi::gNMI::StubInterface &gnmi);

// Two-rate-three-color scheduler parameters. Rates are in bytes/second, sizes
// are in bytes. All parameter are optional, only non-nullopt parameters take
// effect. Documentation:
// - https://datatracker.ietf.org/doc/html/rfc2698
// - http://ops.openconfig.net/branches/models/master/docs/openconfig-qos.html
struct SchedulerParameters {
  std::optional<int64_t> committed_information_rate; // 'cir' in OpenConfig
  std::optional<int64_t> committed_burst_size;       // 'bc' in OpenConfig
  std::optional<int64_t> peak_information_rate;      // 'pir' in OpenConfig
  std::optional<int64_t> excess_burst_size;          // 'be' in OpenConfig
};

// Updates parameters of the scheduler policy of the given name according to
// `params_by_queue_name` and waits for the updated config to converge, or times
// out with an Unavailable error if the state does not converge within the given
// `convergence_timeout`.
absl::Status SetSchedulerPolicyParameters(
    absl::string_view scheduler_policy_name,
    absl::flat_hash_map<std::string, SchedulerParameters> params_by_queue_name,
    gnmi::gNMI::StubInterface &gnmi,
    absl::Duration convergence_timeout = absl::Seconds(10));

}  // namespace pins_test

#endif  // PINS_TESTS_QOS_QOS_TEST_UTIL_H_
