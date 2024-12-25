#ifndef PINS_TESTS_QOS_QOS_TEST_UTIL_H_
#define PINS_TESTS_QOS_QOS_TEST_UTIL_H_

#include "absl/status/statusor.h"
#include "absl/strings/str_format.h"
#include "lib/gnmi/gnmi_helper.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "proto/gnmi/gnmi.pb.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/proto/generic_testbed.pb.h"

namespace pins_test {
// These are the counters we track in these tests.
struct QueueCounters {
  int64_t num_packets_transmitted = 0;
  int64_t num_packet_dropped = 0;
};

// Operator to pretty print Queue Counters.
inline std::ostream &operator<<(std::ostream &os,
                                const QueueCounters &counters) {
  return os << absl::StreamFormat(
             "QueueCounters{"
             ".num_packets_transmitted = %d, "
             ".num_packets_dropped = %d"
             "}",
             counters.num_packets_transmitted, counters.num_packet_dropped);
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
int64_t CumulativeNumPacketsEnqueued(const QueueCounters &counters);

// Set port speed using gNMI.
absl::Status SetPortSpeed(const std::string &port_speed,
                          const std::string &iface,
                          gnmi::gNMI::StubInterface &gnmi_stub);

// Set port MTU using gNMI.
absl::Status SetPortMtu(int port_mtu, const std::string &interface_name,
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

}  // namespace pins_test

#endif  // PINS_TESTS_QOS_QOS_TEST_UTIL_H_
