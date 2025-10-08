#ifndef PINS_LIB_IXIA_PROTOCOL_HELPER_H_
#define PINS_LIB_IXIA_PROTOCOL_HELPER_H_

#include <string>
#include <string_view>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/types/span.h"
#include "thinkit/generic_testbed.h"

namespace pins_test::ixia {

// Creates a LAG with the given vports. The returned LAG can be used as a
// source/destination for protocol traffic and topologies.
absl::StatusOr<std::string> CreateLag(absl::Span<const std::string> vports,
                                      thinkit::GenericTestbed& testbed);

// Creates a topology with the given port (can be vport or LAG).
absl::StatusOr<std::string> CreateTopology(std::string_view port,
                                           thinkit::GenericTestbed& testbed);

// Creates a device group with the given topology.
absl::StatusOr<std::string> CreateDeviceGroup(std::string_view topology,
                                              thinkit::GenericTestbed& testbed);

// Adds an Ethernet protocol to the given device group.
absl::StatusOr<std::string> AddEthernetProtocol(
    std::string_view device_group, thinkit::GenericTestbed& testbed);

// Adds an IPv4 protocol to the given ethernet protocol.
absl::StatusOr<std::string> AddIpv4Protocol(std::string_view ethernet_protocol,
                                            thinkit::GenericTestbed& testbed);

// Starts all protocols configured on the Ixia.
absl::Status StartAllProtocols(thinkit::GenericTestbed& testbed);

}  // namespace pins_test::ixia

#endif  // PINS_LIB_IXIA_PROTOCOL_HELPER_H_
