#ifndef PINS_DVAAS_LABELER_H_
#define PINS_DVAAS_LABELER_H_

#include "absl/status/statusor.h"
#include "dvaas/test_vector.pb.h"

namespace dvaas {

// Returns the 'vlan_tagged_input' label if the input packet is VLAN tagged.
absl::StatusOr<Labels> VlanTaggedInputLabeler(const PacketTestRun& test_run);

// Returns the 'unicast_dst_mac_multicast_dst_ip_input' label if the input
// packet has a unicast destination MAC address and a IPv4/IPv6 multicast
// destination IP address.
absl::StatusOr<Labels> UnicastDstMacMulticastDstIpInputLabeler(
    const PacketTestRun& test_run);

}  // namespace dvaas

#endif  // PINS_DVAAS_LABELER_H_
