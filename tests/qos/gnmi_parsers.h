// Defines functions for parsing and extracting values from gNMI configurations
// in JSON format.

#ifndef GOOGLE_TESTS_QOS_GNMI_PARSERS_H_
#define GOOGLE_TESTS_QOS_GNMI_PARSERS_H_

#include <string>
#include <variant>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "lib/gnmi/openconfig.pb.h"
#include "p4_infra/p4_pdpi/netaddr/ipv4_address.h"
#include "p4_infra/p4_pdpi/netaddr/ipv6_address.h"

namespace pins_test {

absl::StatusOr<
    std::vector<std::variant<netaddr::Ipv4Address, netaddr::Ipv6Address>>>
ParseLoopbackIps(absl::string_view gnmi_config);

absl::StatusOr<
    std::vector<std::variant<netaddr::Ipv4Address, netaddr::Ipv6Address>>>
ParseLoopbackIps(const openconfig::Config &gnmi_config);

absl::StatusOr<std::vector<netaddr::Ipv4Address>>
ParseLoopbackIpv4s(absl::string_view gnmi_config);
absl::StatusOr<std::vector<netaddr::Ipv4Address>>
ParseLoopbackIpv4s(const openconfig::Config &gnmi_config);

absl::StatusOr<std::vector<netaddr::Ipv6Address>>
ParseLoopbackIpv6s(absl::string_view gnmi_config);
absl::StatusOr<std::vector<netaddr::Ipv6Address>>
ParseLoopbackIpv6s(const openconfig::Config &gnmi_config);

absl::StatusOr<absl::flat_hash_map<std::string, bool>>
ParseIsIngressTimestampEnabledByInterfaceName(absl::string_view gnmi_config);
absl::flat_hash_map<std::string, bool>
ParseIsIngressTimestampEnabledByInterfaceName(
    const openconfig::Interfaces& interfaces);

}  // namespace pins_test

#endif // GOOGLE_TESTS_QOS_GNMI_PARSERS_H_
