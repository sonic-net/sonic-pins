// Defines functions for parsing and extracting values from gNMI configurations
// in JSON format.

#ifndef GOOGLE_TESTS_QOS_GNMI_PARSERS_H_
#define GOOGLE_TESTS_QOS_GNMI_PARSERS_H_

#include <optional>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "lib/gnmi/openconfig.pb.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/netaddr/ipv6_address.h"

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

} // namespace pins_test

#endif // GOOGLE_TESTS_QOS_GNMI_PARSERS_H_
