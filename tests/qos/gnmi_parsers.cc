#include "tests/qos/gnmi_parsers.h"

#include <string>
#include <utility>
#include <variant>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "lib/gnmi/openconfig.pb.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/netaddr/ipv6_address.h"

namespace pins_test {

absl::StatusOr<
    std::vector<std::variant<netaddr::Ipv4Address, netaddr::Ipv6Address>>>
ParseLoopbackIps(const openconfig::Config& config) {
  std::vector<std::variant<netaddr::Ipv4Address, netaddr::Ipv6Address>> ips;
  for (auto& interface : config.interfaces().interfaces()) {
    if (interface.config().type() != "iana-if-type:softwareLoopback") continue;
    for (auto& subinterface : interface.subinterfaces().subinterfaces()) {
      for (auto& address : subinterface.ipv4().addresses().addresses()) {
        ASSIGN_OR_RETURN(ips.emplace_back(),
                         netaddr::Ipv4Address::OfString(address.ip()));
      }
      for (auto& address : subinterface.ipv6().addresses().addresses()) {
        ASSIGN_OR_RETURN(ips.emplace_back(),
                         netaddr::Ipv6Address::OfString(address.ip()));
      }
    }
  }
  return ips;
}

absl::StatusOr<
    std::vector<std::variant<netaddr::Ipv4Address, netaddr::Ipv6Address>>>
ParseLoopbackIps(absl::string_view gnmi_config) {
  ASSIGN_OR_RETURN(auto config,
                   gutil::ParseJsonAsProto<openconfig::Config>(
                       gnmi_config, /*ignore_unknown_fields=*/true));
  return ParseLoopbackIps(config);
}

absl::StatusOr<std::vector<netaddr::Ipv6Address>> ParseLoopbackIpv6s(
    absl::string_view gnmi_config) {
  ASSIGN_OR_RETURN(auto config,
                   gutil::ParseJsonAsProto<openconfig::Config>(
                       gnmi_config, /*ignore_unknown_fields=*/true));
  return ParseLoopbackIpv6s(config);
}

absl::StatusOr<std::vector<netaddr::Ipv4Address>> ParseLoopbackIpv4s(
    absl::string_view gnmi_config) {
  ASSIGN_OR_RETURN(auto config,
                   gutil::ParseJsonAsProto<openconfig::Config>(
                       gnmi_config, /*ignore_unknown_fields=*/true));
  return ParseLoopbackIpv4s(config);
}

absl::StatusOr<std::vector<netaddr::Ipv4Address>> ParseLoopbackIpv4s(
    const openconfig::Config& gnmi_config) {
  std::vector<netaddr::Ipv4Address> ipv4s;
  ASSIGN_OR_RETURN(auto ips, ParseLoopbackIps(gnmi_config));
  for (auto& ip : ips) {
    if (auto* ipv4 = std::get_if<netaddr::Ipv4Address>(&ip); ipv4 != nullptr) {
      ipv4s.push_back(std::move(*ipv4));
    }
  }
  return ipv4s;
}

absl::StatusOr<std::vector<netaddr::Ipv6Address>> ParseLoopbackIpv6s(
    const openconfig::Config& gnmi_config) {
  std::vector<netaddr::Ipv6Address> ipv6s;
  ASSIGN_OR_RETURN(auto ips, ParseLoopbackIps(gnmi_config));
  for (auto& ip : ips) {
    if (auto* ipv6 = std::get_if<netaddr::Ipv6Address>(&ip); ipv6 != nullptr) {
      ipv6s.push_back(std::move(*ipv6));
    }
  }
  return ipv6s;
}

absl::StatusOr<absl::flat_hash_map<std::string, bool>>
ParseIsIngressTimestampEnabledByInterfaceName(absl::string_view gnmi_config) {
  ASSIGN_OR_RETURN(auto config,
                   gutil::ParseJsonAsProto<openconfig::Config>(
                       gnmi_config, /*ignore_unknown_fields=*/true));
  return ParseIsIngressTimestampEnabledByInterfaceName(config.interfaces());
}

absl::flat_hash_map<std::string, bool>
ParseIsIngressTimestampEnabledByInterfaceName(
    const openconfig::Interfaces& interfaces) {
  absl::flat_hash_map<std::string, bool> is_timestamp_enabled_by_interface_name;
  for (auto& interface : interfaces.interfaces()) {
    is_timestamp_enabled_by_interface_name[interface.name()] =
        interface.ethernet().config().insert_ingress_timestamp();
  }
  return is_timestamp_enabled_by_interface_name;
}

}  // namespace pins_test
