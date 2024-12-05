#include "tests/qos/gnmi_parsers.h"

#include <optional>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "google/protobuf/util/json_util.h"
#include "gutil/overload.h"
#include "gutil/status.h"
#include "lib/gnmi/openconfig.pb.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/netaddr/ipv6_address.h"

namespace pins_test {

namespace {

template <class T>
absl::StatusOr<T> ParseProtoFromJsonIgnoringUnknownFields(
    absl::string_view json) {
  google::protobuf::util::JsonParseOptions options;
  options.ignore_unknown_fields = true;
  T proto;
  // OS protobuf uses its own `Status`-like and `string_view`-like classes, so
  // some gymnastics are required here:
  // - ToAbslStatus converts any `Status`-like type to an absl::Status.
  // - We pass in `{json.data(), json.size()}` instead of `json`, constructing
  //   a new object of the appropriate `string_view`-like type implicitly.
  RETURN_IF_ERROR(
      gutil::ToAbslStatus(google::protobuf::util::JsonStringToMessage(
          {json.data(), json.size()}, &proto, options)));
  return proto;
}

}  // namespace

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
  ASSIGN_OR_RETURN(
      auto config,
      ParseProtoFromJsonIgnoringUnknownFields<openconfig::Config>(gnmi_config));
  return ParseLoopbackIps(config);
}

absl::StatusOr<std::vector<netaddr::Ipv6Address>> ParseLoopbackIpv6s(
    absl::string_view gnmi_config) {
  ASSIGN_OR_RETURN(
      auto config,
      ParseProtoFromJsonIgnoringUnknownFields<openconfig::Config>(gnmi_config));
  return ParseLoopbackIpv6s(config);
}

absl::StatusOr<std::vector<netaddr::Ipv4Address>> ParseLoopbackIpv4s(
    absl::string_view gnmi_config) {
  ASSIGN_OR_RETURN(
      auto config,
      ParseProtoFromJsonIgnoringUnknownFields<openconfig::Config>(gnmi_config));
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

}  // namespace pins_test
