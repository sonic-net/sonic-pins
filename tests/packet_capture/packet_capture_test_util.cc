#include "tests/packet_capture/packet_capture_test_util.h"

#include <cstdint>
#include <ostream>
#include <string>

#include "absl/container/flat_hash_map.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "gutil/gutil/status.h"
#include "lib/gnmi/gnmi_helper.h"
#include "platforms/networking/gpins/testing/lib/test_util.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "util/gtl/value_or_die.h"

namespace pins_test {
namespace pctutil {

std::ostream& operator<<(std::ostream& os, const SutToControlLinks& links) {
  return os << absl::StreamFormat(
             "SutToControlLink{"
             ".sut_ingress_port_gnmi_name = %s,"
             ".sut_mtp_port_gnmi_name = %s,"
             ".control_switch_inject_port_p4_id = %s"
             "}",
             links.sut_ingress_port.gnmi_name, links.sut_mtp_port.gnmi_name,
             links.control_switch_inject_port.p4_id);
}

absl::StatusOr<SutToControlLinks> PickSutToControlDeviceLinkThatsUp(
    gnmi::gNMI::StubInterface* gnmi_stub) {
  SutToControlLinks links;
  using UpPortMap = absl::flat_hash_map<std::string, std::string>;
  ASSIGN_OR_RETURN(UpPortMap up_ports, GetAllUpInterfacePortIdsByName(
                                           *gnmi_stub, absl::Seconds(30)));
  if (up_ports.size() < 2) {
    LOG(ERROR) << "Not enough up ports availanle for packet capture test.";
    return absl::InternalError("Not enough up ports for packet capture test");
  }

  auto it = up_ports.begin();
  links.sut_ingress_port.gnmi_name = it->first;
  links.sut_ingress_port.p4_id = it->second;
  ++it;
  links.sut_mtp_port.gnmi_name = it->first;
  links.sut_mtp_port.p4_id = it->second;

  auto interface_to_peer_entity_map = gtl::ValueOrDie(
      gpins::ControlP4rtPortIdBySutP4rtPortIdFromSwitchConfig());

  for (const auto& interface_to_peer_entity : interface_to_peer_entity_map) {
    if (interface_to_peer_entity.second.GetP4rtEncoding() ==
        links.sut_ingress_port.p4_id) {
      links.control_switch_inject_port.p4_id =
          interface_to_peer_entity.first.GetP4rtEncoding();
      break;
    }
  }

  return links;
}

absl::StatusOr<std::string>
GetVendorPortId(absl::string_view gnmi_port_name,
                gnmi::gNMI::StubInterface *gnmi_stub) {
  std::string ops_state_path = absl::StrCat(
      "interfaces/interface[name=", gnmi_port_name, "]/state/vendor-id");

  return GetGnmiStatePathInfo(gnmi_stub, ops_state_path,
                              "google-pins-interfaces:vendor-id");
}

absl::StatusOr<uint64_t> GetGnmiStat(absl::string_view stat_name,
                                     absl::string_view interface,
                                     gnmi::gNMI::StubInterface *gnmi_stub) {
  std::string ops_state_path;
  std::string ops_parse_str;

  ops_state_path = absl::StrCat("interfaces/interface[name=", interface,
                                "]/state/counters/", stat_name);
  ops_parse_str = absl::StrCat("openconfig-interfaces:", stat_name);

  ASSIGN_OR_RETURN(
      std::string ops_response,
      GetGnmiStatePathInfo(gnmi_stub, ops_state_path, ops_parse_str));

  uint64_t stat;
  // Skip over the quotes.
  if (!absl::SimpleAtoi(StripQuotes(ops_response), &stat)) {
    return absl::InternalError(
        absl::StrCat("Unable to parse counter from ", ops_response));
  }
  return stat;
}

absl::Duration ParsePsampHeaderObservationTime(uint64_t observation_time) {
  // Lower 32 bits of the observation time are nanoseconds.
  uint32_t nanoseconds = static_cast<uint32_t>(observation_time);
  // Upper 32 bits of the observation time are seconds.
  uint32_t seconds = static_cast<uint32_t>(observation_time >> 32);

  return absl::Seconds(seconds) + absl::Nanoseconds(nanoseconds);
}
} // namespace pctutil
} // namespace pins_test
