#include "tests/packet_capture/packet_capture_test_util.h"

#include <cstdint>
#include <ostream>
#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "gutil/status.h"
#include "lib/gnmi/gnmi_helper.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "thinkit/mirror_testbed.h"

namespace pins_test {
namespace pctutil {

std::ostream &operator<<(std::ostream &os, const SutToControlLink &link) {
  return os << absl::StreamFormat("SutToControlLink{"
                                  ".sut_ingress_port_gnmi_name = %s,"
                                  ".sut_mtp_port_gnmi_name = %s,"
                                  ".control_switch_inject_port_gnmi_name = %s"
                                  "}",
                                  link.sut_ingress_port_gnmi_name,
                                  link.sut_mtp_port_gnmi_name,
                                  link.control_switch_inject_port_gnmi_name);
}

absl::StatusOr<SutToControlLink>
PickSutToControlDeviceLinkThatsUp(thinkit::MirrorTestbed &testbed) {
  // TODO: Pick dynamically instead of hard-coding.
  return SutToControlLink{.sut_ingress_port_gnmi_name = "Ethernet1/1/1",
                          .control_switch_inject_port_gnmi_name =
                              "Ethernet1/1/1",
                          .sut_mtp_port_gnmi_name = "Ethernet1/2/1"};
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
