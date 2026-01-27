#ifndef PINS_LIB_OTG_HELPER_H_
#define PINS_LIB_OTG_HELPER_H_

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "artifacts/otg.grpc.pb.h"
#include "artifacts/otg.pb.h"

namespace pins_test::otg_helper {

void AddPorts(otg::Config& config, absl::string_view src_port_name,
              absl::string_view dst_port_name,
              absl::string_view src_port_location,
              absl::string_view dst_port_location);

otg::Flow& CreateFlow(otg::Config& config, absl::string_view src_port_name,
                      absl::string_view dst_port_name,
                      absl::string_view flow_name);

void SetFlowSize(otg::Flow& flow, int flow_size);

void SetFlowDuration(otg::Flow& flow, int pkt_count);

void SetFlowRatePps(otg::Flow& flow, int flow_rate);

otg::FlowEthernet& AddEthernetHeader(otg::Flow& flow, absl::string_view src_mac,
                                     absl::string_view dst_mac);

otg::FlowIpv4& AddIPv4Header(otg::Flow& flow, absl::string_view src_ipv4,
                             absl::string_view dst_ipv4);

void SetIPv4Priority(otg::FlowIpv4& ip_packet, int dscp, int ecn);

otg::FlowIpv6& AddIPv6Header(otg::Flow& flow, absl::string_view src_ipv6,
                             absl::string_view dst_ipv6);

absl::Status SetTrafficTransmissionState(
    otg::Openapi::StubInterface& otg_stub,
    otg::StateTrafficFlowTransmit::State::Enum transmission_state);

}  // namespace pins_test::otg_helper

#endif  // PINS_LIB_OTG_HELPER_H_
