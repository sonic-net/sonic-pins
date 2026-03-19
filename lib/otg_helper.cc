#include "lib/otg_helper.h"

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "artifacts/otg.grpc.pb.h"
#include "artifacts/otg.pb.h"
#include "grpcpp/client_context.h"
#include "gutil/status.h"

namespace pins_test::otg_helper {

void AddPorts(otg::Config& config, absl::string_view src_port_name,
              absl::string_view dst_port_name,
              absl::string_view src_port_location,
              absl::string_view dst_port_location) {
  otg::Port* src_port = config.add_ports();
  otg::Port* dst_port = config.add_ports();
  src_port->set_name(src_port_name);
  dst_port->set_name(dst_port_name);
  src_port->set_location(src_port_location);
  dst_port->set_location(dst_port_location);
}

otg::Flow& CreateFlow(otg::Config& config, absl::string_view src_port_name,
                      absl::string_view dst_port_name,
                      absl::string_view flow_name) {
  otg::Flow* flow = config.add_flows();
  flow->set_name(flow_name);
  flow->mutable_tx_rx()->set_choice(otg::FlowTxRx::Choice::port);
  flow->mutable_tx_rx()->mutable_port()->set_tx_name(src_port_name);
  flow->mutable_tx_rx()->mutable_port()->set_rx_name(dst_port_name);
  return *flow;
}

void SetFlowSize(otg::Flow& flow, int flow_size) {
  flow.mutable_size()->set_choice(otg::FlowSize::Choice::fixed);
  flow.mutable_size()->set_fixed(flow_size);
}

void SetFlowDuration(otg::Flow& flow, int pkt_count) {
  flow.mutable_duration()->set_choice(otg::FlowDuration::Choice::fixed_packets);
  flow.mutable_duration()->mutable_fixed_packets()->set_packets(pkt_count);
}

void SetFlowRatePps(otg::Flow& flow, int flow_rate) {
  flow.mutable_rate()->set_choice(otg::FlowRate::Choice::pps);
  flow.mutable_rate()->set_pps(flow_rate);
}

otg::FlowEthernet& AddEthernetHeader(otg::Flow& flow, absl::string_view src_mac,
                                     absl::string_view dst_mac) {
  otg::FlowHeader* eth_packet = flow.add_packet();
  eth_packet->set_choice(otg::FlowHeader::Choice::ethernet);
  otg::FlowEthernet* eth_header = eth_packet->mutable_ethernet();
  eth_header->mutable_src()->set_choice(
      otg::PatternFlowEthernetSrc::Choice::value);
  eth_header->mutable_dst()->set_choice(
      otg::PatternFlowEthernetDst::Choice::value);
  eth_header->mutable_src()->set_value(src_mac);
  eth_header->mutable_dst()->set_value(dst_mac);
  return *eth_header;
}

otg::FlowIpv4& AddIPv4Header(otg::Flow& flow, absl::string_view src_ipv4,
                             absl::string_view dst_ipv4) {
  otg::FlowHeader* ipv4_packet = flow.add_packet();
  ipv4_packet->set_choice(otg::FlowHeader::Choice::ipv4);
  otg::FlowIpv4* ipv4_header = ipv4_packet->mutable_ipv4();
  ipv4_header->mutable_src()->set_choice(
      otg::PatternFlowIpv4Src::Choice::value);
  ipv4_header->mutable_dst()->set_choice(
      otg::PatternFlowIpv4Dst::Choice::value);
  ipv4_header->mutable_src()->set_value(src_ipv4);
  ipv4_header->mutable_dst()->set_value(dst_ipv4);
  return *ipv4_header;
}

void SetIPv4Priority(otg::FlowIpv4& ip_packet, int dscp, int ecn) {
  ip_packet.mutable_priority()->set_choice(otg::FlowIpv4Priority::Choice::dscp);
  ip_packet.mutable_priority()->mutable_dscp()->mutable_phb()->set_value(dscp);
  ip_packet.mutable_priority()->mutable_dscp()->mutable_ecn()->set_value(ecn);
}

otg::FlowIpv6& AddIPv6Header(otg::Flow& flow, absl::string_view src_ipv6,
                             absl::string_view dst_ipv6) {
  otg::FlowHeader* ipv6_packet = flow.add_packet();
  ipv6_packet->set_choice(otg::FlowHeader::Choice::ipv6);
  otg::FlowIpv6* ipv6_header = ipv6_packet->mutable_ipv6();
  ipv6_header->mutable_src()->set_choice(
      otg::PatternFlowIpv6Src::Choice::value);
  ipv6_header->mutable_dst()->set_choice(
      otg::PatternFlowIpv6Dst::Choice::value);
  ipv6_header->mutable_src()->set_value(src_ipv6);
  ipv6_header->mutable_dst()->set_value(dst_ipv6);
  return *ipv6_header;
}

absl::Status SetTrafficTransmissionState(
    otg::Openapi::StubInterface& otg_stub,
    otg::StateTrafficFlowTransmit::State::Enum transmission_state) {
  otg::SetControlStateRequest set_state_request;
  otg::SetControlStateResponse set_state_response;
  grpc::ClientContext set_state_context;
  set_state_request.mutable_control_state()->set_choice(
      otg::ControlState::Choice::traffic);
  set_state_request.mutable_control_state()->mutable_traffic()->set_choice(
      otg::StateTraffic::Choice::flow_transmit);
  set_state_request.mutable_control_state()
      ->mutable_traffic()
      ->mutable_flow_transmit()
      ->set_state(transmission_state);
  return gutil::GrpcStatusToAbslStatus(otg_stub.SetControlState(
      &set_state_context, set_state_request, &set_state_response));
}

}  // namespace pins_test::otg_helper
