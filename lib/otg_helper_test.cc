#include "lib/otg_helper.h"

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "artifacts/otg.pb.h"
#include "artifacts/otg_mock.grpc.pb.h"
#include "gmock/gmock.h"
#include "grpcpp/support/status.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"

namespace pins_test::otg_helper {
namespace {

using ::gutil::EqualsProto;
using ::gutil::StatusIs;
using ::testing::_;
using ::testing::Return;

TEST(OtgHelperTest, AddPortsTest) {
  otg::Config config;

  AddPorts(config, /*src_port_name=*/"eth-1/1", /*dst_port_name=*/"eth-1/2",
           /*src_port_location=*/"00:00:00:00:00:1A",
           /*dst_port_location=*/"00:00:00:00:00:1B");

  EXPECT_THAT(config, EqualsProto(R"pb(
                ports { name: "eth-1/1" location: "00:00:00:00:00:1A" }
                ports { name: "eth-1/2" location: "00:00:00:00:00:1B" }
              )pb"));
}

TEST(OtgHelperTest, CreateFlowTest) {
  otg::Config config;
  otg::Flow& flow = CreateFlow(config, /*src_port_name=*/"eth-1/1",
                               /*dst_port_name=*/"eth-1/2",
                               /*flow_name=*/"test_flow");

  EXPECT_THAT(config, EqualsProto(R"pb(
                flows {
                  name: "test_flow"
                  tx_rx {
                    choice: port
                    port { tx_name: "eth-1/1" rx_name: "eth-1/2" }
                  }
                }
              )pb"));

  EXPECT_THAT(flow, EqualsProto(config.flows(0)));
}

TEST(OtgHelperTest, SetFlowSizeTest) {
  otg::Flow flow;
  SetFlowSize(flow, /*flow_size=*/128);

  EXPECT_THAT(flow, EqualsProto(R"pb(
                size { choice: fixed fixed: 128 }
              )pb"));
}

TEST(OtgHelperTest, SetFlowDurationTest) {
  otg::Flow flow;
  SetFlowDuration(flow, /*pkt_count=*/1000);

  EXPECT_THAT(flow, EqualsProto(R"pb(
                duration {
                  choice: fixed_packets
                  fixed_packets { packets: 1000 }
                }
              )pb"));
}

TEST(OtgHelperTest, SetFlowRatePpsTest) {
  otg::Flow flow;
  SetFlowRatePps(flow, /*flow_rate=*/100);

  EXPECT_THAT(flow, EqualsProto(R"pb(
                rate { choice: pps pps: 100 }
              )pb"));
}

TEST(OtgHelperTest, AddEthernetHeaderTest) {
  otg::Flow flow;
  otg::FlowEthernet& eth_header =
      AddEthernetHeader(flow, /*src_mac=*/"00:00:00:00:00:1A",
                        /*dst_mac=*/"00:00:00:00:00:1B");

  EXPECT_THAT(flow, EqualsProto(R"pb(
                packet {
                  choice: ethernet
                  ethernet {
                    src { choice: value value: "00:00:00:00:00:1A" }
                    dst { choice: value value: "00:00:00:00:00:1B" }
                  }
                }
              )pb"));

  EXPECT_THAT(eth_header, EqualsProto(flow.packet(0).ethernet()));
}

TEST(OtgHelperTest, AddIPv4HeaderTest) {
  otg::Flow flow;
  otg::FlowIpv4& ipv4_header =
      AddIPv4Header(flow, /*src_ipv4=*/"192.0.2.1", /*dst_ipv4=*/"192.0.2.2");

  EXPECT_THAT(flow, EqualsProto(R"pb(
                packet {
                  choice: ipv4
                  ipv4 {
                    src { choice: value value: "192.0.2.1" }
                    dst { choice: value value: "192.0.2.2" }
                  }
                }
              )pb"));

  EXPECT_THAT(ipv4_header, EqualsProto(flow.packet(0).ipv4()));
}

TEST(OtgHelperTest, SetIPv4PriorityTest) {
  otg::FlowIpv4 ipv4_header;

  SetIPv4Priority(ipv4_header, /*dscp=*/8, /*ecn=*/2);

  EXPECT_THAT(ipv4_header, EqualsProto(R"pb(
                priority {
                  choice: dscp
                  dscp {
                    phb { value: 8 }
                    ecn { value: 2 }
                  }
                }
              )pb"));
}

TEST(OtgHelperTest, AddIPv6HeaderTest) {
  otg::Flow flow;
  otg::FlowIpv6& ipv6_header = AddIPv6Header(flow, /*src_ipv6=*/"2001:db8::1",
                                             /*dst_ipv6=*/"2001:db8::2");

  EXPECT_THAT(flow, EqualsProto(R"pb(
                packet {
                  choice: ipv6
                  ipv6 {
                    src { choice: value value: "2001:db8::1" }
                    dst { choice: value value: "2001:db8::2" }
                  }
                }
              )pb"));

  EXPECT_THAT(ipv6_header, EqualsProto(flow.packet(0).ipv6()));
}

TEST(OtgHelperTest, SetTrafficTransmissionStateSuccess) {
  otg::MockOpenapiStub mock_stub;

  EXPECT_CALL(mock_stub, SetControlState(_, EqualsProto(R"pb(
                                           control_state {
                                             choice: traffic
                                             traffic {
                                               choice: flow_transmit
                                               flow_transmit { state: start }
                                             }
                                           }
                                         )pb"),
                                         _))
      .WillOnce(Return(grpc::Status::OK));

  EXPECT_OK(SetTrafficTransmissionState(
      mock_stub, otg::StateTrafficFlowTransmit::State::start));
}

TEST(OtgHelperTest, SetTrafficTransmissionStateFailure) {
  otg::MockOpenapiStub mock_stub;

  EXPECT_CALL(mock_stub, SetControlState(_, EqualsProto(R"pb(
                                           control_state {
                                             choice: traffic
                                             traffic {
                                               choice: flow_transmit
                                               flow_transmit { state: stop }
                                             }
                                           }
                                         )pb"),
                                         _))
      .WillOnce(
          Return(grpc::Status(grpc::StatusCode::INTERNAL, "Mock RPC error")));

  EXPECT_THAT(SetTrafficTransmissionState(
                  mock_stub, otg::StateTrafficFlowTransmit::State::stop),
              StatusIs(absl::StatusCode::kInternal, "Mock RPC error"));
}

}  // namespace
}  // namespace pins_test::otg_helper
