// Copyright 2025 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "tests/integration/system/nsf/traffic_helpers/otg_helper.h"

#include <sys/types.h>

#include <cstdint>
#include <memory>
#include <string>
#include <variant>
#include <vector>

#include "absl/algorithm/container.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "artifacts/otg.grpc.pb.h"
#include "artifacts/otg.pb.h"
#include "glog/logging.h"
#include "grpcpp/client_context.h"
#include "gutil/overload.h"
#include "gutil/status.h"
#include "lib/utils/generic_testbed_utils.h"
#include "lib/validator/validator_lib.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/mirror_testbed.h"

namespace pins_test {
namespace {

// Struct to hold the per-flow traffic metrics.
// `traffic_outage` is the total duration of time the traffic was dropped during
// the entire duration of traffic flow.
struct TrafficMetrics {
  uint64_t frames_dropped;
  uint64_t bytes_dropped;
  absl::Duration outage_duration;
};

absl::Status SetOtgConfig(otg::Openapi::StubInterface* stub,
                          const otg::SetConfigRequest& request,
                          otg::SetConfigResponse& response) {
  grpc::ClientContext context;
  return gutil::GrpcStatusToAbslStatus(
      stub->SetConfig(&context, request, &response));
}

TrafficMetrics GetTrafficMetrics(const otg::FlowMetric& flow_metric,
                                 bool enable_linerate) {
  TrafficMetrics metrics;
  metrics.frames_dropped = flow_metric.frames_tx() - flow_metric.frames_rx();
  metrics.bytes_dropped = flow_metric.bytes_tx() - flow_metric.bytes_rx();
  if (flow_metric.frames_tx() == 0) {
    metrics.outage_duration = absl::InfiniteDuration();
    return metrics;
  }

  const double outage_fraction = static_cast<double>(metrics.frames_dropped) /
                                 static_cast<double>(flow_metric.frames_tx());
  const double total_duration_ns =
      flow_metric.timestamps().last_timestamp_ns() -
      flow_metric.timestamps().first_timestamp_ns();
  double outage_duration_ns = total_duration_ns * outage_fraction;
  if (enable_linerate) {
    outage_duration_ns *= 1e8;
  }
  metrics.outage_duration = absl::Nanoseconds(outage_duration_ns);

  return metrics;
}

}  // namespace

absl::Status OtgHelper::StartTraffic(Testbed& testbed) {
  return std::visit(
      gutil::Overload{
          [this](std::unique_ptr<thinkit::GenericTestbed>& testbed)
              -> absl::Status {
            ASSIGN_OR_RETURN(std::vector<InterfaceLink> up_links,
                             GetUpLinks(GetAllTrafficGeneratorLinks, *testbed));
            if (up_links.size() < 2) {
              return absl::InvalidArgumentError(
                  "Test requires at least 2 SUT ports connected to a Software "
                  "(Host) or Hardware (Ixia) Traffic Generator");
            }

            // We sort the peer interfaces to ensure that the traffic Tx/Rx
            // interfaces match with those programmed on the SUT.
            absl::c_sort(up_links,
                         [](const InterfaceLink& a, const InterfaceLink& b) {
                           return a.peer_interface < b.peer_interface;
                         });

            // Create config.
            otg::SetConfigRequest set_config_request;
            otg::SetConfigResponse set_config_response;
            auto* config = set_config_request.mutable_config();

            // Randomly pick source and destination hosts.
            const std::string otg_src_port =
                up_links.front().peer_traffic_location;
            const std::string otg_dst_port =
                up_links.back().peer_traffic_location;
            const std::string otg_src_mac = up_links.front().peer_mac_address;
            const std::string otg_dst_mac = up_links.back().peer_mac_address;
            const std::string otg_src_ip = up_links.front().peer_ipv6_address;
            const std::string otg_dst_ip = up_links.back().peer_ipv6_address;
            const std::string otg_src_loc =
                up_links.front().peer_traffic_location;
            const std::string otg_dst_loc =
                up_links.back().peer_traffic_location;

            // Add ports.
            auto* src_port = config->add_ports();
            auto* dst_port = config->add_ports();
            src_port->set_name(otg_src_port);
            dst_port->set_name(otg_dst_port);
            src_port->set_location(otg_src_loc);
            dst_port->set_location(otg_dst_loc);

            // helper function. Set layer1.
            auto* layer1 = config->add_layer1();
            layer1->set_name("ly");
            layer1->add_port_names(otg_src_port);
            layer1->add_port_names(otg_dst_port);

            // linerate.
            // Set speed.
            if (enable_linerate_) {
              layer1->set_speed(otg::Layer1::Speed::speed_200_gbps);
            } else {
              layer1->set_speed(otg::Layer1::Speed::speed_1_gbps);
            }

            // Set MTU.
            layer1->set_mtu(9000);

            // Create flow.
            auto* flow = config->add_flows();
            flow->set_name("Host Traffic flow");

            // Set Tx / Rx ports.
            flow->mutable_tx_rx()->set_choice(otg::FlowTxRx::Choice::port);
            flow->mutable_tx_rx()->mutable_port()->set_tx_name(otg_src_port);
            flow->mutable_tx_rx()->mutable_port()->set_rx_name(otg_dst_port);

            // Set packet size.
            flow->mutable_size()->set_choice(otg::FlowSize::Choice::fixed);
            flow->mutable_size()->set_fixed(256);

            // Set transmission duration.
            flow->mutable_duration()->set_choice(
                otg::FlowDuration::Choice::continuous);

            // Set transmission rate.
            flow->mutable_rate()->set_choice(otg::FlowRate::Choice::percentage);
            if (enable_linerate_) {
              flow->mutable_rate()->set_percentage(98);
            } else {
              flow->mutable_rate()->set_percentage(5);
            }

            // Set capture metrics.
            flow->mutable_metrics()->set_enable(true);
            flow->mutable_metrics()->set_loss(false);
            flow->mutable_metrics()->set_timestamps(true);
            flow->mutable_metrics()->mutable_latency()->set_enable(true);
            flow->mutable_metrics()->mutable_latency()->set_mode(
                otg::FlowLatencyMetrics::Mode::cut_through);

            // Set ethernet header.
            auto* eth_packet = flow->add_packet();
            eth_packet->set_choice(otg::FlowHeader::Choice::ethernet);
            eth_packet->mutable_ethernet()->mutable_src()->set_choice(
                otg::PatternFlowEthernetSrc::Choice::value);
            eth_packet->mutable_ethernet()->mutable_dst()->set_choice(
                otg::PatternFlowEthernetDst::Choice::value);
            eth_packet->mutable_ethernet()->mutable_src()->set_value(
                otg_src_mac);
            eth_packet->mutable_ethernet()->mutable_dst()->set_value(
                otg_dst_mac);

            // Set IP header.
            auto* ip_packet = flow->add_packet();
            ip_packet->set_choice(otg::FlowHeader::Choice::ipv6);
            ip_packet->mutable_ipv6()->mutable_src()->set_choice(
                otg::PatternFlowIpv6Src::Choice::value);
            ip_packet->mutable_ipv6()->mutable_dst()->set_choice(
                otg::PatternFlowIpv6Dst::Choice::value);
            ip_packet->mutable_ipv6()->mutable_src()->set_value(otg_src_ip);
            ip_packet->mutable_ipv6()->mutable_dst()->set_value(otg_dst_ip);

            // Set the config.
            otg::Openapi::StubInterface* stub = testbed->GetTrafficClient();

            RETURN_IF_ERROR(WaitForCondition(SetOtgConfig, absl::Minutes(5),
                                             stub, set_config_request,
                                             set_config_response));

            // Start the traffic.
            otg::SetControlStateRequest request;
            otg::SetControlStateResponse response;
            grpc::ClientContext context;
            request.mutable_control_state()->set_choice(
                otg::ControlState::Choice::traffic);
            request.mutable_control_state()->mutable_traffic()->set_choice(
                otg::StateTraffic::Choice::flow_transmit);
            request.mutable_control_state()
                ->mutable_traffic()
                ->mutable_flow_transmit()
                ->set_state(otg::StateTrafficFlowTransmit::State::start);
            return gutil::GrpcStatusToAbslStatus(
                stub->SetControlState(&context, request, &response));
          },
          [&](thinkit::MirrorTestbed* testbed) {
            return absl::UnimplementedError("MirrorTestbed not implemented");
          }},
      testbed);
}

absl::Status OtgHelper::StopTraffic(Testbed& testbed) {
  return std::visit(
      gutil::Overload{
          [&](std::unique_ptr<thinkit::GenericTestbed>& testbed)
              -> absl::Status {
            otg::Openapi::StubInterface* stub = testbed->GetTrafficClient();
            otg::SetControlStateRequest request;
            otg::SetControlStateResponse response;
            ::grpc::ClientContext context;
            request.mutable_control_state()->set_choice(
                otg::ControlState::Choice::traffic);
            request.mutable_control_state()->mutable_traffic()->set_choice(
                otg::StateTraffic::Choice::flow_transmit);
            request.mutable_control_state()
                ->mutable_traffic()
                ->mutable_flow_transmit()
                ->set_state(otg::StateTrafficFlowTransmit::State::stop);
            return gutil::GrpcStatusToAbslStatus(
                stub->SetControlState(&context, request, &response));
          },
          [&](thinkit::MirrorTestbed* testbed) {
            return absl::UnimplementedError("MirrorTestbed not implemented");
          }},
      testbed);
}

absl::Status OtgHelper::ValidateTraffic(Testbed& testbed,
                                        absl::Duration max_acceptable_outage) {
  return std::visit(
      gutil::Overload{
          [&](std::unique_ptr<thinkit::GenericTestbed>& testbed)
              -> absl::Status {
            otg::Openapi::StubInterface* stub = testbed->GetTrafficClient();
            otg::GetMetricsRequest metrics_req;
            otg::GetMetricsResponse metrics_res;
            grpc::ClientContext metrics_ctx;

            metrics_req.mutable_metrics_request()->set_choice(
                otg::MetricsRequest::Choice::flow);
            RETURN_IF_ERROR(gutil::GrpcStatusToAbslStatus(
                stub->GetMetrics(&metrics_ctx, metrics_req, &metrics_res)));

            RETURN_IF_ERROR(testbed->Environment().StoreTestArtifact(
                absl::StrCat("OTG_Traffic_Metrics_",
                             absl::FormatTime("%H_%M_%S", absl::Now(),
                                              absl::LocalTimeZone()),
                             ".txt"),
                metrics_res.DebugString()));
            // Verify flow metrics is not empty.
            if (metrics_res.metrics_response().flow_metrics().empty()) {
              return absl::InternalError(
                  "Cannot validate traffic as no flow metrics received.");
            }

            // Verify transmission completion and no frames or bytes drops for
            // each flow.
            std::vector<std::string> errors;
            for (const auto& flow_metric :
                 metrics_res.metrics_response().flow_metrics()) {
              bool transmission_stopped =
                  flow_metric.transmit() == otg::FlowMetric::Transmit::stopped;

              if (flow_metric.frames_tx() == 0) {
                errors.push_back(
                    absl::StrCat("Flow name:\t\t", flow_metric.name(),
                                 "\nFrames Tx:\t\t", flow_metric.frames_tx(),
                                 "\nBytes Tx:\t\t", flow_metric.bytes_tx(),
                                 transmission_stopped
                                     ? ""
                                     : "\nTransmission not completed within "
                                       "the expected time."));
                continue;
              }

              TrafficMetrics traffic_metrics =
                  GetTrafficMetrics(flow_metric, enable_linerate_);
              LOG(INFO) << "Traffic outage: "
                        << traffic_metrics.outage_duration;
              LOG(INFO) << "Max permissible traffic outage: "
                        << max_acceptable_outage;
              if (traffic_metrics.outage_duration <= max_acceptable_outage)
                continue;

              errors.push_back(absl::StrCat(
                  "Flow name:\t\t", flow_metric.name(), "\nTraffic outage:\t\t",
                  traffic_metrics.outage_duration,
                  "\nMax permissible traffic outage:\t\t",
                  max_acceptable_outage, "\nFrames dropped:\t\t",
                  traffic_metrics.frames_dropped, "\nBytes dropped:\t\t",
                  traffic_metrics.bytes_dropped,
                  transmission_stopped ? ""
                                       : "\nTransmission not completed within "
                                         "the expected time."));
            }

            if (errors.empty()) return absl::OkStatus();
            return absl::InternalError(absl::StrCat(
                "Following errors were observed while validating traffic:\n\n",
                absl::StrJoin(errors, "\n\n")));
          },
          [&](thinkit::MirrorTestbed* testbed) {
            return absl::UnimplementedError("MirrorTestbed not implemented");
          }},
      testbed);
}

}  // namespace pins_test
