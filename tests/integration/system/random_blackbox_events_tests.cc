// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "tests/integration/system/random_blackbox_events_tests.h"

#include <functional>
#include <limits>
#include <memory>
#include <optional>
#include <string>
#include <thread>
#include <utility>
#include <vector>

#include "absl/cleanup/cleanup.h"
#include "absl/log/log.h"
#include "absl/random/random.h"
#include "absl/status/statusor.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "gmock/gmock.h"
#include "google/rpc/code.pb.h"
#include "grpcpp/client_context.h"
#include "grpcpp/impl/call_op_set.h"
#include "grpcpp/support/sync_stream.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "lib/basic_traffic/basic_traffic.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/p4rt/p4rt_port.h"
#include "lib/utils/generic_testbed_utils.h"
#include "lib/validator/validator_lib.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_fuzzer/annotation_util.h"
#include "p4_fuzzer/fuzz_util.h"
#include "p4_fuzzer/fuzzer.pb.h"
#include "p4_fuzzer/fuzzer_config.h"
#include "p4_fuzzer/switch_state.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4_infra/p4_pdpi/packetlib/packetlib.pb.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "proto/gnmi/gnmi.pb.h"
#include "sai_p4/fixed/roles.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/proto/generic_testbed.pb.h"
#include "thinkit/switch.h"
#include "thinkit/test_environment.h"

namespace pins_test {
namespace {

class ScopedThread {
 public:
  ScopedThread(std::function<void(const bool&)> body)
      : time_to_exit_(false),
        thread_(std::move(body), std::cref(time_to_exit_)) {}

  ~ScopedThread() {
    time_to_exit_ = true;
    thread_.join();
  }

 private:
  bool time_to_exit_;
  std::thread thread_;
};

}  // namespace

TEST_P(RandomBlackboxEventsTest, ControlPlaneWithTrafficWithoutValidation) {
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<thinkit::GenericTestbed> testbed,
                       GetTestbedWithRequirements(
                           gutil::ParseProtoOrDie<thinkit::TestRequirements>(
                               R"pb(interface_requirements {
                                      count: 2
                                      interface_mode: CONTROL_INTERFACE
                                    })pb")));

  // Initial sanity check.
  ASSERT_OK(SwitchReady(testbed->Sut()));

  // Setup gNMI subscription request.
  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, testbed->Sut().CreateGnmiStub());
  auto subscription_request =
      gutil::ParseProtoFileOrDie<gnmi::SubscribeRequest>(
          "tests/integration/system/"
          "gnmi_subscription_request.textproto");
  grpc::ClientContext subscribe_context;
  auto subscription = gnmi_stub->Subscribe(&subscribe_context);
  subscription->WriteLast(subscription_request, grpc::WriteOptions());
  std::thread subscribe_thread([&subscription] {
    gnmi::SubscribeResponse response;
    while (subscription->Read(&response)) {
      LOG_EVERY_POW_2(INFO)
          << "Received subscribe notification (Count: " << COUNTER
          << "): " << response.ShortDebugString();
    }
  });
  absl::Cleanup cancel_subscribe = [&subscribe_context, &subscribe_thread] {
    subscribe_context.TryCancel();
    subscribe_thread.join();
  };

  // Setup fuzzer thread.
  ASSERT_OK_AND_ASSIGN(std::vector<P4rtPortId> port_ids,
                       pins_test::GetMatchingP4rtPortIds(
                           *gnmi_stub, pins_test::IsEnabledEthernetInterface));

  p4::config::v1::P4Info p4_info;
  if (GetParam().p4_info.has_value()) {
    p4_info = *std::move(GetParam().p4_info);
  } else {
    ASSERT_OK_AND_ASSIGN(auto p4rt_session,
                         pdpi::P4RuntimeSession::Create(testbed->Sut()));
    ASSERT_OK_AND_ASSIGN(p4::v1::GetForwardingPipelineConfigResponse response,
                         pdpi::GetForwardingPipelineConfig(p4rt_session.get()));
    p4_info = std::move(*response.mutable_config()->mutable_p4info());
  }

  p4_fuzzer::ConfigParams fuzzer_config_params =
      GetParam().fuzzer_config_params;
  fuzzer_config_params.ports = std::move(port_ids);
  ASSERT_OK_AND_ASSIGN(p4_fuzzer::FuzzerConfig config,
                       p4_fuzzer::FuzzerConfig::Create(
                           p4_info, std::move(fuzzer_config_params)));
  ASSERT_OK_AND_ASSIGN(
      auto p4rt_session,
      pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
          testbed->Sut(), /*gnmi_config=*/std::nullopt, std::move(p4_info)));
  absl::Cleanup clear_p4rt_entries = [&] {
    absl::Status status = pdpi::ClearEntities(*p4rt_session);
    if (!status.ok()) {
      LOG(ERROR) << "Failed to cleanup table entries: " << status;
    }
  };
  {
    ScopedThread p4rt_fuzzer([&config,
                              &p4rt_session](const bool& time_to_exit) {
      absl::BitGen generator;
      p4_fuzzer::SwitchState state(config.GetIrP4Info());
      while (!time_to_exit) {
        p4_fuzzer::AnnotatedWriteRequest annotated_request =
            p4_fuzzer::FuzzWriteRequest(&generator, config, state,
                                        std::numeric_limits<int>::max());
        p4::v1::WriteRequest request =
            p4_fuzzer::RemoveAnnotations(annotated_request);
        request.set_device_id(p4rt_session->DeviceId());
        request.set_role(P4RUNTIME_ROLE_SDN_CONTROLLER);
        *request.mutable_election_id() = p4rt_session->ElectionId();

        ASSERT_OK_AND_ASSIGN(
            pdpi::IrWriteRpcStatus response,
            pdpi::GrpcStatusToIrWriteRpcStatus(
                p4rt_session->WriteAndReturnGrpcStatus(request),
                request.updates_size()));

        for (int i = 0; i < response.rpc_response().statuses().size(); i++) {
          const pdpi::IrUpdateStatus& status =
              response.rpc_response().statuses(i);
          const p4::v1::Update& update = request.updates(i);
          EXPECT_NE(status.code(), google::rpc::Code::INTERNAL)
              << "Fuzzing should never cause an INTERNAL error, but got: "
              << status.DebugString();

          if (status.code() == google::rpc::Code::OK) {
            ASSERT_OK(state.ApplyUpdate(update));
          }
        }

        EXPECT_OK(pdpi::ReadPiTableEntries(p4rt_session.get()).status());
      }
    });

    // Send traffic and report discrepancies.
    const auto test_packet = gutil::ParseProtoOrDie<packetlib::Packet>(R"pb(
      headers {
        ethernet_header {
          ethernet_destination: "02:03:04:05:06:07"
          ethernet_source: "00:01:02:03:04:05"
          ethertype: "0x0800"
        }
      }
      headers {
        ipv4_header {
          version: "0x4"
          ihl: "0x5"
          dscp: "0x03"
          ecn: "0x0"
          identification: "0x0000"
          flags: "0x0"
          fragment_offset: "0x0000"
          ttl: "0x20"
          protocol: "0x11"
          ipv4_source: "1.2.3.4"
        }
      }
      headers {
        udp_header { source_port: "0x0000" destination_port: "0x0000" }
      })pb");
    std::vector<std::string> sut_control_interfaces =
        GetSutInterfaces(FromTestbed(GetAllControlLinks, *testbed));
    ASSERT_OK_AND_ASSIGN(
        auto statistics,
        basic_traffic::SendTraffic(
            *testbed, p4rt_session.get(), config.GetIrP4Info(),
            {basic_traffic::InterfacePair{
                .ingress_interface = sut_control_interfaces[0],
                .egress_interface = sut_control_interfaces[1]}},
            {test_packet}, absl::Minutes(5)));
    for (const basic_traffic::TrafficStatistic& statistic : statistics) {
      if (statistic.packets_sent != statistic.packets_received) {
        LOG(WARNING) << statistic.interfaces.ingress_interface << " -> "
                     << statistic.interfaces.egress_interface
                     << ": Count mismatch; sent " << statistic.packets_sent
                     << " received " << statistic.packets_received << ", "
                     << statistic.packets_routed_incorrectly
                     << " routed incorrectly.";
      }
    }
  }
  // Final sanity check.
  ASSERT_OK(SwitchReady(testbed->Sut()));
}

}  // namespace pins_test
