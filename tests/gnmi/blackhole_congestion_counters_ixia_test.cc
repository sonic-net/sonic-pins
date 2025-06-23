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

#include "tests/gnmi/blackhole_congestion_counters_ixia_test.h"

#include <sys/types.h>

#include <cmath>
#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/optional.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "include/nlohmann/json.hpp"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/ixia_helper.h"
#include "lib/utils/generic_testbed_utils.h"
#include "lib/utils/json_utils.h"
#include "p4_infra/p4_runtime/p4_runtime_session.h"
#include "p4_infra/packetlib/packetlib.pb.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/generic_testbed_fixture.h"
#include "thinkit/proto/generic_testbed.pb.h"
#include "thinkit/switch.h"

namespace pins_test {
namespace {

using ::nlohmann::json;

constexpr int kInErrorsThresh = 10;
constexpr double kOutDiscardsRateThresh = 0.05;
constexpr int kDecimalToMilliPercent = 1e5;
constexpr uint64_t kOutDiscardsRateThreshMilliPercent =
    kOutDiscardsRateThresh * kDecimalToMilliPercent;

const char kOpenConfigSystemParseKey[] = "openconfig-system:system";
const char kPinsDiagParseKey[] = "diag:diag";

// Takes a `gnmi_config` from the config generator and returns a modified
// version that sets up blackhole and congestion related configs and thresholds
// for the testbed. If the testbed does not support blackhole and congestion
// monitoring, returns an error status.
absl::StatusOr<std::string> SetUpBlackholeCongestionConfig(
    absl::string_view gnmi_config) {
  ASSIGN_OR_RETURN(json gnmi_config_json, json_yang::ParseJson(gnmi_config));

  // Gets the switch-level and port-level configs.
  json& switch_config =
      gnmi_config_json[kOpenConfigSystemParseKey][kPinsDiagParseKey]["config"];
  json& port_profiles =
      gnmi_config_json[kOpenConfigSystemParseKey][kPinsDiagParseKey]
                      ["port-profiles"]["port-profile"];

  if (switch_config.empty() || port_profiles.empty()) {
    return absl::UnimplementedError(
        "Blackhole and congestion monitoring not supported on testbed: Failed "
        "to get switch-level or port-level configs.");
  }

  // Updates switch-level configs.
  switch_config["blackhole-monitoring-enable"] = true;
  switch_config["congestion-monitoring-enable"] = true;

  // Updates port-level configs.
  for (json& port_profile : port_profiles) {
    port_profile["config"]["in-errors-threshold"] = kInErrorsThresh;
    port_profile["config"]["out-discards-rate-threshold"] =
        kOutDiscardsRateThreshMilliPercent;
    // Updates queue-level configs.
    for (json& queue_profile : port_profile["queues"]["queue"]) {
      if (queue_profile["qname"] == "NC1") {
        queue_profile["config"]["dropped-rate-threshold"] =
            kOutDiscardsRateThreshMilliPercent;
      }
    }
  }

  return json_yang::DumpJson(gnmi_config_json);
}

struct IxiaSetUpResult {
  // Ixia reference URL to topology.
  std::string topology_ref;
  // Ixia reference URL to traffic.
  std::string traffic_ref;
};

absl::StatusOr<IxiaSetUpResult> SetUpIxiaForInFcsErrorTest(
    absl::string_view ixia_interface, thinkit::GenericTestbed& generic_testbed,
    int frame_rate, int frame_count) {
  constexpr absl::string_view kLldpMulticastMac = "01:80:c2:00:00:0e";
  constexpr absl::string_view kSrcMac = "00:01:02:03:04:05";

  ASSIGN_OR_RETURN(ixia::IxiaPortInfo ixia_port,
                   ixia::ExtractPortInfo(ixia_interface));

  // Connect to the Ixia.
  ASSIGN_OR_RETURN(std::string topology_ref,
                   ixia::IxiaConnect(ixia_port.hostname, generic_testbed));

  // Connect to the Ixia card/port.
  ASSIGN_OR_RETURN(std::string vport_ref,
                   ixia::IxiaVport(topology_ref, ixia_port.card, ixia_port.port,
                                   generic_testbed));

  // Start a session.
  ASSIGN_OR_RETURN(std::string traffic_ref,
                   ixia::IxiaSession(vport_ref, generic_testbed));

  // Set the frame rate.
  RETURN_IF_ERROR(ixia::SetFrameRate(traffic_ref, frame_rate, generic_testbed));

  // Set the frame count.
  RETURN_IF_ERROR(
      ixia::SetFrameCount(traffic_ref, frame_count, generic_testbed));

  // Set the destination MAC address to LLDP multicast.
  RETURN_IF_ERROR(
      ixia::SetDestMac(traffic_ref, kLldpMulticastMac, generic_testbed));

  // Set the source MAC address.
  RETURN_IF_ERROR(ixia::SetSrcMac(traffic_ref, kSrcMac, generic_testbed));

  // PATCH to /ixnetwork/traffic/trafficItem/1/configElement/1
  // with {"crc":"badCrc"}
  const std::string badcrc_path = absl::StrCat(traffic_ref, "/configElement/1");
  const std::string badcrc_json = "{\"crc\":\"badCrc\"}";
  ASSIGN_OR_RETURN(thinkit::HttpResponse badcrc_response,
                   generic_testbed.SendRestRequestToIxia(
                       thinkit::RequestType::kPatch, badcrc_path, badcrc_json));
  EXPECT_EQ(badcrc_response.response_code, 200) << badcrc_response.response;
  if (badcrc_response.response_code != 200) {
    return absl::InternalError(
        absl::StrCat("Failed to patch ", badcrc_path, " with ", badcrc_json,
                     ". Response: ", badcrc_response.response));
  }

  return IxiaSetUpResult{topology_ref, traffic_ref};
}

TEST_P(BlackholeCongestionCountersIxiaTestFixture,
       TestInFcsErrorsAboveThreshIncrementBlackholeCounters) {
  constexpr uint32_t kInFcsErrorsPerSecond = kInErrorsThresh + 5;
  constexpr uint32_t kInFcsErrorsDurationSeconds = 10;
  constexpr uint32_t kInFcsErrorsCount =
      kInFcsErrorsPerSecond * kInFcsErrorsDurationSeconds;

  ASSERT_OK_AND_ASSIGN(
      InErrorCounters in_fcs_error_counters_delta,
      TriggerInFcsErrors(kInFcsErrorsPerSecond, kInFcsErrorsCount));

  // Check the changes are as expected.
  EXPECT_EQ(in_fcs_error_counters_delta.port_in_error_packets,
            kInFcsErrorsCount);
  EXPECT_GE(in_fcs_error_counters_delta.port_blackhole_in_error_events, 1);
  EXPECT_GE(in_fcs_error_counters_delta.switch_blackhole_in_error_events, 1);
  EXPECT_GE(in_fcs_error_counters_delta.switch_blackhole_events, 1);
  EXPECT_EQ(in_fcs_error_counters_delta.port_blackhole_in_error_events,
            in_fcs_error_counters_delta.switch_blackhole_events);
}

TEST_P(BlackholeCongestionCountersIxiaTestFixture,
       TestInFcsErrorsBelowThreshNotIncrementBlackholeCounters) {
  constexpr uint32_t kInFcsErrorsPerSecond = kInErrorsThresh - 5;
  constexpr uint32_t kInFcsErrorsDurationSeconds = 10;
  constexpr uint32_t kInFcsErrorsCount =
      kInFcsErrorsPerSecond * kInFcsErrorsDurationSeconds;

  ASSERT_OK_AND_ASSIGN(
      InErrorCounters in_fcs_error_counters_delta,
      TriggerInFcsErrors(kInFcsErrorsPerSecond, kInFcsErrorsCount));

  // Check the changes are as expected.
  EXPECT_EQ(in_fcs_error_counters_delta.port_in_error_packets,
            kInFcsErrorsCount);
  EXPECT_EQ(in_fcs_error_counters_delta.port_blackhole_in_error_events, 0);
  EXPECT_EQ(in_fcs_error_counters_delta.switch_blackhole_in_error_events, 0);
  EXPECT_EQ(in_fcs_error_counters_delta.switch_blackhole_events, 0);
}

constexpr absl::string_view kOutDiscardTestTrafficName =
    "OutDiscardTestTraffic";

absl::StatusOr<IxiaSetUpResult> SetUpIxiaForOutDiscardTest(
    absl::string_view ixia_tx_port, absl::string_view ixia_rx_port,
    thinkit::GenericTestbed& generic_testbed, const int frame_size_in_bytes,
    const int frame_rate, const int dscp) {
  // Extract Ixia port info.
  ASSIGN_OR_RETURN(ixia::IxiaPortInfo ixia_tx_port_info,
                   ixia::ExtractPortInfo(ixia_tx_port));
  ASSIGN_OR_RETURN(ixia::IxiaPortInfo ixia_rx_port_info,
                   ixia::ExtractPortInfo(ixia_rx_port));

  // Connect to Ixia.
  ASSIGN_OR_RETURN(
      std::string topology_ref,
      ixia::IxiaConnect(ixia_tx_port_info.hostname, generic_testbed));

  // Get Ixia reference to Ixia ports.
  ASSIGN_OR_RETURN(std::string tx_vport_ref,
                   ixia::IxiaVport(topology_ref, ixia_tx_port_info.card,
                                   ixia_tx_port_info.port, generic_testbed));
  ASSIGN_OR_RETURN(std::string rx_vport_ref,
                   ixia::IxiaVport(topology_ref, ixia_rx_port_info.card,
                                   ixia_rx_port_info.port, generic_testbed));

  // Set up traffic items with source and destination ports.
  ASSIGN_OR_RETURN(
      std::string traffic_ref,
      ixia::SetUpTrafficItem(tx_vport_ref, rx_vport_ref,
                             kOutDiscardTestTrafficName, generic_testbed));

  // Set up traffic parameters.
  ixia::TrafficParameters traffic_parameters = {
      .frame_size_in_bytes = frame_size_in_bytes,
      .traffic_speed = ixia::FramesPerSecond{frame_rate},
  };
  traffic_parameters.ip_parameters = ixia::Ipv4TrafficParameters{
      .priority =
          ixia::IpPriority{
              .dscp = dscp,
              .ecn = 0,
          },
  };
  RETURN_IF_ERROR(ixia::SetTrafficParameters(traffic_ref, traffic_parameters,
                                             generic_testbed));

  return IxiaSetUpResult{
      .topology_ref = topology_ref,
      .traffic_ref = traffic_ref,
  };
}

absl::StatusOr<int64_t> GetQueuePir(absl::string_view port_name,
                                    absl::string_view queue_name,
                                    gnmi::gNMI::StubInterface& gnmi_stub) {
  // Gets scheduler policy name for port.
  const std::string kSchedulerPolicyNamePath = absl::StrFormat(
      "qos/interfaces/interface[interface-id=%s]/output/scheduler-policy/"
      "config/name",
      port_name);
  const std::string kSchedulerPolicyNameParseStr = "openconfig-qos:name";
  ASSIGN_OR_RETURN(
      std::string port_scheduler_policy_name,
      ReadGnmiPath(&gnmi_stub, kSchedulerPolicyNamePath,
                   gnmi::GetRequest::CONFIG, kSchedulerPolicyNameParseStr));
  port_scheduler_policy_name =
      std::string(StripQuotes(port_scheduler_policy_name));

  // Pulls scheduler policy config.
  const std::string kSchedulerPolicyPath =
      absl::StrFormat("qos/scheduler-policies/scheduler-policy[name=%s]",
                      port_scheduler_policy_name);
  const std::string kSchedulerPolicyParseStr =
      "openconfig-qos:scheduler-policy";
  ASSIGN_OR_RETURN(
      const std::string scheduler_policy_raw_config,
      ReadGnmiPath(&gnmi_stub, kSchedulerPolicyPath, gnmi::GetRequest::CONFIG,
                   kSchedulerPolicyParseStr));
  ASSIGN_OR_RETURN(
      openconfig::Qos::SchedulerPolicy scheduler_policy_proto_config,
      gutil::ParseJsonAsProto<openconfig::Qos::SchedulerPolicy>(
          StripBrackets(scheduler_policy_raw_config),
          /*ignore_unknown_fields=*/true));

  // Looks for config for the queue.
  for (openconfig::Qos::Scheduler& scheduler :
       *scheduler_policy_proto_config.mutable_schedulers()
            ->mutable_scheduler()) {
    if (scheduler.inputs().input_size() != 1) continue;
    const std::string kQueue = scheduler.inputs().input(0).config().queue();
    if (kQueue != queue_name) continue;
    if (scheduler.config().type() !=
        "openconfig-qos-types:TWO_RATE_THREE_COLOR") {
      continue;
    }
    openconfig::Qos::Scheduler::TwoRateThreeColor::Config& config =
        *scheduler.mutable_two_rate_three_color()->mutable_config();
    int64_t pir;
    if (!absl::SimpleAtoi(config.pir(), &pir)) {
      return absl::InvalidArgumentError(
          absl::StrCat("Invalid pir: ", config.pir()));
    }
    return pir;
  }

  return absl::NotFoundError(
      absl::StrCat("No scheduler found for queue: ", queue_name));
}

TEST_P(BlackholeCongestionCountersIxiaTestFixture,
       TestCongestionsAboveThreshIncrementOutDiscardsAndCongestionCounters) {
  constexpr double kOutDiscardsRate = kOutDiscardsRateThresh + 0.025;
  constexpr absl::Duration kTrafficDuration = absl::Seconds(5);
  constexpr double kOutDiscardsRateTolerance = 0.025;

  ASSERT_OK_AND_ASSIGN(OutDiscardCounters out_discard_counters,
                       TriggerOutDiscards(kOutDiscardsRate, kTrafficDuration));

  // Check the changes are as expected.
  double observed_out_discard_rate =
      (double)out_discard_counters.port_out_discard_packets /
      out_discard_counters.port_out_packets;
  LOG(INFO) << "Observed out discard rate: " << observed_out_discard_rate;
  EXPECT_NEAR(observed_out_discard_rate, kOutDiscardsRate,
              kOutDiscardsRateTolerance);
  EXPECT_GE(out_discard_counters.port_blackhole_out_discard_events, 1);
  EXPECT_GE(out_discard_counters.switch_blackhole_out_discard_events, 1);
  EXPECT_GE(out_discard_counters.switch_blackhole_events, 1);
  EXPECT_GE(out_discard_counters.queue_dropped_packet_events, 1);
  EXPECT_GE(out_discard_counters.switch_congestion_events, 1);
}

TEST_P(BlackholeCongestionCountersIxiaTestFixture,
       TestCongestionsBelowThreshNotIncrementOutDiscardsAndCongestionCounters) {
  constexpr double kOutDiscardsRate = kOutDiscardsRateThresh - 0.025;
  constexpr absl::Duration kTrafficDuration = absl::Seconds(5);
  constexpr double kOutDiscardsRateTolerance = 0.025;

  ASSERT_OK_AND_ASSIGN(OutDiscardCounters out_discard_counters,
                       TriggerOutDiscards(kOutDiscardsRate, kTrafficDuration));

  // Check the changes are as expected.
  double observed_out_discard_rate =
      (double)out_discard_counters.port_out_discard_packets /
      out_discard_counters.port_out_packets;
  LOG(INFO) << "Observed out discard rate: " << observed_out_discard_rate;
  EXPECT_NEAR(observed_out_discard_rate, kOutDiscardsRate,
              kOutDiscardsRateTolerance);
  EXPECT_EQ(out_discard_counters.port_blackhole_out_discard_events, 0);
  EXPECT_EQ(out_discard_counters.switch_blackhole_out_discard_events, 0);
  EXPECT_EQ(out_discard_counters.switch_blackhole_events, 0);
  EXPECT_EQ(out_discard_counters.queue_dropped_packet_events, 0);
  EXPECT_EQ(out_discard_counters.switch_congestion_events, 0);
}

}  // namespace

void BlackholeCongestionCountersIxiaTestFixture::SetUp() {
  thinkit::GenericTestbedFixture<>::SetUp();
  // Pick a testbed with an Ixia Traffic Generator. A SUT is assumed.
  thinkit::TestRequirements requirements =
      gutil::ParseProtoOrDie<thinkit::TestRequirements>(
          R"pb(interface_requirements {
                 count: 2
                 interface_mode: TRAFFIC_GENERATOR
               })pb");

  ASSERT_OK_AND_ASSIGN(generic_testbed_,
                       GetTestbedWithRequirements(requirements));

  ASSERT_OK_AND_ASSIGN(std::string blackhole_congestion_config,
                       SetUpBlackholeCongestionConfig(GetParam().gnmi_config));
  ASSERT_OK(generic_testbed_->Environment().StoreTestArtifact(
      "gnmi_config.txt", GetParam().gnmi_config));
  ASSERT_OK(generic_testbed_->Environment().StoreTestArtifact(
      "blackhole_congestion_config.txt", blackhole_congestion_config));

  // Hook up to gNMI.
  ASSERT_OK_AND_ASSIGN(gnmi_stub_, generic_testbed_->Sut().CreateGnmiStub());

  // Set up P4 Runtime session.
  ASSERT_OK_AND_ASSIGN(sut_p4_session_,
                       ConfigureSwitchAndReturnP4RuntimeSession(
                           generic_testbed_->Sut(), blackhole_congestion_config,
                           GetParam().p4_info));

  ASSERT_OK_AND_ASSIGN(
      traffic_generator_links_,
      GetUpLinks(GetAllTrafficGeneratorLinks, *generic_testbed_));
  ASSERT_FALSE(traffic_generator_links_.empty()) << "Ixia links are not ready";
}

void BlackholeCongestionCountersIxiaTestFixture::TearDown() {
  // Restores the gNMI config and clears table entries.
  ASSERT_OK(PushGnmiConfig(generic_testbed_->Sut(), GetParam().gnmi_config));
  ASSERT_OK(p4_runtime::ClearEntities(*sut_p4_session_));
  ASSERT_OK(sut_p4_session_->Finish());
  thinkit::GenericTestbedFixture<>::TearDown();
}

absl::StatusOr<InErrorCounters>
BlackholeCongestionCountersIxiaTestFixture::TriggerInFcsErrors(
    int frame_rate_per_second, int frame_count) {
  const std::string ixia_interface = traffic_generator_links_[0].peer_interface;
  const std::string sut_interface = traffic_generator_links_[0].sut_interface;

  ASSIGN_OR_RETURN(
      IxiaSetUpResult ixia_setup_result,
      SetUpIxiaForInFcsErrorTest(ixia_interface, *generic_testbed_,
                                 frame_rate_per_second, frame_count));

  // Read some initial counters via gMNI from the SUT.
  ASSIGN_OR_RETURN(
      const uint64_t initial_port_in_errors,
      GetInterfaceCounter("in-errors", sut_interface, gnmi_stub_.get()));
  ASSIGN_OR_RETURN(
      const BlackholeSwitchCounters initial_blackhole_switch_counters,
      GetBlackholeSwitchCounters(*gnmi_stub_));
  ASSIGN_OR_RETURN(const BlackholePortCounters initial_blackhole_port_counters,
                   GetBlackholePortCounters(sut_interface, *gnmi_stub_));

  RETURN_IF_ERROR(ixia::StartTraffic(ixia_setup_result.traffic_ref,
                                     ixia_setup_result.topology_ref,
                                     *generic_testbed_));

  absl::SleepFor(absl::Seconds(frame_count / frame_rate_per_second));

  // Re-read the same counters via gMNI from the SUT.
  ASSIGN_OR_RETURN(
      const uint64_t final_port_in_errors,
      GetInterfaceCounter("in-errors", sut_interface, gnmi_stub_.get()));
  ASSIGN_OR_RETURN(
      const BlackholeSwitchCounters final_blackhole_switch_counters,
      GetBlackholeSwitchCounters(*gnmi_stub_));
  ASSIGN_OR_RETURN(const BlackholePortCounters final_blackhole_port_counters,
                   GetBlackholePortCounters(sut_interface, *gnmi_stub_));

  // Compute the change for each counter.
  const uint64_t port_in_errors_delta =
      final_port_in_errors - initial_port_in_errors;
  const BlackholeSwitchCounters blackhole_switch_delta =
      final_blackhole_switch_counters - initial_blackhole_switch_counters;
  const BlackholePortCounters blackhole_port_delta =
      final_blackhole_port_counters - initial_blackhole_port_counters;

  return InErrorCounters{
      .port_in_error_packets = port_in_errors_delta,
      .port_blackhole_in_error_events = blackhole_port_delta.in_error_events,
      .switch_blackhole_in_error_events =
          blackhole_switch_delta.in_error_events,
      // Sometimes fec_not_correctable_events occur which the test can't
      // control, so subtract those from the switch blackhole counter.
      .switch_blackhole_events =
          blackhole_switch_delta.blackhole_events -
          blackhole_switch_delta.fec_not_correctable_events,
  };
}

absl::StatusOr<OutDiscardCounters>
BlackholeCongestionCountersIxiaTestFixture::TriggerOutDiscards(
    const double out_discard_rate, const absl::Duration traffic_duration) {
  // Use NC1 queue to control congestion drop rate.
  constexpr int kNc1Dscp = 50;
  constexpr absl::string_view kNc1QueueName = "NC1";

  EXPECT_GE(traffic_generator_links_.size(), 2);
  if (traffic_generator_links_.size() < 2) {
    return absl::InternalError(absl::StrCat(
        "Test requires at least 2 SUT ports connected to an Ixia"));
  }

  const std::string ixia_tx_port = traffic_generator_links_[0].peer_interface;
  const std::string sut_in_port = traffic_generator_links_[0].sut_interface;

  const std::string ixia_rx_port = traffic_generator_links_[1].peer_interface;
  const std::string sut_out_port = traffic_generator_links_[1].sut_interface;

  // Look up the port IDs used by P4RT for the SUT interfaces.
  absl::flat_hash_map<std::string, std::string> port_id_by_interface;
  ASSIGN_OR_RETURN(port_id_by_interface,
                   GetAllInterfaceNameToPortId(*gnmi_stub_));
  ASSIGN_OR_RETURN(const std::string sut_in_port_id,
                   gutil::FindOrStatus(port_id_by_interface, sut_in_port));
  ASSIGN_OR_RETURN(const std::string sut_out_port_id,
                   gutil::FindOrStatus(port_id_by_interface, sut_out_port));

  constexpr int kDefaultFrameSizeinBytes = 1514;
  constexpr int kBytesToBits = 8;

  // Get egress port NC1 queue speed in bits per second.
  ASSIGN_OR_RETURN(const int64_t out_queue_pir,
                   GetQueuePir(sut_out_port, kNc1QueueName, *gnmi_stub_));
  LOG(INFO) << "SUT out port: " << sut_out_port << " Queue: " << kNc1QueueName;
  LOG(INFO) << "Egress queue pir (bits/second): " << out_queue_pir;

  const double frame_rate_at_line_speed_of_out_queue =
      (double)out_queue_pir / (kDefaultFrameSizeinBytes * kBytesToBits);
  // Set the traffic frame rate to be above the out discards rate threshold.
  const int64_t traffic_frame_rate =
      ceil(frame_rate_at_line_speed_of_out_queue * (1 + out_discard_rate));
  LOG(INFO) << "Traffic rate (bits/second): "
            << traffic_frame_rate * kDefaultFrameSizeinBytes * kBytesToBits;

  // Set up Ixia.
  ASSIGN_OR_RETURN(IxiaSetUpResult ixia_setup_result,
                   SetUpIxiaForOutDiscardTest(
                       ixia_tx_port, ixia_rx_port, *generic_testbed_,
                       kDefaultFrameSizeinBytes, traffic_frame_rate, kNc1Dscp));

  // Clear entries and install entries forwarding all packets to egress port.
  RETURN_IF_ERROR(p4_runtime::ClearEntities(*sut_p4_session_));
  RETURN_IF_ERROR(sai::EntryBuilder()
                      .AddEntriesForwardingIpPacketsToGivenPort(
                          sut_out_port_id, sai::IpVersion::kIpv4And6)
                      .LogPdEntries()
                      .InstallDedupedEntities(*sut_p4_session_));

  // Read some initial counters via GNMI from the SUT.
  ASSIGN_OR_RETURN(
      const uint64_t initial_port_out_pkts,
      GetInterfaceCounter("out-pkts", sut_out_port, gnmi_stub_.get()));
  ASSIGN_OR_RETURN(
      const uint64_t initial_port_out_discards,
      GetInterfaceCounter("out-discards", sut_out_port, gnmi_stub_.get()));
  ASSIGN_OR_RETURN(BlackholeSwitchCounters initial_blackhole_switch_counters,
                   GetBlackholeSwitchCounters(*gnmi_stub_));
  ASSIGN_OR_RETURN(BlackholePortCounters initial_blackhole_port_counters,
                   GetBlackholePortCounters(sut_out_port, *gnmi_stub_));
  ASSIGN_OR_RETURN(
      const uint64_t initial_queue_dropped_packet_events,
      GetCongestionQueueCounter(sut_out_port, kNc1QueueName, *gnmi_stub_));
  ASSIGN_OR_RETURN(const uint64_t initial_switch_congestion_events,
                   GetCongestionSwitchCounter(*gnmi_stub_));

  RETURN_IF_ERROR(ixia::StartTraffic(ixia_setup_result.traffic_ref,
                                     ixia_setup_result.topology_ref,
                                     *generic_testbed_));

  absl::SleepFor(traffic_duration);

  RETURN_IF_ERROR(
      ixia::StopTraffic(ixia_setup_result.traffic_ref, *generic_testbed_));

  ASSIGN_OR_RETURN(
      const ixia::TrafficItemStats ixia_traffic_stats,
      ixia::GetTrafficItemStats(ixia_setup_result.topology_ref,
                                kOutDiscardTestTrafficName, *generic_testbed_));
  const int64_t observed_traffic_rate =
      ixia::BytesPerSecondReceived(ixia_traffic_stats);
  LOG(INFO) << "Observed traffic rate (bits/second): "
            << observed_traffic_rate * kBytesToBits;

  // Re-read the same counters via GNMI from the SUT.
  ASSIGN_OR_RETURN(
      const uint64_t final_port_out_pkts,
      GetInterfaceCounter("out-pkts", sut_out_port, gnmi_stub_.get()));
  ASSIGN_OR_RETURN(
      const uint64_t final_port_out_discards,
      GetInterfaceCounter("out-discards", sut_out_port, gnmi_stub_.get()));
  ASSIGN_OR_RETURN(BlackholeSwitchCounters final_blackhole_switch_counters,
                   GetBlackholeSwitchCounters(*gnmi_stub_));
  ASSIGN_OR_RETURN(BlackholePortCounters final_blackhole_port_counters,
                   GetBlackholePortCounters(sut_out_port, *gnmi_stub_));
  ASSIGN_OR_RETURN(
      const uint64_t final_queue_dropped_packet_events,
      GetCongestionQueueCounter(sut_out_port, kNc1QueueName, *gnmi_stub_));
  ASSIGN_OR_RETURN(const uint64_t final_switch_congestion_events,
                   GetCongestionSwitchCounter(*gnmi_stub_));

  // Compute the change for each counter.
  const uint64_t port_out_pkts_delta =
      final_port_out_pkts - initial_port_out_pkts;
  const uint64_t port_out_discards_delta =
      final_port_out_discards - initial_port_out_discards;
  BlackholeSwitchCounters blackhole_switch_delta =
      final_blackhole_switch_counters - initial_blackhole_switch_counters;
  BlackholePortCounters blackhole_port_delta =
      final_blackhole_port_counters - initial_blackhole_port_counters;
  const uint64_t queue_dropped_packet_events_delta =
      final_queue_dropped_packet_events - initial_queue_dropped_packet_events;
  const uint64_t switch_congestion_events_delta =
      final_switch_congestion_events - initial_switch_congestion_events;

  return OutDiscardCounters{
      .port_out_packets = port_out_pkts_delta,
      .port_out_discard_packets = port_out_discards_delta,
      .port_blackhole_out_discard_events =
          blackhole_port_delta.out_discard_events,
      .switch_blackhole_out_discard_events =
          blackhole_switch_delta.out_discard_events,
      // Sometimes fec_not_correctable_events occur which the test can't
      // control, so subtract those from the switch blackhole counter.
      .switch_blackhole_events =
          blackhole_switch_delta.blackhole_events -
          blackhole_switch_delta.fec_not_correctable_events,
      .queue_dropped_packet_events = queue_dropped_packet_events_delta,
      .switch_congestion_events = switch_congestion_events_delta,
  };
}

}  // namespace pins_test
