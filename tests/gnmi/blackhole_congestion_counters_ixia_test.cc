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

#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"  // NOLINT: Need to add status_matchers.h for using `ASSERT_OK` in upstream code.
#include "gutil/testing.h"
#include "include/nlohmann/json.hpp"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/ixia_helper.h"
#include "lib/utils/generic_testbed_utils.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/generic_testbed_fixture.h"
#include "thinkit/proto/generic_testbed.pb.h"
#include "thinkit/switch.h"

namespace pins_test {

using ::nlohmann::json;

void BlackholeCongestionCountersIxiaTestFixture::SetUp() {
  thinkit::GenericTestbedFixture<>::SetUp();
  // Pick a testbed with an Ixia Traffic Generator. A SUT is assumed.
  thinkit::TestRequirements requirements =
      gutil::ParseProtoOrDie<thinkit::TestRequirements>(
          R"pb(interface_requirements {
                 count: 1
                 interface_mode: TRAFFIC_GENERATOR
               })pb");

  ASSERT_OK_AND_ASSIGN(generic_testbed_,
                       GetTestbedWithRequirements(requirements));

  // Hook up to gNMI.
  ASSERT_OK_AND_ASSIGN(gnmi_stub_, generic_testbed_->Sut().CreateGnmiStub());

  ASSERT_OK_AND_ASSIGN(
      traffic_generator_links_,
      GetUpLinks(GetAllTrafficGeneratorLinks, *generic_testbed_));
  ASSERT_FALSE(traffic_generator_links_.empty()) << "Ixia links are not ready";
}

struct InFcsErrorTestIxiaSetUpResult {
  // Ixia reference URL to topology.
  std::string topology_ref;
  // Ixia reference URL to traffic.
  std::string traffic_ref;
};

absl::StatusOr<InFcsErrorTestIxiaSetUpResult> SetUpIxiaForInFcsErrorTest(
    absl::string_view ixia_interface, thinkit::GenericTestbed &generic_testbed,
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

  return InFcsErrorTestIxiaSetUpResult{topology_ref, traffic_ref};
}

absl::StatusOr<InErrorCounters>
BlackholeCongestionCountersIxiaTestFixture::TriggerInFcsErrors(
    int frame_rate_per_second, int frame_count) {
  const std::string ixia_interface = traffic_generator_links_[0].peer_interface;
  const std::string sut_interface = traffic_generator_links_[0].sut_interface;

  ASSIGN_OR_RETURN(
      InFcsErrorTestIxiaSetUpResult ixia_setup_result,
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

TEST_P(BlackholeCongestionCountersIxiaTestFixture,
       TestInFcsErrorsAboveThreshIncrementBlackholeCounters) {
  constexpr int kInFcsErrorAboveThreshFramesPerSecond = 15;
  constexpr int kInFcsErrorAboveThreshFramesDurationSeconds = 10;
  constexpr int kInFcsErrorAboveThreshFrameCount =
      kInFcsErrorAboveThreshFramesPerSecond *
      kInFcsErrorAboveThreshFramesDurationSeconds;

  // TODO: Connect to TestTracker for test status

  ASSERT_OK_AND_ASSIGN(InErrorCounters in_fcs_error_counters_delta,
                       TriggerInFcsErrors(kInFcsErrorAboveThreshFramesPerSecond,
                                          kInFcsErrorAboveThreshFrameCount));

  // Check the changes are as expected.
  EXPECT_EQ(in_fcs_error_counters_delta.port_in_error_packets,
            kInFcsErrorAboveThreshFrameCount);
  EXPECT_GT(in_fcs_error_counters_delta.port_blackhole_in_error_events, 0);
  EXPECT_GT(in_fcs_error_counters_delta.switch_blackhole_in_error_events, 0);
  EXPECT_GT(in_fcs_error_counters_delta.switch_blackhole_events, 0);
  EXPECT_EQ(in_fcs_error_counters_delta.port_blackhole_in_error_events,
            in_fcs_error_counters_delta.switch_blackhole_events);
}

TEST_P(BlackholeCongestionCountersIxiaTestFixture,
       TestInFcsErrorsBelowThreshNotIncrementBlackholeCounters) {
  constexpr int kInFcsErrorBelowThreshFramesPerSecond = 5;
  constexpr int kInFcsErrorBelowThreshFramesDurationSeconds = 10;
  constexpr int kInFcsErrorBelowThreshFrameCount =
      kInFcsErrorBelowThreshFramesPerSecond *
      kInFcsErrorBelowThreshFramesDurationSeconds;

  // TODO: Connect to TestTracker for test status

  ASSERT_OK_AND_ASSIGN(InErrorCounters in_fcs_error_counters_delta,
                       TriggerInFcsErrors(kInFcsErrorBelowThreshFramesPerSecond,
                                          kInFcsErrorBelowThreshFrameCount));

  // Check the changes are as expected.
  EXPECT_EQ(in_fcs_error_counters_delta.port_in_error_packets,
            kInFcsErrorBelowThreshFrameCount);
  EXPECT_EQ(in_fcs_error_counters_delta.port_blackhole_in_error_events, 0);
  EXPECT_EQ(in_fcs_error_counters_delta.switch_blackhole_in_error_events, 0);
  EXPECT_EQ(in_fcs_error_counters_delta.switch_blackhole_events, 0);
}

}  // namespace pins_test
