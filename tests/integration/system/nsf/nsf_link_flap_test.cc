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
#include "tests/integration/system/nsf/nsf_link_flap_test.h"

#include <memory>
#include <string>
#include <thread>
#include <utility>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"  // NOLINT: Need to add status_matchers.h for using `ASSERT_OK` in upstream code.
#include "gutil/gutil/testing.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "tests/gnmi/util.h"
#include "tests/integration/system/nsf/interfaces/flow_programmer.h"
#include "tests/integration/system/nsf/interfaces/image_config_params.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "tests/integration/system/nsf/util.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/proto/generic_testbed.pb.h"
#include "thinkit/switch.h"

namespace pins_test {
namespace {

constexpr absl::Duration kLinkFlapTimeout = absl::Seconds(90);

// Flaps all the links in parallel and returns the total time taken to flap all
// the links.
absl::StatusOr<absl::Duration> FlapAllLinksAndReportDuration(
    gnmi::gNMI::StubInterface& gnmi_stub,
    thinkit::GenericTestbed& generic_testbed,
    absl::flat_hash_map<std::string, thinkit::InterfaceInfo>
         host_interface_infos,
    bool is_ixia_testbed) {
  // Create a flat_hash_map to store the link flap results for all the links
  // where the key is the SUT link name and the value is the link flap
  // status.
  absl::flat_hash_map<std::string, absl::Status> link_flap_status;

  // Initialize the link_flap_status with all the links. This is to avoid
  // re-hashing and thus avoid the race condition and link_flap_status can be
  // used for concurrent writes.
  for (const auto& [sut_interface, host_interface_info] :
       host_interface_infos) {
    link_flap_status.emplace(sut_interface, absl::Status());
  }

  // Create a vector of threads to flap all the links in parallel.
  std::vector<std::thread> link_threads;

  // Start the link flap for all the interfaces in parallel.
  const absl::Time link_flap_start_time = absl::Now();
  for (const auto& [sut_interface, host_interface_info] :
       host_interface_infos) {
    // Flap all the links in parallel.
    std::thread thread([&gnmi_stub, &generic_testbed, &sut_interface,
                        &host_interface_info, &link_flap_status,
                        &is_ixia_testbed] {
      link_flap_status[sut_interface] =
          FlapLink(gnmi_stub, generic_testbed, sut_interface,
                   host_interface_info, is_ixia_testbed);
    });
    link_threads.push_back(std::move(thread));
  }

  // Wait for all the threads to complete.
  for (std::thread& thread : link_threads) {
    thread.join();
  }

  // Calculate the total time taken to flap all the links.
  const absl::Duration link_flap_duration = absl::Now() - link_flap_start_time;

  // Check if any link flaps have failed.
  absl::Status overall_status;
  for (const auto& [sut_interface, status] : link_flap_status) {
    if (status.ok()) continue;
    absl::Status annotated_status = gutil::StatusBuilder(status).SetPrepend()
                                    << "Failed to flap link: " << sut_interface
                                    << " due to error " << status << ": ";
    if (overall_status.ok()) {
      overall_status.Update(annotated_status);
    } else {
      overall_status = gutil::StatusBuilder(overall_status).SetAppend()
                       << "\n"
                       << annotated_status.ToString();
    }
  }

  // Return the overall status if any link flap has failed.
  if (!overall_status.ok()) {
    return overall_status;
  }

  // Return the total time taken to flap all the links.
  LOG(INFO) << "Link flap duration: " << link_flap_duration;
  return link_flap_duration;
}
}  // namespace

TEST_P(NsfLinkFlapTestFixture, NsfLinkFlapTest) {
  LOG(INFO) << "Get testbed requirements.";
  thinkit::TestRequirements requirements =
      GetParam().is_ixia_testbed
          ? gutil::ParseProtoOrDie<thinkit::TestRequirements>(
                R"pb(interface_requirements {
                       count: 1
                       interface_mode: TRAFFIC_GENERATOR
                     })pb")
          : gutil::ParseProtoOrDie<thinkit::TestRequirements>(
                R"pb(interface_requirements {
                       count: 1
                       interface_mode: CONTROL_INTERFACE
                     })pb");
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<thinkit::GenericTestbed> generic_testbed,
                       GetTestbedWithRequirements(requirements));

  LOG(INFO) << "Get interface info of all interfaces in SUT.";
  // TODO: Replace below code with GetAllControlLinks once the
  // support for peer device index is added.
  absl::flat_hash_map<std::string, thinkit::InterfaceInfo> interface_info =
      generic_testbed->GetSutInterfaceInfo();
  absl::flat_hash_map<std::string, thinkit::InterfaceInfo> host_interface_infos;
  for (const auto& [interface, info] : interface_info) {
    LOG(INFO) << "Get sut interface info: " << interface;
    if (info.peer_interface_name.empty()) {
      LOG(WARNING) << "Skipping the interface "
                   << interface << " as peer interface is missing."
                   << " Peer MAC Address: " << info.peer_mac_address
                   << " Peer IPv6 Address: " << info.peer_ipv6_address
                   << " Peer interface name: " << info.peer_interface_name
                   << " Peer device index: " << info.peer_device_index;
      continue;
    }
    if (info.interface_modes.contains(thinkit::CONTROL_INTERFACE) ||
        info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR)) {
      host_interface_infos[interface] = info;
    } else {
      LOG(WARNING) << "Skipping the interface " << interface
                   << " as interface mode is neither CONTROL_INTERFACE nor "
                      "TRAFFIC_GENERATOR.";
    }
  }
  if (host_interface_infos.empty()) {
    GTEST_SKIP() << "No suitable link found in SUT for link flap.";
  }

  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, generic_testbed->Sut().CreateGnmiStub());

  LOG(INFO) << "Flap links before NSF Reboot.";

  // Flap links and report the time taken to flap all the links.
  const absl::StatusOr<absl::Duration> pre_nsf_link_flap_time =
      FlapAllLinksAndReportDuration(*gnmi_stub, *generic_testbed,
                                    host_interface_infos,
                                    GetParam().is_ixia_testbed);
  if (pre_nsf_link_flap_time.ok()) {
    LOG(INFO) << "Pre-NSF Link Flap Time: " << pre_nsf_link_flap_time.value();
    EXPECT_LE(pre_nsf_link_flap_time.value(), kLinkFlapTimeout)
        << "Pre-NSF Link Flap Time: " << pre_nsf_link_flap_time.value()
        << " is greater than the maximum expected time: " << kLinkFlapTimeout;
  } else {
    // Fail the test if the link flap before NSF fails.
    ADD_FAILURE() << pre_nsf_link_flap_time.status().message();
  }
  LOG(INFO) << "Initiating NSF reboot";
  ASSERT_OK(DoNsfRebootAndWaitForSwitchReadyOrRecover(generic_testbed.get(),
                                                      *GetParam().ssh_client));
  LOG(INFO) << "Flap links after NSF Reboot.";
  // Flap links and report the time taken to flap all the links.
  const absl::StatusOr<absl::Duration> post_nsf_link_flap_time =
      FlapAllLinksAndReportDuration(*gnmi_stub, *generic_testbed,
                                    host_interface_infos,
                                    GetParam().is_ixia_testbed);
  if (post_nsf_link_flap_time.ok()) {
    LOG(INFO) << "Post-NSF Link Flap Time: " << post_nsf_link_flap_time.value();
    EXPECT_LE(post_nsf_link_flap_time.value(), kLinkFlapTimeout)
        << "Post-NSF Link Flap Time: " << post_nsf_link_flap_time.value()
        << " is greater than the maximum expected time: " << kLinkFlapTimeout;
  } else {
    // Fail the test if the link flap after NSF fails.
    ADD_FAILURE() << post_nsf_link_flap_time.status().message();
  }
}

}  // namespace pins_test
