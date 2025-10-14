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
#include <utility>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"  // NOLINT: Need to add status_matchers.h for using `ASSERT_OK` in upstream code.
#include "gutil/testing.h"
#include "tests/gnmi/util.h"
#include "tests/integration/system/nsf/interfaces/image_config_params.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "tests/integration/system/nsf/util.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/proto/generic_testbed.pb.h"
#include "thinkit/switch.h"

namespace pins_test {
namespace {

constexpr double kLinkFlapThresholdPostNsfReboot = 0.05;

}  // namespace

TEST_P(NsfLinkFlapTestFixture, NsfLinkFlapTest) {
  LOG(INFO) << "Get testbed requirements.";
  thinkit::TestRequirements requirements =
      gutil::ParseProtoOrDie<thinkit::TestRequirements>(
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
    if (info.interface_modes.contains(thinkit::CONTROL_INTERFACE)) {
      host_interface_infos[interface] = info;
    } else {
      LOG(WARNING)
          << "Skipping the interface "
          << interface << " as interface mode is not CONTROL_INTERFACE.";
    }
  }
  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, generic_testbed->Sut().CreateGnmiStub());

  LOG(INFO) << "Flap links before NSF Reboot.";
  // Capturing the current time to compare the overall time needed for link
  // flap.
  const absl::Time pre_nsf_link_flap_start_time = absl::Now();
  for (const auto& [sut_interface, host_interface_info] :
       host_interface_infos) {
    EXPECT_OK(FlapLink(*gnmi_stub, *generic_testbed, sut_interface,
                       host_interface_info));
  }
  const absl::Duration pre_nsf_link_flap_time =
      absl::Now() - pre_nsf_link_flap_start_time;
  LOG(INFO) << "Pre-NSF Link Flap Time: " << pre_nsf_link_flap_time;
  LOG(INFO) << "Initiating NSF reboot";
  ASSERT_OK(DoNsfRebootAndWaitForSwitchReady(generic_testbed.get(),
                                             *GetParam().ssh_client));
  LOG(INFO) << "Flap links after NSF Reboot.";
  const absl::Time post_nsf_link_flap_start_time = absl::Now();
  for (const auto& [sut_interface, host_interface_info] :
       host_interface_infos) {
    EXPECT_OK(FlapLink(*gnmi_stub, *generic_testbed, sut_interface,
                       host_interface_info));
  }
  const absl::Duration post_nsf_link_flap_time =
      absl::Now() - post_nsf_link_flap_start_time;
  LOG(INFO) << "Post-NSF Link Flap Time: " << post_nsf_link_flap_time;

  if (post_nsf_link_flap_time > pre_nsf_link_flap_time) {
    double link_flap_time_increase =
        absl::FDivDuration((post_nsf_link_flap_time - pre_nsf_link_flap_time),
                           pre_nsf_link_flap_time);
    EXPECT_LE(link_flap_time_increase, kLinkFlapThresholdPostNsfReboot)
        << "Link flap time has increased post NSF";
  }
}

}  // namespace pins_test
