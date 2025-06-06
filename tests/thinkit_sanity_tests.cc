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

#include "tests/thinkit_sanity_tests.h"

#include <cstdint>
#include <cstdlib>
#include <map>
#include <memory>
#include <string>
#include <utility>
#include <valarray>

#include "absl/container/flat_hash_set.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/flags/flag.h"
#include "gmock/gmock.h"
#include "grpcpp/impl/codegen/client_context.h"
#include "grpcpp/support/status.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "include/nlohmann/json.hpp"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/utils/constants.h"
#include "lib/validator/validator_lib.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "proto/gnmi/gnmi.pb.h"
#include "system/system.grpc.pb.h"
#include "system/system.pb.h"
#include "tests/thinkit_util.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

// Flag to bypass the gNMI call to get the boottime
// TODO(PINS): To be removed when get boottime is supported
ABSL_FLAG(bool, gnmi_boottime_support, true, "gNMI get boot time supported");

namespace pins_test {
namespace {

using ::nlohmann::json;
using ::testing::HasSubstr;

constexpr int kEpochMarginalError = 2;
constexpr absl::Duration kColdRebootWaitForDownTime = absl::Seconds(75);
constexpr char kV3ReleaseConfigBlob[] = R"({
   "openconfig-platform:components" : {
      "component" : [
         {
           "name" : "integrated_circuit0",
           "config" : {
               "name" : "integrated_circuit0"
           },
           "integrated-circuit" : {
               "config" : {
                  "node-id" : "183930889"
               }
            }
         }
      ]
   },
   "openconfig-system:system" : {
       "config" : {
           "config-meta-data" : "v4"
       }
   },
   "openconfig-interfaces:interfaces" : {
      "interface" : [
         {
            "name": "Ethernet0",
            "config" : {
               "name" : "Ethernet0",
               "enabled" : true,
               "id": 1
            },
            "ethernet" : {
               "config" : {
                  "port-speed" : "SPEED_400GB"
               }
            }
         },
         {
            "name": "Ethernet8",
            "config" : {
               "name" : "Ethernet8",
               "enabled" : true,
               "id": 2
            },
            "ethernet" : {
               "config" : {
                  "port-speed" : "SPEED_200GB"
               }
            }
         },
         {
            "name": "Ethernet12",
            "config" : {
               "name" : "Ethernet12",
               "enabled" : true,
               "id": 518
            },
            "ethernet" : {
               "config" : {
                  "port-speed" : "SPEED_200GB"
               }
            }
         }
      ]
   }
})";

}  // namespace

void TestSSHCommand(thinkit::SSHClient& ssh_client, thinkit::Switch& sut) {
  EXPECT_OK(SSHable(sut, ssh_client));
}

void TestP4Session(thinkit::Switch& sut) {
  // Before a connection to P4RT can be established we need to configure the
  // device ID.
  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, sut.CreateGnmiStub());
  ASSERT_OK(pins_test::SetDeviceId(*gnmi_stub, sut.DeviceId()));
  ASSERT_OK_AND_ASSIGN(auto device_id, pins_test::GetDeviceId(*gnmi_stub));
  EXPECT_EQ(device_id, sut.DeviceId());
  EXPECT_OK(P4rtAble(sut));
}

void TestGnmiGetInterfaceOperation(thinkit::Switch& sut) {
  EXPECT_OK(GnmiAble(sut));
}

void TestGnmiGetAllOperation(thinkit::Switch& sut) {
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(gnmi::GetRequest req,
                       BuildGnmiGetRequest("", gnmi::GetRequest::ALL));
  LOG(INFO) << "Sending GET request: " << req.ShortDebugString();
  gnmi::GetResponse resp;
  grpc::ClientContext context;
  ASSERT_OK(sut_gnmi_stub->Get(&context, req, &resp));
  LOG(INFO) << "Received GET response: " << resp.ShortDebugString();
}

void TestGnmiCheckAlarms(thinkit::MirrorTestbed& testbed) {
  EXPECT_OK(NoAlarms(testbed.Sut()));
}

// This test sets the config blob and verifies corresponding state paths.
void TestGnmiConfigBlobSet(thinkit::Switch& sut) {
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(
      gnmi::SetRequest req,
      BuildGnmiSetRequest("", GnmiSetType::kUpdate, kV3ReleaseConfigBlob));
  LOG(INFO) << "Sending SET request: " << req.ShortDebugString();
  gnmi::SetResponse resp;
  grpc::ClientContext context;
  ASSERT_OK(sut_gnmi_stub->Set(&context, req, &resp));
  LOG(INFO) << "Received SET response: " << resp.ShortDebugString();

  auto config_json = json::parse(kV3ReleaseConfigBlob);
  const auto components_json =
      config_json.find("openconfig-platform:components");
  ASSERT_NE(components_json, config_json.end());
  const auto component_list_json = components_json->find("component");
  ASSERT_NE(component_list_json, components_json->end());

  std::map<std::string, std::string> ic_nodeid_map;
  for (auto const& element : component_list_json->items()) {
    auto const element_name_json = element.value().find("name");
    const auto element_integrated_circuit_json =
        element.value().find("integrated-circuit");
    const auto element_ic_config_json =
        element_integrated_circuit_json.value().find("config");
    const auto element_node_json =
        element_ic_config_json.value().find("node-id");
    // Converting "integrated_circuit0" to integrated_circuit0
    ic_nodeid_map[element_name_json->dump().substr(
        1, element_name_json->dump().size() - 2)] =
        element_node_json->dump().substr(1,
                                         element_node_json->dump().size() - 2);
  }
  //  Only one integrated-circuit configuration is present in config blob.
  ASSERT_EQ(ic_nodeid_map.size(), 1);
  gnmi::GetRequest get_req;
  gnmi::GetResponse get_resp;
  grpc::ClientContext get_context;
  std::string component_req =
      absl::StrCat("components/component[name=", ic_nodeid_map.begin()->first,
                   "]/integrated-circuit/state");
  ASSERT_OK_AND_ASSIGN(
      get_req, BuildGnmiGetRequest(component_req, gnmi::GetRequest::STATE));
  LOG(INFO) << "Sending GET request: " << get_req.ShortDebugString();

  ASSERT_OK(sut_gnmi_stub->Get(&get_context, get_req, &get_resp));
  LOG(INFO) << "Received GET response: " << get_resp.ShortDebugString();
  ASSERT_OK_AND_ASSIGN(
      std::string nodeid_respose,
      ParseGnmiGetResponse(get_resp, "openconfig-platform:state"));
  EXPECT_THAT(nodeid_respose, HasSubstr(ic_nodeid_map.begin()->second));

  std::map<std::string, std::string> intf_speed_map;
  const auto interfaces_json =
      config_json.find("openconfig-interfaces:interfaces");
  const auto interface_list_json = interfaces_json->find("interface");

  for (auto const& element : interface_list_json->items()) {
    auto const element_name_json = element.value().find("name");
    const auto element_ethernet_json = element.value().find("ethernet");
    const auto element_ethernet_config_json =
        element_ethernet_json.value().find("config");
    const auto element_port_speed_json =
        element_ethernet_config_json.value().find("port-speed");
    intf_speed_map[element_name_json->dump()] =
        element_port_speed_json->dump().substr(
            1, element_port_speed_json->dump().size() - 2);
  }

  if (intf_speed_map.empty()) {
    return;
  }
  ASSERT_OK_AND_ASSIGN(
      get_req, BuildGnmiGetRequest(kInterfaces, gnmi::GetRequest::STATE));
  LOG(INFO) << "Sending GET request: " << get_req.ShortDebugString();

  grpc::ClientContext get_state_context;
  ASSERT_OK(sut_gnmi_stub->Get(&get_state_context, get_req, &get_resp));
  LOG(INFO) << "Received GET response: " << get_resp.ShortDebugString();
  ASSERT_EQ(get_resp.notification_size(), 1);
  ASSERT_EQ(get_resp.notification(0).update_size(), 1);
  auto intf_state_json =
      json::parse(get_resp.notification(0).update(0).val().json_ietf_val());
  const auto oc_intf_json =
      intf_state_json.find("openconfig-interfaces:interfaces");
  ASSERT_NE(oc_intf_json, intf_state_json.end());
  const auto oc_intf_list_json = oc_intf_json->find("interface");
  ASSERT_NE(oc_intf_list_json, oc_intf_json->end());
  for (auto const& element : oc_intf_list_json->items()) {
    auto const element_name_json = element.value().find("name");
    ASSERT_NE(element_name_json, element.value().end());
    auto if_speed_elem = intf_speed_map.find(element_name_json->dump());
    if (if_speed_elem == intf_speed_map.end()) {
      continue;
    }
    const auto element_ethernet_json =
        element.value().find("openconfig-if-ethernet:ethernet");
    ASSERT_NE(element_ethernet_json, element.value().end())
        << element.value().find("name")->dump();
    const auto element_interface_state_json =
        element_ethernet_json->find("state");
    ASSERT_NE(element_interface_state_json, element_ethernet_json->end())
        << element.value().find("name")->dump();
    const auto element_speed_json =
        element_interface_state_json->find("port-speed");
    ASSERT_NE(element_speed_json, element_interface_state_json->end())
        << element.value().find("name")->dump();
    EXPECT_THAT(element_speed_json->dump(), HasSubstr(if_speed_elem->second))
        << element_interface_state_json->find("name")->dump();
  }
}

//  Returns last boot time of SUT.
absl::StatusOr<uint64_t> GetGnmiSystemBootTime(
    thinkit::Switch& sut, gnmi::gNMI::StubInterface* sut_gnmi_stub) {

  // If gNMI does not support get boot time, use this flag to return
  // a dummy value
  // TODO(PINS): To be removed when get boottime is supported
  if (!absl::GetFlag(FLAGS_gnmi_boottime_support)) {
    return 0x01;
  }

  ASSIGN_OR_RETURN(
      gnmi::GetRequest request,
      BuildGnmiGetRequest("system/state/boot-time", gnmi::GetRequest::STATE));
  LOG(INFO) << "Sending GET request: " << request.ShortDebugString();
  gnmi::GetResponse response;
  grpc::ClientContext context;
  EXPECT_OK(sut_gnmi_stub->Get(&context, request, &response));
  LOG(INFO) << "Received GET response: " << response.ShortDebugString();

  ASSIGN_OR_RETURN(
      std::string parsed_str,
      ParseGnmiGetResponse(response, "openconfig-system:boot-time"));
  // Remove characters <"">  in the parsed string.
  std::string boot_time_string = parsed_str.substr(1, parsed_str.size() - 2);
  uint64_t boot_time;
  if (!absl::SimpleAtoi(boot_time_string, &boot_time)) {
    return gutil::InternalErrorBuilder().LogError()
           << absl::StrCat("SimpleAtoi Error while parsing ")
           << boot_time_string;
  }
  LOG(INFO) << "Boot Time: " << boot_time;
  return boot_time;
}

void TestGnoiSystemColdReboot(thinkit::Switch& sut,
                              absl::Span<const std::string> interfaces) {
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(uint64_t first_boot_time,
                       GetGnmiSystemBootTime(sut, sut_gnmi_stub.get()));

  ASSERT_OK_AND_ASSIGN(auto sut_gnoi_system_stub, sut.CreateGnoiSystemStub());
  gnoi::system::RebootRequest request;
  request.set_method(gnoi::system::RebootMethod::COLD);
  request.set_message("Testing Purpose");
  gnoi::system::RebootResponse response;
  grpc::ClientContext context;
  VLOG(1) << "Sending Reboot request: " << request.ShortDebugString();
  ASSERT_OK(sut_gnoi_system_stub->Reboot(&context, request, &response));
  VLOG(1) << "Received Reboot response: " << response.ShortDebugString();

  absl::Time start_time = absl::Now();
  bool system_down = false;

  // Wait for system to become unreachable via ping - as that's the last thing
  // that goes down.
  while (absl::Now() < (start_time + kColdRebootWaitForDownTime)) {
    if (Pingable(sut, absl::Seconds(1)) != absl::OkStatus()) {
      LOG(INFO) << "The switch is not pingable at "
                << absl::FormatTime("%Y-%m-%d %H:%M:%S", absl::Now(),
                                    absl::LocalTimeZone())
                << ", which is before the timeout threshold at: "
                << absl::FormatTime("%Y-%m-%d %H:%M:%S",
                                    (start_time + kColdRebootWaitForDownTime),
                                    absl::LocalTimeZone());
      system_down = true;
      break;
    }
  }

  // Return failure if system did not go down.
  ASSERT_TRUE(system_down) << "System did not go down in "
                           << kColdRebootWaitForDownTime
                           << ". Reboot triggered timestamp is "
                           << absl::FormatTime("%Y-%m-%d %H:%M:%S", start_time,
                                               absl::LocalTimeZone());

  // Wait for system to become reachable over gNOI.
  start_time = absl::Now();
  absl::Status status;
  const absl::Duration kColdRebootWaitForUpTime = GetColdRebootWaitForUpTime();
  while (absl::Now() < (start_time + kColdRebootWaitForUpTime)) {
    status = SwitchReady(sut, interfaces);
    if (status.ok()) {
      LOG(INFO) << "The switch is ready at "
                << absl::FormatTime("%Y-%m-%d %H:%M:%S", absl::Now(),
                                    absl::LocalTimeZone())
                << ", which is before the timeout threshold at: "
                << absl::FormatTime("%Y-%m-%d %H:%M:%S",
                                    (start_time + kColdRebootWaitForUpTime),
                                    absl::LocalTimeZone());
      system_down = false;
      break;
    }
  }

  // Return failure if system did not come up.
  ASSERT_FALSE(system_down)
      << "System did not come up in " << kColdRebootWaitForUpTime
      << " with error: " << status << ". Probe activation timestamp is "
      << absl::FormatTime("%Y-%m-%d %H:%M:%S", start_time,
                          absl::LocalTimeZone());

  ASSERT_OK_AND_ASSIGN(uint64_t latest_boot_time,
                       GetGnmiSystemBootTime(sut, sut_gnmi_stub.get()));

  EXPECT_GT((latest_boot_time - first_boot_time), kEpochMarginalError);
}

}  // namespace pins_test
