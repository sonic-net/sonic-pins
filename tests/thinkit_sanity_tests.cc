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

#include <stdint.h>

#include <string>
#include <utility>

#include "absl/container/flat_hash_set.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "lib/gnmi/gnmi_helper.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "include/nlohmann/json.hpp"
#include "tests/thinkit_util.h"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

namespace pins_test {
namespace {

using ::nlohmann::json;
using ::testing::Eq;
using ::testing::HasSubstr;

}  // namespace

constexpr char kMtuJsonVal[] = "{\"mtu\":2000}";

void TestSSHCommand(thinkit::SSHClient& ssh_client, thinkit::Switch& sut) {
  ASSERT_OK_AND_ASSIGN(std::string output,
                       ssh_client.RunCommand(sut.ChassisName(), "echo foo",
                                             absl::ZeroDuration()));
  EXPECT_THAT(output, Eq("foo\n"));
}

void TestP4Session(thinkit::Switch& sut) {
  // TODO: Remove kDeviceId once device ID is set through gNMI in
  // P4RT app.
  static constexpr uint64_t kDeviceId = 183807201;
  ASSERT_OK_AND_ASSIGN(auto sut_p4runtime_stub, sut.CreateP4RuntimeStub());
  EXPECT_OK(
      pdpi::P4RuntimeSession::Create(std::move(sut_p4runtime_stub), kDeviceId));
}

void TestGnmiInterfaceConfigSetMtu(thinkit::Switch& sut,
                                   absl::string_view if_name) {
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());
  std::string if_req =
      absl::StrCat("interfaces/interface[name=", if_name, "]/config/mtu");

  ASSERT_OK_AND_ASSIGN(
      gnmi::SetRequest req,
      BuildGnmiSetRequest(if_req, GnmiSetType::kUpdate, kMtuJsonVal));
  LOG(INFO) << "Sending SET request: " << req.ShortDebugString();
  gnmi::SetResponse resp;
  grpc::ClientContext context;
  ASSERT_OK(sut_gnmi_stub->Set(&context, req, &resp));
  LOG(INFO) << "Received SET response: " << resp.ShortDebugString();

  ASSERT_OK_AND_ASSIGN(gnmi::GetRequest get_req,
                       BuildGnmiGetRequest(if_req, gnmi::GetRequest::CONFIG));
  LOG(INFO) << "Sending GET request: " << get_req.ShortDebugString();
  gnmi::GetResponse get_resp;
  grpc::ClientContext get_context;
  ASSERT_OK(sut_gnmi_stub->Get(&get_context, get_req, &get_resp));
  LOG(INFO) << "Received GET response: " << resp.ShortDebugString();
  ASSERT_OK_AND_ASSIGN(
      std::string mtu_respose,
      ParseGnmiGetResponse(get_resp, "openconfig-interfaces:mtu"));
  LOG(INFO) << "mtu_respose: " << mtu_respose;
  EXPECT_THAT(mtu_respose, HasSubstr("2000"));

  ASSERT_OK_AND_ASSIGN(req, BuildGnmiSetRequest(if_req, GnmiSetType::kDelete));
  LOG(INFO) << "Sending SET request: " << req.ShortDebugString();
  grpc::ClientContext new_set_context;
  ASSERT_OK(sut_gnmi_stub->Set(&new_set_context, req, &resp));
  LOG(INFO) << "Received SET response: " << resp.ShortDebugString();
}

void TestGnmiCheckSpecificInterfaceStateOperation(thinkit::Switch& sut,
                                                  absl::string_view if_name) {
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());
  std::string if_req = absl::StrCat("interfaces/interface[name=", if_name,
                                    "]/state/oper-status");
  ASSERT_OK_AND_ASSIGN(gnmi::GetRequest req,
                       BuildGnmiGetRequest(if_req, gnmi::GetRequest::STATE));
  LOG(INFO) << "Sending GET request: " << req.ShortDebugString();

  gnmi::GetResponse resp;
  grpc::ClientContext context;
  ASSERT_OK(sut_gnmi_stub->Get(&context, req, &resp));
  LOG(INFO) << "Received GET response: " << resp.ShortDebugString();
  ASSERT_OK_AND_ASSIGN(
      std::string oper_response,
      ParseGnmiGetResponse(resp, "openconfig-interfaces:oper-status"));
  LOG(INFO) << "oper_respose: " << oper_response;
  EXPECT_THAT(oper_response, HasSubstr(kStateUp));
}

void TestGnmiCheckInterfaceStateOperation(thinkit::Switch& sut) {
  const absl::flat_hash_set<std::string> k1Ethernet10GBInterfaces = {
      "\"Ethernet256\"", "\"Ethernet260\""};
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(
      gnmi::GetRequest req,
      BuildGnmiGetRequest(kInterfaces, gnmi::GetRequest::STATE));
  LOG(INFO) << "Sending GET request: " << req.ShortDebugString();

  gnmi::GetResponse resp;
  grpc::ClientContext context;
  ASSERT_OK(sut_gnmi_stub->Get(&context, req, &resp));
  LOG(INFO) << "Received GET response: " << resp.ShortDebugString();
  ASSERT_EQ(resp.notification_size(), 1);
  ASSERT_EQ(resp.notification(0).update_size(), 1);
  const auto resp_json =
      json::parse(resp.notification(0).update(0).val().json_ietf_val());
  const auto oc_intf_json = resp_json.find("openconfig-interfaces:interfaces");
  ASSERT_NE(oc_intf_json, resp_json.end());
  const auto oc_intf_list_json = oc_intf_json->find("interface");
  ASSERT_NE(oc_intf_list_json, oc_intf_json->end());
  for (auto const& element : oc_intf_list_json->items()) {
    auto const element_name_json = element.value().find("name");
    ASSERT_NE(element_name_json, element.value().end());
    // TODO : Revert back to interface port-speed check.
    // Arista chassis have 2 additional 10G SFP ports, skipping checks for these
    // ports as they aren't connected.
    if (!k1Ethernet10GBInterfaces.contains(element_name_json->dump())) {
      const auto element_interface_state_json = element.value().find("state");
      ASSERT_NE(element_interface_state_json, element.value().end())
          << element.value().find("name")->dump();

      const auto element_status_json =
          element_interface_state_json->find("oper-status");
      ASSERT_NE(element_status_json, element_interface_state_json->end())
          << element.value().find("name")->dump();

      EXPECT_THAT(element_status_json->dump(), HasSubstr(kStateUp))
          << element_interface_state_json->find("name")->dump();
    }
  }
}
void TestGnmiGetInterfaceOperation(thinkit::Switch& sut) {
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());
  ASSERT_OK_AND_ASSIGN(gnmi::GetRequest req,
                       BuildGnmiGetRequest(kInterfaces, gnmi::GetRequest::ALL));
  LOG(INFO) << "Sending GET request: " << req.ShortDebugString();
  gnmi::GetResponse resp;
  grpc::ClientContext context;
  ASSERT_OK(sut_gnmi_stub->Get(&context, req, &resp));
  LOG(INFO) << "Received GET response: " << resp.ShortDebugString();
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

}  // namespace pins_test
