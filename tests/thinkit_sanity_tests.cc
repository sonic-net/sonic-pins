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

#include "absl/status/statusor.h"
#include "absl/time/time.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "include/nlohmann/json.hpp"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

namespace pins_test {
namespace {

using ::nlohmann::json;
using ::testing::Eq;

}  // namespace

constexpr char kOpenconfigStr[] = "openconfig";
constexpr char kStateUp[] = "UP";
constexpr char kInterfaces[] = "interfaces";

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

void TestGnmiCheckSpecificInterfaceStateOperation(thinkit::Switch& sut,
                                                  std::string if_name) {
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());
  gnmi::GetRequest req;
  req.set_type(gnmi::GetRequest_DataType_STATE);
  req.mutable_prefix()->set_origin(kOpenconfigStr);
  gnmi::Path* path = req.add_path();
  path->add_elem()->set_name(kInterfaces);
  auto elem = path->add_elem();
  elem->set_name("interface");
  (*elem->mutable_key())["name"] = if_name;
  path->add_elem()->set_name("state");
  path->add_elem()->set_name("oper-status");

  req.set_encoding(::gnmi::Encoding::JSON_IETF);
  LOG(INFO) << "Sending GET request: " << req.ShortDebugString();

  gnmi::GetResponse resp;
  grpc::ClientContext context;
  ASSERT_OK(sut_gnmi_stub->Get(&context, req, &resp));
  LOG(INFO) << "Received GET response: " << resp.ShortDebugString();
  ASSERT_EQ(resp.notification_size(), 1);
  ASSERT_EQ(resp.notification(0).update_size(), 1);
  const std::string val_str =
      resp.notification(0).update(0).val().json_ietf_val();
  auto const resp_json = json::parse(val_str);
  auto const oper_status = resp_json.find("openconfig-interfaces:oper-status");
  ASSERT_NE(oper_status, resp_json.end());
  EXPECT_THAT(oper_status->dump(), testing::HasSubstr(kStateUp));
}

void TestGnmiCheckInterfaceStateOperation(thinkit::Switch& sut) {
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());
  gnmi::GetRequest req;
  req.mutable_prefix()->set_origin(kOpenconfigStr);
  req.set_type(gnmi::GetRequest_DataType_STATE);
  gnmi::Path* path = req.add_path();
  path->add_elem()->set_name(kInterfaces);
  req.set_encoding(::gnmi::Encoding::JSON_IETF);
  LOG(INFO) << "Sending GET request: " << req.ShortDebugString();

  gnmi::GetResponse resp;
  grpc::ClientContext context;
  ASSERT_OK(sut_gnmi_stub->Get(&context, req, &resp));
  LOG(INFO) << "Received GET response: " << resp.ShortDebugString();
  ASSERT_EQ(resp.notification_size(), 1);
  ASSERT_EQ(resp.notification(0).update_size(), 1);
  auto const resp_json =
      json::parse(resp.notification(0).update(0).val().json_ietf_val());
  auto const oc_intf_json = resp_json.find("openconfig-interfaces:interfaces");
  ASSERT_NE(oc_intf_json, resp_json.end());
  auto const oc_intf_list_json = oc_intf_json->find("interface");
  ASSERT_NE(oc_intf_list_json, oc_intf_json->end());
  for (auto const& element : oc_intf_list_json->items()) {
    auto const element_state_json = element.value().find("state");
    ASSERT_NE(element_state_json, element.value().end());

    auto const element_status_json = element_state_json->find("oper-status");
    ASSERT_NE(element_status_json, element_state_json->end());

    EXPECT_THAT(element_status_json->dump(), testing::HasSubstr(kStateUp));
  }
}
void TestGnmiGetInterfaceOperation(thinkit::Switch& sut) {
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());
  gnmi::GetRequest req;
  req.mutable_prefix()->set_origin(kOpenconfigStr);
  req.set_type(gnmi::GetRequest_DataType_ALL);
  gnmi::Path* path = req.add_path();
  path->add_elem()->set_name(kInterfaces);
  req.set_encoding(::gnmi::Encoding::JSON_IETF);
  LOG(INFO) << "Sending GET request: " << req.ShortDebugString();
  gnmi::GetResponse resp;
  grpc::ClientContext context;
  ASSERT_OK(sut_gnmi_stub->Get(&context, req, &resp));
  LOG(INFO) << "Received GET response: " << resp.ShortDebugString();
}

void TestGnmiGetAllOperation(thinkit::Switch& sut) {
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());
  gnmi::GetRequest req;
  req.mutable_prefix()->set_origin(kOpenconfigStr);
  req.set_type(gnmi::GetRequest_DataType_ALL);
  req.set_encoding(gnmi::Encoding::JSON_IETF);
  LOG(INFO) << "Sending GET request: " << req.ShortDebugString();
  gnmi::GetResponse resp;
  grpc::ClientContext context;
  ASSERT_OK(sut_gnmi_stub->Get(&context, req, &resp));
  LOG(INFO) << "Received GET response: " << resp.ShortDebugString();
}

}  // namespace pins_test
