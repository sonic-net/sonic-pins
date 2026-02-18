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

#include "tests/thinkit_gnmi_subscribe_tests.h"

#include "absl/container/flat_hash_set.h"
#include "absl/log/log.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"
#include "include/nlohmann/json.hpp"
#include "lib/gnmi/gnmi_helper.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "proto/gnmi/gnmi.pb.h"
#include "tests/thinkit_util.h"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

namespace pins_test {

constexpr absl::Duration kSubscribeWaitTime = absl::Seconds(100);

// This test subscribes to interface and component subtree for updates.
void TestGnmiInterfaceAndComponentSubscribe(thinkit::Switch& sut) {
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());
  grpc::ClientContext context;
  auto stream = sut_gnmi_stub->Subscribe(&context);
  ASSERT_NE(stream, nullptr) << "cannot create a stream!.";
  gnmi::SubscribeRequest subscribe_request;
  gnmi::SubscriptionList* subscription_list =
      subscribe_request.mutable_subscribe();
  subscription_list->set_mode(gnmi::SubscriptionList::STREAM);
  subscription_list->mutable_prefix()->set_origin(kOpenconfigStr);
  subscription_list->mutable_prefix()->set_target(kTarget);
  AddSubtreeToGnmiSubscription(kInterfaces, *subscription_list, gnmi::SAMPLE,
                               /*suppress_redundant=*/false, absl::Seconds(5));
  AddSubtreeToGnmiSubscription(kComponents, *subscription_list, gnmi::SAMPLE,
                               /*suppress_redundant=*/false, absl::Seconds(5));
  LOG(INFO) << "Sending subscription: " << subscribe_request.ShortDebugString();
  ASSERT_TRUE(stream->Write(subscribe_request))
      << "Failed Write to forward request: " << subscribe_request.DebugString()
      << ". Possibly broken stream.";
  LOG(INFO) << "Wrote subscribe request.";
  gnmi::SubscribeResponse response;
  bool intf_response_received = false;
  bool component_response_received = false;
  const auto start_time = absl::Now();
  while (absl::Now() < (start_time + kSubscribeWaitTime) &&
         stream->Read(&response)) {
    LOG(INFO) << "Subscribe response received: " << response.DebugString();
    ASSERT_OK_AND_ASSIGN(auto elem_name_vector,
                         GnmiGetElementFromTelemetryResponse(response));
    for (auto elem_name : elem_name_vector) {
      if (elem_name == kComponents) {
        component_response_received = true;
      }
      if (elem_name == kInterfaces) {
        intf_response_received = true;
      }
    }
    if (component_response_received && intf_response_received) {
      break;
    }
  }
  EXPECT_TRUE(component_response_received);
  EXPECT_TRUE(intf_response_received);
}

}  // namespace pins_test
