// Copyright 2025 Google LLC
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

#include "tests/gnoi/factory_reset_test.h"

#include <memory>
#include <string>

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/numbers.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "factory_reset/factory_reset.pb.h"
#include "gmock/gmock.h"
#include "grpcpp/client_context.h"
#include "grpcpp/support/status.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "lib/validator/validator_lib.h"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

namespace factory_reset {
namespace {

// TODO: investigate why shutdown time is increasing and revert
// to 60s if possible.
constexpr absl::Duration kFactoryResetWaitForDownTime = absl::Seconds(75);
constexpr absl::Duration kPingReachabilityInterval = absl::Seconds(2);
constexpr absl::Duration kPingTimeout = absl::Seconds(1);
constexpr int kConsecutivePingsRequired = 3;
constexpr absl::Duration kFactoryResetWaitForUpTime = absl::Minutes(25);
constexpr absl::Duration kSshSessionTimeout = absl::Seconds(20);

void IssueGnoiFactoryResetAndValidateStatus(
    thinkit::Switch& sut, const gnoi::factory_reset::StartRequest& request,
    gnoi::factory_reset::StartResponse* response,
    grpc::Status expected_status = {}) {
  LOG(INFO) << "Issuing factory reset with parameters: "
            << request.DebugString();
  ASSERT_OK_AND_ASSIGN(auto sut_gnoi_factory_reset_stub,
                       sut.CreateGnoiFactoryResetStub());
  grpc::ClientContext context;
  grpc::Status status =
      sut_gnoi_factory_reset_stub->Start(&context, request, response);
  LOG(INFO) << "Factory reset status: " << status.error_code() << ", "
            << status.error_message();
  LOG(INFO) << "Factory reset response: " << response->DebugString();
  if (expected_status.ok()) {
    EXPECT_OK(status);
  } else {
    EXPECT_EQ(status.error_code(), expected_status.error_code());
    EXPECT_THAT(status.error_message(),
                testing::HasSubstr(expected_status.error_message()));
  }
}

void ValidateStackState(thinkit::Switch& sut,
                        absl::Span<const std::string> interfaces) {
  absl::Time start_time = absl::Now();
  bool system_down = false;

  // Wait for system to become unreachable via ping - as that's the last thing
  // that goes down.
  LOG(INFO) << "Starting polling for unreachability, now: " << absl::Now()
            << " deadline: " << start_time + kFactoryResetWaitForDownTime;
  while (absl::Now() < (start_time + kFactoryResetWaitForDownTime)) {
    if (!pins_test::Pingable(sut, kPingTimeout).ok()) {
      system_down = true;
      break;
    }
    LOG(INFO) << "System still reachable at " << absl::Now() << " sleeping";
    absl::SleepFor(kPingReachabilityInterval);
  }
  // Return failure if system did not go down.
  ASSERT_TRUE(system_down) << "System did not go down in "
                           << kFactoryResetWaitForDownTime;
  // Wait for system to become reachable over gNOI.
  start_time = absl::Now();
  while (absl::Now() < (start_time + kFactoryResetWaitForUpTime)) {
    if (pins_test::SwitchReady(sut, interfaces).ok()) {
      system_down = false;
      break;
    }
    LOG(INFO) << "System still unreachable, sleeping";
    absl::SleepFor(kPingReachabilityInterval);
  }
  // Return failure if system did not come up.
  ASSERT_FALSE(system_down)
      << "System did not come up in " << kFactoryResetWaitForUpTime;
}

}  // namespace

void TestFactoryResetSuccess(thinkit::Switch& sut,
                             thinkit::SSHClient& ssh_client,
                             absl::Span<const std::string> interfaces) {
  gnoi::factory_reset::StartRequest request;
  gnoi::factory_reset::StartResponse response;
  IssueGnoiFactoryResetAndValidateStatus(sut, request, &response);
  EXPECT_TRUE(response.has_reset_success());
  ValidateStackState(sut, interfaces);
}

void TestDuplicateFactoryResetFailure(
    thinkit::Switch& sut, thinkit::SSHClient& ssh_client,
    absl::Span<const std::string> interfaces) {
  gnoi::factory_reset::StartRequest request;
  gnoi::factory_reset::StartResponse response, dup_response;
  IssueGnoiFactoryResetAndValidateStatus(sut, request, &response);
  // Before the switch stack is down, send an immediate duplicate request.
  IssueGnoiFactoryResetAndValidateStatus(sut, request, &dup_response);
  EXPECT_TRUE(response.has_reset_success());
  EXPECT_TRUE(dup_response.reset_error().other());
  EXPECT_EQ(dup_response.reset_error().detail(), "Previous reset is ongoing.");
  ValidateStackState(sut, interfaces);
}

void TestGnoiFactoryResetGnoiServerUnreachableFail(
    thinkit::Switch& sut, thinkit::SSHClient& ssh_client,
    absl::Span<const std::string> interfaces) {
  gnoi::factory_reset::StartRequest request;
  gnoi::factory_reset::StartResponse response;
  IssueGnoiFactoryResetAndValidateStatus(sut, request, &response);
  EXPECT_TRUE(response.has_reset_success());

  LOG(INFO) << "Waiting for device to become unreachable";
  absl::Time start = absl::Now();
  int consecutive_unreachable_count = 0;
  while (consecutive_unreachable_count < kConsecutivePingsRequired) {
    if (pins_test::Pingable(sut, kPingTimeout).ok()) {
      consecutive_unreachable_count = 0;
      LOG(INFO) << "System still reachable";
      if (absl::Now() - start > kFactoryResetWaitForDownTime) {
        FAIL() << "System did not go down in " << kFactoryResetWaitForDownTime;
      }
    } else {
      consecutive_unreachable_count++;
      LOG(INFO) << "System unreachable for " << consecutive_unreachable_count
                << " consecutive pings";
    }
    absl::SleepFor(kPingReachabilityInterval);
  }
  LOG(INFO) << "Device became unreachable after: " << absl::Now() - start;

  // Wait until the switch goes down, send another request and expect a failure
  // due to gNOI server unreachable.
  IssueGnoiFactoryResetAndValidateStatus(
      sut, request, &response,
      grpc::Status(grpc::StatusCode::UNAVAILABLE,
                   "failed to connect to all addresses"));

  LOG(INFO) << "Waiting for device to become reachable";
  absl::SleepFor(kFactoryResetWaitForUpTime);
  // Return failure if system did not come up.
  ASSERT_OK(pins_test::SwitchReady(sut, interfaces))
      << "System did not come up in " << kFactoryResetWaitForUpTime;
}

}  // namespace factory_reset
