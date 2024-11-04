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

#include "tests/gnoi/factory_reset_test.h"

#include <cstdint>
#include <cstdlib>
#include <map>
#include <memory>
#include <string>
#include <utility>
#include <valarray>

#include "absl/container/flat_hash_set.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/validator/validator_lib.h"

namespace factory_reset {

constexpr absl::Duration kFactoryResetWaitForDownTime = absl::Seconds(60);
constexpr absl::Duration kFactoryResetWaitForUpTime = absl::Minutes(18);
constexpr absl::Duration kSshSessionTimeout = absl::Seconds(5);

void IssueGnoiFactoryResetAndValidateStatus(
    thinkit::Switch& sut, const gnoi::factory_reset::StartRequest& request,
    gnoi::factory_reset::StartResponse* response,
    grpc::Status expected_status) {
  ASSERT_OK_AND_ASSIGN(auto sut_gnoi_factory_reset_stub,
                       sut.CreateGnoiFactoryResetStub());
  grpc::ClientContext context;
  grpc::Status status =
      sut_gnoi_factory_reset_stub->Start(&context, request, response);
  if (expected_status.ok()) {
    EXPECT_OK(status);
  } else {
    EXPECT_EQ(status.error_code(), expected_status.error_code());
    EXPECT_EQ(status.error_message(), expected_status.error_message());
  }
}

void ValidateStackState(thinkit::Switch& sut,
                        absl::Span<const std::string> interfaces) {
  absl::Time start_time = absl::Now();
  bool system_down = false;

  // Wait for system to become unreachable via ping - as that's the last thing
  // that goes down.
  while (absl::Now() < (start_time + kFactoryResetWaitForDownTime)) {
    if (!pins_test::Pingable(sut).ok()) {
      system_down = true;
      break;
    }
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
  }
  // Return failure if system did not come up.
  ASSERT_FALSE(system_down)
      << "System did not come up in " << kFactoryResetWaitForUpTime;
}

void TestFactoryResetSuccess(thinkit::Switch& sut,
                             thinkit::SSHClient& ssh_client,
                             absl::Span<const std::string> interfaces) {
  gnoi::factory_reset::StartRequest request;
  gnoi::factory_reset::StartResponse response;
  IssueGnoiFactoryResetAndValidateStatus(sut, request, &response);
  // TODO: Check the response protobuf.
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
  // TODO: Check the response and dup_response protobuf.
  ValidateStackState(sut, interfaces);
}

void TestGnoiFactoryResetGnoiServerUnreachableFail(
    thinkit::Switch& sut, thinkit::SSHClient& ssh_client,
    absl::Span<const std::string> interfaces) {
  gnoi::factory_reset::StartRequest request;
  gnoi::factory_reset::StartResponse response;
  IssueGnoiFactoryResetAndValidateStatus(sut, request, &response);

  absl::SleepFor(kFactoryResetWaitForDownTime);
  ASSERT_TRUE(!pins_test::Pingable(sut).ok())
      << "System did not go down in " << kFactoryResetWaitForDownTime;

  // Wait until the switch goes down, send another request and expect a failure
  // due to gNOI server unreachable.
  IssueGnoiFactoryResetAndValidateStatus(
      sut, request, &response,
      grpc::Status(grpc::StatusCode::UNAVAILABLE,
                   "failed to connect to all addresses"));

  absl::SleepFor(kFactoryResetWaitForUpTime);
  // Return failure if system did not come up.
  ASSERT_OK(pins_test::SwitchReady(sut, interfaces))
      << "System did not come up in " << kFactoryResetWaitForUpTime;
}

}  // namespace factory_reset
