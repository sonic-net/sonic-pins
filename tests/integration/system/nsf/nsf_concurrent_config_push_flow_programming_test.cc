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
#include "tests/integration/system/nsf/nsf_concurrent_config_push_flow_programming_test.h"

#include <memory>

#include <string>
#include <thread>
#include <vector>
#include "absl/flags/flag.h"
#include "absl/random/random.h"
#include "absl/status/status.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "google/protobuf/message.h"
#include "grpcpp/client_context.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "lib/gnmi/gnmi_helper.h"
#include "p4_pdpi/ir.pb.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "tests/integration/system/nsf/compare_p4flows.h"
#include "tests/integration/system/nsf/interfaces/image_config_params.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "tests/integration/system/nsf/util.h"
#include "thinkit/switch.h"
#include "thinkit/test_environment.h"

namespace pins_test {
using ::p4::v1::ReadResponse;

constexpr int kIsolatedLacpSystemPriority = 512;

// Here is the criteria for the NSF delay duration window:
// 1. The flows used in the test takes ~3s to get programmed. Hence the minimum
//    delay is set to 4s.
// 2. Config push takes ~10s to complete. Hence the maximum delay is set to 14s.
// In future, if the config or the flows are modified, consider calculating the
// time needed for both and set the NSF delay duration window accordingly.

constexpr int kFlowPrepDuration = 3;
constexpr int kMinNsfDelayDuration = kFlowPrepDuration + 1;
constexpr int kMaxNsfDelayDuration = kMinNsfDelayDuration + 10;
// TODO: Remove the below constants once hsflowd changes are
// rolled out to release.
constexpr int kMinNsfDelayReleaseDuration = 15;
constexpr int kMaxNsfDelayReleaseDuration = 25;
constexpr absl::Duration kTurnUpTimeout = absl::Minutes(6);
constexpr char kInterfaceToRemove[] = "Ethernet1/10/1";
constexpr int kMaxGnmiGetClients = 15;
constexpr int kMaxGnmiSubscribeClients = 10;
constexpr absl::Duration kSubscribeWaitTime = absl::Seconds(100);

void NsfConcurrentConfigPushFlowProgrammingTestFixture::SetUp() {
  flow_programmer_ = GetParam().create_flow_programmer();
  traffic_helper_ = GetParam().create_traffic_helper();
  testbed_interface_ = GetParam().create_testbed_interface();
  component_validators_ = GetParam().create_component_validators();
  ssh_client_ = GetParam().create_ssh_client();
  SetupTestbed(testbed_interface_);
  ASSERT_OK_AND_ASSIGN(testbed_, GetTestbed(testbed_interface_));
}
void NsfConcurrentConfigPushFlowProgrammingTestFixture::TearDown() {
  if (HasFailure()) {
    thinkit::Switch& sut = GetSut(testbed_);
    LOG(INFO) << "Performing cold reboot to recover the switch.";
    thinkit::TestEnvironment& env = GetTestEnvironment(testbed_);
    ASSERT_OK(
        pins_test::Reboot(gnoi::system::RebootMethod::COLD, sut, env,
                          /*collect_debug_artifacts_before_reboot=*/false));
    ASSERT_OK(WaitForReboot(testbed_, *ssh_client_));
  }
  if (!GetParam().image_config_params.empty()) {
    LOG(INFO) << "Restoring the original config";
    ASSERT_OK(PushConfig(GetParam().image_config_params[0], GetSut(testbed_),
                         *ssh_client_));
    ASSERT_OK(WaitForSwitchState(GetSut(testbed_), SwitchState::kReady,
                                 kTurnUpTimeout, *ssh_client_,
                                 GetConnectedInterfacesForSut(testbed_)));
  }
  TearDownTestbed(testbed_interface_);
}

TEST_P(NsfConcurrentConfigPushFlowProgrammingTestFixture,
       NsfConcurrentConfigPushFlowProgrammingTest) {
  thinkit::TestEnvironment &environment = GetTestEnvironment(testbed_);

  // The test needs at least 1 image_config_param to run.
  if (GetParam().image_config_params.empty()) {
    GTEST_SKIP() << "No image config params provided";
  }
  // Pick the first image config param.
  ImageConfigParams image_config_param = GetParam().image_config_params[0];
  thinkit::Switch& sut = GetSut(testbed_);

  LOG(INFO) << "Clearing the flows before the start of the test";
  ASSERT_OK(flow_programmer_->ClearFlows(testbed_));

  ASSERT_OK(ValidateTestbedState(testbed_, *ssh_client_, &image_config_param));

  // P4 snapshot before programming flows and starting the traffic.
  LOG(INFO) << "Capturing P4 snapshot before programming flows and starting "
               "the traffic";
  ASSERT_OK_AND_ASSIGN(ReadResponse p4flow_snapshot1, TakeP4FlowSnapshot(sut));
  ASSERT_OK(SaveP4FlowSnapshot(p4flow_snapshot1,
                               "p4flow_snapshot1_before_programming_flows.txt",
                               environment));

  // Program all the flows.
  LOG(INFO) << "Programming L3 flows before starting the traffic";
  ASSERT_OK(flow_programmer_->ProgramFlows(image_config_param, testbed_,
                                           *ssh_client_));
  LOG(INFO) << "Starting the traffic";
  ASSERT_OK(traffic_helper_->StartTraffic(testbed_));
  // Modifying existing config.
  // Creating a copy.
  ImageConfigParams modified_image_config_param = image_config_param;
  ASSERT_OK(environment.StoreTestArtifact("original_gnmi_config.json",
                                          image_config_param.gnmi_config));
  ASSERT_OK(environment.StoreTestArtifact(
      "modified_gnmi_config.json", modified_image_config_param.gnmi_config));

  ASSERT_OK(StoreSutDebugArtifacts(
      absl::StrCat(
          "before_nsf_reboot_",
          absl::FormatTime("%H_%M_%S", absl::Now(), absl::LocalTimeZone())),
      sut, environment));
  absl::BitGen gen;
  
  // TODO - Remove the below code once hsflowd changes are
  // rolled out to release.
  bool is_release_image = true;

  int nsf_delay_duration;
  if (is_release_image) {
    nsf_delay_duration = absl::uniform_int_distribution<int>(
        kMinNsfDelayReleaseDuration, kMaxNsfDelayReleaseDuration)(gen);
  } else {
    nsf_delay_duration = absl::uniform_int_distribution<int>(
        kMinNsfDelayDuration, kMaxNsfDelayDuration)(gen);
  }

  // Config Push thread.
  absl::Status config_push_status = absl::UnknownError("Yet to push config");
  auto config_push_func = [&sut,
                           &modified_image_config_param]() -> absl::Status {
    LOG(INFO) << "Pushing modified config on " << sut.ChassisName();
    RETURN_IF_ERROR(
        PushGnmiConfig(sut, modified_image_config_param.gnmi_config));
    LOG(INFO) << "Successfully pushed modified config on " << sut.ChassisName();
    return absl::OkStatus();
  };
  std::thread config_push_thread(
      [&]() { config_push_status = config_push_func(); });

  // Flow Programming thread.
  absl::Status flow_programming_status =
      absl::UnknownError("Yet to program flows");
  auto flow_programming_func = [&sut, &image_config_param,
                                &is_release_image]() -> absl::Status {
    // TODO - Remove the below code once hsflowd changes are
    // rolled out to release.
    if (is_release_image) {
      // Flows used in the test takes ~6s to get programmed.
      if (kMinNsfDelayDuration > 6) {
        absl::SleepFor(absl::Seconds(kMinNsfDelayDuration - 6));
      }
    }

    LOG(INFO) << "Programming flows";
    RETURN_IF_ERROR(ProgramFlowsBasedOnTable(sut, image_config_param.p4_info,
                                             "ipv6_table"));
    LOG(INFO) << "Successfully programmed flows on " << sut.ChassisName();
    return absl::OkStatus();
  };
  std::thread flow_programming_thread(
      [&]() { flow_programming_status = flow_programming_func(); });

  // Get gNMI info thread. Fetch gNMI information multiple times periodically
  // from different clients to increase stress from Get() clients.
  auto get_gnmi_func = [&nsf_delay_duration, &sut]() -> absl::Status {
    // Wait for sometime before initiating the gNMI connection. The order of
    // test execution is as follows:
    // 1) Create Get() threads.
    // 2) Create NSF reboot thread.
    // In each Get() thread, wait for sometime and then start Get() operation.
    // This increases the chances of hitting the race condition between gNMI
    // operation and NSF reboot request.
    absl::SleepFor(absl::Seconds(nsf_delay_duration));
    LOG(INFO) << "Fetching gNMI information on " << sut.ChassisName();
    ASSIGN_OR_RETURN(auto gnmi_stub, sut.CreateGnmiStub());
    auto status = GetGnmiStatePathInfo(gnmi_stub.get(), "");
    LOG(INFO) << "gNMI Get() operation completed";
    return absl::OkStatus();
  };
  std::vector<std::thread> gnmi_get_threads;
  for (int i = 0; i < kMaxGnmiGetClients; i++) {
    gnmi_get_threads.emplace_back(get_gnmi_func);
  }

  // gNMI subscribe thread to increase stress from gNMI subscribe clients.
  auto subscribe_gnmi_func = [&nsf_delay_duration, &sut]() -> absl::Status {
    // Wait for sometime before initiating the gNMI connection (same reason as
    // gNMI Get() thread above).
    absl::SleepFor(absl::Seconds(nsf_delay_duration));
    ASSIGN_OR_RETURN(auto gnmi_stub, sut.CreateGnmiStub());
    grpc::ClientContext context;
    auto stream = gnmi_stub->Subscribe(&context);
    if (stream == nullptr) {
      return absl::InternalError("Cannot create gNMI stream");
    }
    gnmi::SubscribeRequest subscribe_request;
    gnmi::SubscriptionList* subscription_list =
        subscribe_request.mutable_subscribe();
    subscription_list->set_mode(gnmi::SubscriptionList::STREAM);
    subscription_list->mutable_prefix()->set_origin(kOpenconfigStr);
    subscription_list->mutable_prefix()->set_target(kTarget);
    AddSubtreeToGnmiSubscription("", *subscription_list, gnmi::SAMPLE,
                                 /*suppress_redundant=*/false,
                                 absl::Seconds(1));
    LOG(INFO) << "Sending subscription request: "
              << google::protobuf::ShortFormat(subscribe_request);
    if (!stream->Write(subscribe_request)) {
      return absl::InternalError("Failed to write subscribe request");
    }
    LOG(INFO) << "Write subscribe request successful. Reading from stream..";
    const auto start_time = absl::Now();
    while (absl::Now() < (start_time + kSubscribeWaitTime)) {
      gnmi::SubscribeResponse response;
      if (!stream->Read(&response)) {
        // Stream to server is broken possibly due to warm reboot.
        LOG(INFO) << "Subscribe client cannot read from the stream";
        return absl::OkStatus();
      }
      LOG(INFO) << "Subscribe response received";
    }
    return absl::InternalError(
        "subscribe client didn't break stream with server");
  };
  std::vector<std::thread> gnmi_subscribe_threads;
  for (int i = 0; i < kMaxGnmiSubscribeClients; i++) {
    gnmi_subscribe_threads.emplace_back(subscribe_gnmi_func);
  }

  // NSF Reboot thread.
  absl::Status nsf_reboot_status = absl::UnknownError("Yet to do nsf reboot");
  ReadResponse p4flow_snapshot2;
  auto nsf_reboot_func = [&nsf_delay_duration, &sut, &environment,
                          &p4flow_snapshot2]() -> absl::Status {
    // Sleeping for few seconds before joining NSF thread. This is to make sure
    // config push and flow programming are initiated before NSF.
    LOG(INFO) << "Sleeping for " << nsf_delay_duration
              << " seconds before triggering NSF reboot";
    absl::SleepFor(absl::Seconds(nsf_delay_duration));
    // P4 snapshot before NSF reboot.
    LOG(INFO) << "Capturing P4 snapshot before NSF reboot";
    ASSIGN_OR_RETURN(p4flow_snapshot2, TakeP4FlowSnapshot(sut));
    LOG(INFO) << "Initiating NSF reboot";
    // Using generic Reboot helper instead of Nsf specific helper as that has an
    // initial delay to collect the debug artifacts. The below call will trigger
    // NSF reboot immediately.
    RETURN_IF_ERROR(
        pins_test::Reboot(gnoi::system::RebootMethod::NSF, sut, environment,
                          /*collect_debug_artifacts_before_reboot=*/false));
    LOG(INFO) << "Successfully triggered NSF reboot on " << sut.ChassisName();
    return absl::OkStatus();
  };
  std::thread nsf_reboot_thread(
      [&]() { nsf_reboot_status = nsf_reboot_func(); });

  // Joining all threads.
  config_push_thread.join();
  flow_programming_thread.join();
  nsf_reboot_thread.join();
  // Calling the SaveP4FlowSnapshot function after the NSF reboot thread is
  // joined. This is to avoid the delay that might get introduced by the
  // SaveP4FlowSnapshot function before the NSF reboot.
  EXPECT_OK(SaveP4FlowSnapshot(p4flow_snapshot2,
                               "p4flow_snapshot2_before_nsf.txt", environment));
  // Since gNMI Get and Subscribe clients are read-only and are being called to
  // add delay during quiescence, we don't really care about the result of these
  // calls. Therefore, joining these threads after all information has been
  // fetched from the switch to perform validations.
  for (auto& gnmi_get_thread : gnmi_get_threads) {
    gnmi_get_thread.join();
  }
  for (auto& gnmi_subscribe_thread : gnmi_subscribe_threads) {
    gnmi_subscribe_thread.join();
  }
  EXPECT_OK(config_push_status) << "Failed to push config";
  EXPECT_OK(flow_programming_status) << "Failed to program flows";
  ASSERT_OK(nsf_reboot_status) << "Failed to initiate NSF reboot";
  ASSERT_OK(
      WaitForNsfReboot(testbed_, *ssh_client_, &modified_image_config_param));

  // P4 snapshot after upgrade and NSF reboot.
  LOG(INFO) << "Capturing P4 snapshot after NSF reboot";
  ASSERT_OK_AND_ASSIGN(ReadResponse p4flow_snapshot3, TakeP4FlowSnapshot(sut));
  ASSERT_OK(SaveP4FlowSnapshot(p4flow_snapshot3,
                               "p4flow_snapshot3_after_nsf.txt", environment));

  // Stop and validate traffic
  LOG(INFO) << "Stopping the traffic";
  ASSERT_OK(traffic_helper_->StopTraffic(testbed_));

  // TODO: For now, we validate traffic only after stopping
  // traffic. Ideally we would want to validate traffic while injection is in
  // progress to narrow down when the traffic loss occurred (i.e. before
  // reboot, during reboot or after reconciliation).
  LOG(INFO) << "Validating the traffic";
  ASSERT_OK(traffic_helper_->ValidateTraffic(testbed_));

  LOG(INFO) << "Clearing the flows";
  ASSERT_OK(flow_programmer_->ClearFlows(testbed_));

  // P4 snapshot after clearing flows.
  LOG(INFO) << "Capturing P4 snapshot after clearing flows";
  ASSERT_OK_AND_ASSIGN(ReadResponse p4flow_snapshot4, TakeP4FlowSnapshot(sut));
  ASSERT_OK(SaveP4FlowSnapshot(p4flow_snapshot4,
                               "p4flow_snapshot4_after_clearing_flows.txt",
                               environment));

  LOG(INFO) << "Comparing P4 snapshots - Before Programming Flows Vs After "
               "Clearing Flows";
  EXPECT_OK(CompareP4FlowSnapshots(p4flow_snapshot1, p4flow_snapshot4));

  LOG(INFO) << "Comparing P4 snapshots - Before Vs. After NSF Reboot";
  ASSERT_OK(CompareP4FlowSnapshots(p4flow_snapshot2, p4flow_snapshot3));
}

}  // namespace pins_test
