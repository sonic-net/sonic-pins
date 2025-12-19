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

#include "tests/gnoi/bert_tests.h"

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <ctime>
#include <iterator>
#include <random>
#include <sstream>
#include <string>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/flags/flag.h"
#include "absl/log/log.h"
#include "absl/random/random.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "diag/diag.grpc.pb.h"
#include "diag/diag.pb.h"
#include "gmock/gmock.h"
#include "google/protobuf/util/message_differencer.h"
#include "grpcpp/client_context.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/validator/validator_lib.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "system/system.grpc.pb.h"
#include "system/system.pb.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "tests/integration/system/nsf/util.h"
#include "tests/thinkit_gnmi_interface_util.h"
#include "thinkit/control_device.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/switch.h"

ABSL_FLAG(uint32_t, idx_seed, static_cast<uint32_t>(std::time(nullptr)),
          "Seed to randomly generate interface index.");

ABSL_FLAG(std::string, interface, "",
          "Interface to run qualification on. If unspecified, random port "
          "will be chosen.");

ABSL_FLAG(std::vector<std::string>, interfaces, std::vector<std::string>(),
          "Interfaces to run qualification on. If unspecified, random ports "
          "will be chosen.");

namespace bert {
namespace {

using ::gnoi::diag::StartBERTResponse_PerPortResponse;
using ::gnoi::diag::StopBERTResponse_PerPortResponse;
using ::google::protobuf::util::MessageDifferencer;
using ::gutil::IsOkAndHolds;
using ::testing::HasSubstr;
using ::testing::SizeIs;

// BERT test duration.
constexpr absl::Duration kTestDuration = absl::Seconds(180);
constexpr absl::Duration kLongTestDuration = absl::Seconds(360);
// Maximum allowed duration for port to sync with its peer.
constexpr absl::Duration kSyncDuration = absl::Minutes(5);
// Maximum allowed BERT delay duration due to setup, sync and recovery
// operations.
constexpr absl::Duration kDelayDuration = absl::Minutes(10);
// Wait duration after requesting BERT to read the oper status of the port.
constexpr absl::Duration kWaitToReadOperStatus = absl::Seconds(30);
// Polling interval.
constexpr absl::Duration kPollInterval = absl::Seconds(30);
// Minimum wait time after the BERT request to read the BERT result.
constexpr absl::Duration kWaitTime = absl::Seconds(30);
// Wait time for ports to be up after re-enabling admin down ports.
constexpr absl::Duration kPortsUpWaitTime = absl::Seconds(30);
// Wait time for BERT recovery phase.
constexpr absl::Duration kWaitForRecoveryComplete = absl::Seconds(90);

constexpr uint8_t kMaxAllowedInterfacesToRunBert = 96;

constexpr char kEnabledFalse[] = "{\"enabled\":false}";
constexpr char kEnabledTrue[] = "{\"enabled\":true}";

constexpr absl::Duration kNsfActiveTimeout = absl::Minutes(3);

std::string BuildPerPortStartBertRequest(
    absl::string_view interface_name,
    absl::Duration test_duration = kTestDuration) {
  return absl::Substitute(R"pb(
                            interface {
                              origin: "openconfig"
                              elem { name: "interfaces" }
                              elem {
                                name: "interface"
                                key { key: "name" value: '$0' }
                              }
                            }
                            prbs_polynomial: PRBS_POLYNOMIAL_PRBS31
                            test_duration_in_secs: $1
                          )pb",
                          interface_name, ToInt64Seconds(test_duration));
}

std::string BuildOpenConfigInterface(absl::string_view interface_name) {
  return absl::Substitute(R"pb(
                            origin: "openconfig"
                            elem { name: "interfaces" }
                            elem {
                              name: "interface"
                              key { key: "name" value: '$0' }
                            }
                          )pb",
                          interface_name);
}

void SendStartBertRequestSuccessfullyOnSut(
    const gnoi::diag::StartBERTRequest& request,
    gnoi::diag::Diag::StubInterface& gnoi_diag_stub) {
  gnoi::diag::StartBERTResponse response;
  grpc::ClientContext context;
  LOG(INFO) << "StartBERT request on SUT: " << request.ShortDebugString();
  ASSERT_OK(gnoi_diag_stub.StartBERT(&context, request, &response));

  // Verify response.
  ASSERT_THAT(response.per_port_responses(),
              SizeIs(request.per_port_requests_size()));
  EXPECT_EQ(response.bert_operation_id(), request.bert_operation_id());

  for (int idx = 0; idx < response.per_port_responses_size(); ++idx) {
    const StartBERTResponse_PerPortResponse &per_port_response =
        response.per_port_responses(idx);
    SCOPED_TRACE(absl::StrCat("Verifying StartBERT port response on SUT: ",
                              per_port_response.ShortDebugString()));
    EXPECT_EQ(per_port_response.status(), gnoi::diag::BERT_STATUS_OK);
    EXPECT_TRUE(
        MessageDifferencer::Equals(per_port_response.interface(),
                                   request.per_port_requests(idx).interface()));
  }
}

void SendStartBertRequestSuccessfullyOnControlSwitch(
    const gnoi::diag::StartBERTRequest& request,
    thinkit::ControlDevice& control_device) {
  LOG(INFO) << "StartBERT request on control switch: "
            << request.ShortDebugString();

  ASSERT_OK_AND_ASSIGN(gnoi::diag::StartBERTResponse response,
                       control_device.StartBERT(request));

  // Verify response.
  ASSERT_THAT(response.per_port_responses(),
              SizeIs(request.per_port_requests_size()));

  EXPECT_EQ(response.bert_operation_id(), request.bert_operation_id());

  for (int idx = 0; idx < response.per_port_responses_size(); ++idx) {
    const StartBERTResponse_PerPortResponse &per_port_response =
        response.per_port_responses(idx);
    SCOPED_TRACE(
        absl::StrCat("Verifying StartBERT port response on control switch: ",
                     per_port_response.ShortDebugString()));
    EXPECT_EQ(per_port_response.status(), gnoi::diag::BERT_STATUS_OK);
    EXPECT_TRUE(
        MessageDifferencer::Equals(per_port_response.interface(),
                                   request.per_port_requests(idx).interface()));
  }
}

absl::StatusOr<std::string> GetInterfaceNameFromOcInterfacePath(
    const gnoi::types::Path& interface) {
  // Validate if interface is in valid format(either in OpenConfig format or
  // SONiC format).
  // Example: openconfig/interfaces/interface[name=Ethernet0] or
  // openconfig-interfaces/interfaces/interface[name=Ethernet0].
  std::stringstream error_stream;
  if ((interface.origin() != "openconfig") &&
      (interface.origin() != "openconfig-interfaces")) {
    error_stream << "Invalid interface origin. Expected: openconfig or "
                    "openconfig-interfaces but received: "
                 << interface.origin() << " in: " << interface.DebugString();
    return absl::InvalidArgumentError(error_stream.str());
  }
  auto elems = interface.elem();
  if (elems.size() != 2) {
    error_stream << "Invalid element path count. Expected: 2 but received: "
                 << elems.size() << " in: " << interface.DebugString();
    return absl::InvalidArgumentError(error_stream.str());
  }
  if ((elems[0].name() != "interfaces") || (elems[0].key_size() > 0)) {
    error_stream << "First interface path element is malformed. Expected "
                    "element name: interfaces but received: "
                 << elems[0].name()
                 << " and expected 0 key but received: " << elems[0].key_size()
                 << " in: " << interface.DebugString();
    return absl::InvalidArgumentError(error_stream.str());
  }
  if ((elems[1].name() != "interface")) {
    error_stream << "Second interface path element is malformed. Expected "
                    "element name: interface but received: "
                 << elems[1].name() << " in: " << interface.DebugString();
    return absl::InvalidArgumentError(error_stream.str());
  }
  auto it = elems[1].key().find("name");
  if (it != elems[1].key().end()) {
    return it->second;
  }
  return absl::InvalidArgumentError(
      absl::StrCat("Interface name is missing in: ", interface.DebugString()));
}

void SetAdminStateOnInterfaceList(gnmi::gNMI::StubInterface& gnmi_stub,
                                  std::vector<std::string>& interfaces,
                                  absl::string_view value) {
  for (const std::string& interface : interfaces) {
    const std::string if_enabled_config_path = absl::StrCat(
        "interfaces/interface[name=", interface, "]/config/enabled");
    ASSERT_OK(SetGnmiConfigPath(&gnmi_stub, if_enabled_config_path,
                                pins_test::GnmiSetType::kUpdate, value));
  }
}

bool IsInterfaceInList(absl::string_view interface,
                       const std::vector<std::string>& interfaces) {
  return std::find(interfaces.begin(), interfaces.end(), interface) !=
         interfaces.end();
}

void WaitForBertToCompleteOnInterfaces(
    gnmi::gNMI::StubInterface& sut_gnmi_stub,
    std::vector<std::string> sut_interfaces,
    thinkit::ControlDevice& control_device,
    gnoi::diag::GetBERTResultRequest control_switch_result_request,
    int max_poll_count, absl::Duration test_duration = kTestDuration) {
  for (int count = 0; count < max_poll_count; ++count) {
    absl::SleepFor(kPollInterval);
    // If port is no longer in "TESTING" oper state on both sides of the link,
    // linkqual has completed on the link and full result is ready.
    for (auto it = sut_interfaces.begin(); it != sut_interfaces.end();) {
      ASSERT_OK_AND_ASSIGN(
          pins_test::OperStatus oper_status,
          pins_test::GetInterfaceOperStatusOverGnmi(sut_gnmi_stub, *it));
      if (oper_status != pins_test::OperStatus::kTesting) {
        it = sut_interfaces.erase(it);
        continue;
      }
      ++it;
    }

    // Check if BERT is completed on control switch - we cannot check
    // "TESTING" mode on control device so read BERT result and verify that
    // BERT either failed, or succeeded and the error count per minute field
    // is completely populated (size is equal to number of minutes). If status
    // is OK and error count per minute field isn't completely populated, BERT
    // is still in progress.
    if (control_switch_result_request.per_port_requests_size() != 0) {
      gnoi::diag::GetBERTResultRequest tmp_result_request;
      tmp_result_request.set_bert_operation_id(
          control_switch_result_request.bert_operation_id());
      ASSERT_OK_AND_ASSIGN(
          gnoi::diag::GetBERTResultResponse result_response,
          control_device.GetBERTResult(control_switch_result_request));
      ASSERT_THAT(
          result_response.per_port_responses(),
          SizeIs(control_switch_result_request.per_port_requests_size()));
      int testDurationMinutes = absl::ToInt64Minutes(test_duration);
      for (const auto& result : result_response.per_port_responses()) {
        if (result.status() == gnoi::diag::BERT_STATUS_OK &&
            result.error_count_per_minute_size() < testDurationMinutes) {
          *(tmp_result_request.add_per_port_requests()->mutable_interface()) =
              result.interface();
        }
      }
      control_switch_result_request = tmp_result_request;
    }
    if (sut_interfaces.empty() &&
        (control_switch_result_request.per_port_requests_size() == 0))
      break;
  }

  EXPECT_THAT(sut_interfaces, testing::IsEmpty());
  EXPECT_THAT(control_switch_result_request.per_port_requests(),
              testing::IsEmpty());
  // For SUT ports, verification of non-TESTING mode is enough to indicate the
  // completion of BERT. However for the control switch, there is a possibility
  // that when the result was read, results were fully populated but recovery
  // steps were not completed yet, if control switch BERT steps were running
  // behind the SUT BERT steps - we cannot differentiate if BERT is completed or
  // post BERT recovery steps are still in progress based on BERT results on
  // control switch. Sleeping for some extra time ensures that control switch
  // BERT is completed.
  absl::SleepFor(kWaitForRecoveryComplete);
}

void VerifyBertResultForSuccess(
    const gnoi::diag::GetBERTResultResponse::PerPortResponse& bert_result,
    absl::string_view op_id, const gnoi::types::Path& interface,
    gnoi::diag::PrbsPolynomial prbs_order,
    absl::Duration test_duration = kTestDuration) {
  EXPECT_EQ(bert_result.status(), gnoi::diag::BERT_STATUS_OK);
  EXPECT_TRUE(MessageDifferencer::Equals(bert_result.interface(), interface));
  EXPECT_EQ(bert_result.bert_operation_id(), op_id);
  EXPECT_EQ(bert_result.prbs_polynomial(), prbs_order);
  EXPECT_TRUE(bert_result.peer_lock_established());
  EXPECT_FALSE(bert_result.peer_lock_lost());
  // Check the timestamps to verify if time taken for BERT is between test
  // duration and (test duration + 60 seconds). Allow duration to be slightly
  // less: Sandcastle BERT duration is sometimes just under 180s, by less than
  // 1 second.
  EXPECT_GE(bert_result.last_bert_get_result_timestamp() -
                bert_result.last_bert_start_timestamp(),
            absl::ToInt64Microseconds(test_duration - absl::Seconds(1)));
  EXPECT_LE(bert_result.last_bert_get_result_timestamp() -
                bert_result.last_bert_start_timestamp(),
            absl::ToInt64Microseconds(test_duration + absl::Seconds(60)));

  EXPECT_THAT(bert_result.error_count_per_minute(),
              SizeIs(absl::ToInt64Minutes(test_duration)));
  uint64_t total_errors = 0;
  for (const uint32_t error_count : bert_result.error_count_per_minute()) {
    total_errors += error_count;
  }
  EXPECT_EQ(bert_result.total_errors(), total_errors);
}

// Helps in getting the BERT result on a set of ports and if BERT is running on
// the port, forces admin status down by disabling it. It also modifies the
// list of ports in request by removing the port that was running BERT.
void CheckRunningBertAndForceAdminDownHelperSut(
    gnoi::diag::Diag::StubInterface& gnoi_diag_stub,
    gnmi::gNMI::StubInterface& gnmi_stub,
    thinkit::ControlDevice& control_device,
    const absl::flat_hash_map<std::string, std::string>&
        sut_to_control_interface_mapping,
    gnoi::diag::GetBERTResultRequest* request,
    gnoi::diag::GetBERTResultRequest* request_peer_admin_down) {
  gnoi::diag::GetBERTResultResponse response;
  grpc::ClientContext context;
  ASSERT_OK(gnoi_diag_stub.GetBERTResult(&context, *request, &response));

  ASSERT_THAT(response.per_port_responses(),
              SizeIs(request->per_port_requests_size()));

  gnoi::diag::GetBERTResultResponse response_peer;
  ASSERT_OK_AND_ASSIGN(response_peer,
                       control_device.GetBERTResult(*request_peer_admin_down));
  absl::flat_hash_map<std::string, bool> peer_bert_running;
  ASSERT_THAT(response_peer.per_port_responses(),
              SizeIs(request_peer_admin_down->per_port_requests_size()));
  for (const auto& result : response_peer.per_port_responses()) {
    ASSERT_OK_AND_ASSIGN(
        const std::string interface,
        GetInterfaceNameFromOcInterfacePath(result.interface()));
    peer_bert_running[interface] =
        (result.status() == gnoi::diag::BERT_STATUS_OK) &&
        (result.peer_lock_established());
  }
  request->clear_per_port_requests();
  request_peer_admin_down->clear_per_port_requests();
  for (const auto& result : response.per_port_responses()) {
    ASSERT_OK_AND_ASSIGN(
        const std::string interface,
        GetInterfaceNameFromOcInterfacePath(result.interface()));
    absl::string_view peer_interface =
        sut_to_control_interface_mapping.at(interface);
    // Check if BERT is running.
    if ((result.status() == gnoi::diag::BERT_STATUS_OK) &&
        (result.peer_lock_established()) &&
        peer_bert_running.at(peer_interface)) {
      // Disable the admin status.
      const std::string if_enabled_config_path = absl::StrCat(
          "interfaces/interface[name=", interface, "]/config/enabled");
      ASSERT_OK(SetGnmiConfigPath(&gnmi_stub, if_enabled_config_path,
                                  pins_test::GnmiSetType::kUpdate,
                                  kEnabledFalse));
    } else {
      // Get result for interfaces again that didn't start BERT in last poll.
      *(request->add_per_port_requests()->mutable_interface()) =
          result.interface();
      *(request_peer_admin_down->add_per_port_requests()->mutable_interface()) =
          gutil::ParseProtoOrDie<gnoi::types::Path>(
              BuildOpenConfigInterface(peer_interface));
    }
  }
}

void CheckRunningBertAndForceAdminDownHelperControlSwitch(
    thinkit::ControlDevice& control_device,
    gnoi::diag::Diag::StubInterface& gnoi_diag_stub,
    const absl::flat_hash_map<std::string, std::string>&
        control_to_sut_interface_mapping,
    gnoi::diag::GetBERTResultRequest* request,
    gnoi::diag::GetBERTResultRequest* request_peer_admin_down) {
  gnoi::diag::GetBERTResultResponse response;

  ASSERT_OK_AND_ASSIGN(response, control_device.GetBERTResult(*request));

  ASSERT_THAT(response.per_port_responses(),
              SizeIs(request->per_port_requests_size()));

  gnoi::diag::GetBERTResultResponse response_peer;
  grpc::ClientContext context;
  ASSERT_OK(gnoi_diag_stub.GetBERTResult(&context, *request_peer_admin_down,
                                         &response_peer));
  absl::flat_hash_map<std::string, bool> peer_bert_running;
  ASSERT_THAT(response_peer.per_port_responses(),
              SizeIs(request_peer_admin_down->per_port_requests_size()));
  for (const auto& result : response_peer.per_port_responses()) {
    ASSERT_OK_AND_ASSIGN(
        const std::string interface,
        GetInterfaceNameFromOcInterfacePath(result.interface()));
    peer_bert_running[interface] =
        (result.status() == gnoi::diag::BERT_STATUS_OK) &&
        (result.peer_lock_established());
  }
  request->clear_per_port_requests();
  request_peer_admin_down->clear_per_port_requests();
  for (const auto& result : response.per_port_responses()) {
    ASSERT_OK_AND_ASSIGN(
        const std::string interface,
        GetInterfaceNameFromOcInterfacePath(result.interface()));
    absl::string_view peer_interface =
        control_to_sut_interface_mapping.at(interface);
    // Check if BERT is running.
    if ((result.status() == gnoi::diag::BERT_STATUS_OK) &&
        (result.peer_lock_established()) &&
        peer_bert_running.at(peer_interface)) {
      // Disable the admin status.
      EXPECT_OK(control_device.SetAdminLinkState({interface},
                                                 thinkit::LinkState::kDown));
    } else {
      // Get result for interfaces again that didn't start BERT in last poll.
      *(request->add_per_port_requests()->mutable_interface()) =
          result.interface();
      *(request_peer_admin_down->add_per_port_requests()->mutable_interface()) =
          gutil::ParseProtoOrDie<gnoi::types::Path>(
              BuildOpenConfigInterface(peer_interface));
    }
  }
}

// Checks if BERT is running on the ports where we are supposed to force admin
// status DOWN. If BERT is running, force admin status to DOWN on port.
void CheckRunningBertAndForceAdminDown(
    gnoi::diag::Diag::StubInterface& sut_gnoi_diag_stub,
    thinkit::ControlDevice& control_device,
    gnmi::gNMI::StubInterface& sut_gnmi_stub, absl::string_view op_id,
    const std::vector<std::string>& sut_interfaces,
    const std::vector<std::string>& control_switch_interfaces,
    const absl::flat_hash_map<std::string, std::string>&
        sut_to_control_interface_mapping,
    const absl::flat_hash_map<std::string, std::string>&
        control_to_sut_interface_mapping) {
  gnoi::diag::GetBERTResultRequest sut_request;
  gnoi::diag::GetBERTResultRequest control_switch_request_peer_admin_down;
  sut_request.set_bert_operation_id(std::string(op_id));
  control_switch_request_peer_admin_down.set_bert_operation_id(
      std::string(op_id));
  for (const std::string& interface : sut_interfaces) {
    *(sut_request.add_per_port_requests()->mutable_interface()) =
        gutil::ParseProtoOrDie<gnoi::types::Path>(
            BuildOpenConfigInterface(interface));

    absl::string_view peer_interface =
        sut_to_control_interface_mapping.at(interface);
    *(control_switch_request_peer_admin_down.add_per_port_requests()
          ->mutable_interface()) =
        gutil::ParseProtoOrDie<gnoi::types::Path>(
            BuildOpenConfigInterface(peer_interface));
  }

  gnoi::diag::GetBERTResultRequest control_switch_request;
  gnoi::diag::GetBERTResultRequest sut_request_peer_admin_down;
  control_switch_request.set_bert_operation_id(std::string(op_id));
  sut_request_peer_admin_down.set_bert_operation_id(std::string(op_id));
  for (const std::string& interface : control_switch_interfaces) {
    *(control_switch_request.add_per_port_requests()->mutable_interface()) =
        gutil::ParseProtoOrDie<gnoi::types::Path>(
            BuildOpenConfigInterface(interface));
    absl::string_view peer_interface =
        control_to_sut_interface_mapping.at(interface);
    *(sut_request_peer_admin_down.add_per_port_requests()
          ->mutable_interface()) =
        gutil::ParseProtoOrDie<gnoi::types::Path>(
            BuildOpenConfigInterface(peer_interface));
  }

  int max_poll_count =
      1 + (absl::ToInt64Seconds(kSyncDuration - absl::Seconds(1)) /
           absl::ToInt64Seconds(kPollInterval));

  while (max_poll_count > 0) {
    absl::SleepFor(kPollInterval);
    if (sut_request.per_port_requests_size() > 0) {
      // Check BERT status on SUT and force admin status down.
      ASSERT_NO_FATAL_FAILURE(CheckRunningBertAndForceAdminDownHelperSut(
          sut_gnoi_diag_stub, sut_gnmi_stub, control_device,
          sut_to_control_interface_mapping, &sut_request,
          &control_switch_request_peer_admin_down));
    }

    if (control_switch_request.per_port_requests_size() > 0) {
      // Check BERT status on control switch and force admin status down.
      ASSERT_NO_FATAL_FAILURE(
          CheckRunningBertAndForceAdminDownHelperControlSwitch(
              control_device, sut_gnoi_diag_stub,
              control_to_sut_interface_mapping, &control_switch_request,
              &sut_request_peer_admin_down));
    }
    if (sut_request.per_port_requests().empty() &&
        control_switch_request.per_port_requests().empty()) {
      break;
    }
    --max_poll_count;
  }

  EXPECT_THAT(sut_request.per_port_requests(), testing::IsEmpty());
  EXPECT_THAT(control_switch_request.per_port_requests(), testing::IsEmpty());
}

// Gets the BERT result on all the ports that are running BERT. Verifies BERT
// failure result on ports where admin status was forced to DOWN. Other ports
// are expected to have successful BERT results.
void GetAndVerifyBertResultsWithAdminDownInterfaces(
    const gnoi::diag::StartBERTRequest& bert_request,
    const gnoi::diag::GetBERTResultResponse& result_response,
    const std::vector<std::string>& admin_down_interfaces,
    const std::vector<std::string>& admin_down_on_peer_interfaces,
    absl::Duration test_duration = kLongTestDuration) {
  ASSERT_THAT(result_response.per_port_responses(),
              SizeIs(bert_request.per_port_requests_size()));
  for (unsigned idx = 0; idx < result_response.per_port_responses_size();
       ++idx) {
    // Extract interface name from OC interface path.
    ASSERT_OK_AND_ASSIGN(
        const std::string interface_name,
        GetInterfaceNameFromOcInterfacePath(
            result_response.per_port_responses(idx).interface()));
    LOG(INFO) << "Verifying result for interface: " << interface_name;
    SCOPED_TRACE(absl::Substitute("Interface: $0", interface_name));
    // Check if interface is part of list where admin state was disabled.
    if (IsInterfaceInList(interface_name, admin_down_interfaces) ||
        IsInterfaceInList(interface_name, admin_down_on_peer_interfaces)) {
      // Verify BERT failure.
      EXPECT_EQ(result_response.per_port_responses(idx).status(),
                gnoi::diag::BERT_STATUS_PEER_LOCK_LOST);
      continue;
    }
    // If it is normal BERT running port, verify normal SUCCESS result.
    VerifyBertResultForSuccess(
        result_response.per_port_responses(idx),
        bert_request.bert_operation_id(),
        bert_request.per_port_requests(idx).interface(),
        bert_request.per_port_requests(idx).prbs_polynomial(), test_duration);
  }
}

gnoi::diag::GetBERTResultRequest GetBertResultRequestFromStartRequest(
    const gnoi::diag::StartBERTRequest& start_request) {
  gnoi::diag::GetBERTResultRequest result_request;
  result_request.set_bert_operation_id(start_request.bert_operation_id());
  for (const auto& per_port_request : start_request.per_port_requests()) {
    *(result_request.add_per_port_requests()->mutable_interface()) =
        per_port_request.interface();
  }
  return result_request;
}

static void GetAndVerifyResultForSuccess(
    gnoi::diag::StartBERTRequest &bert_start_request_sut,
    gnoi::diag::StartBERTRequest &bert_start_request_control_switch,
    gnoi::diag::Diag::StubInterface &sut_diag_stub,
    thinkit::ControlDevice &control_device, absl::Duration test_duration) {
  LOG(INFO) << "Verify BERT results on SUT interfaces.";
  grpc::ClientContext context;
  gnoi::diag::GetBERTResultResponse bert_result_response_sut;
  ASSERT_OK(sut_diag_stub.GetBERTResult(
      &context, GetBertResultRequestFromStartRequest(bert_start_request_sut),
      &bert_result_response_sut));

  std::vector<std::string> admin_down_interfaces = {};
  ASSERT_NO_FATAL_FAILURE(GetAndVerifyBertResultsWithAdminDownInterfaces(
      bert_start_request_sut, bert_result_response_sut, admin_down_interfaces,
      admin_down_interfaces, test_duration));

  LOG(INFO) << "Verify BERT results on control switch interfaces.";
  ASSERT_OK_AND_ASSIGN(
      gnoi::diag::GetBERTResultResponse bert_result_response_control_switch,
      control_device.GetBERTResult(GetBertResultRequestFromStartRequest(
          bert_start_request_control_switch)));
  ASSERT_NO_FATAL_FAILURE(GetAndVerifyBertResultsWithAdminDownInterfaces(
      bert_start_request_control_switch, bert_result_response_control_switch,
      admin_down_interfaces, admin_down_interfaces, test_duration));
}

void VerifyOperStatusOnSetOfSutInterfaces(gnmi::gNMI::StubInterface& gnmi_stub,
                                          std::vector<std::string>& interfaces,
                                          absl::string_view oper_status) {
  LOG(INFO) << "Verifying operational state " << oper_status
            << " on interfaces.";
  ASSERT_OK_AND_ASSIGN(auto interface_to_oper_status_map,
                       pins_test::GetInterfaceToOperStatusMapOverGnmi(
                           gnmi_stub, /*timeout=*/absl::Seconds(60)));
  for (const std::string& interface : interfaces) {
    SCOPED_TRACE(absl::StrCat("Interface: ", interface));
    EXPECT_NE(interface_to_oper_status_map.count(interface), 0);
    EXPECT_EQ(interface_to_oper_status_map[interface], oper_status);
  }
}

absl::Status ValidatePortsUp(
    thinkit::Switch& sut, thinkit::ControlDevice& control_device,
    const std::vector<std::string>& sut_interfaces,
    const std::vector<std::string>& control_device_interfaces) {
  absl::Status sut_ports_up_status =
      pins_test::PortsUp(sut, absl::Span<const std::string>(sut_interfaces));
  absl::Status control_switch_ports_up_status = control_device.ValidatePortsUp(
      absl::Span<const std::string>(control_device_interfaces));

  if (sut_ports_up_status.ok() && control_switch_ports_up_status.ok()) {
    return absl::OkStatus();
  }

  EXPECT_OK(sut_ports_up_status);
  EXPECT_OK(control_switch_ports_up_status);
  return absl::InternalError("PortsUp validation failed.");
}

std::vector<std::string> SelectNInterfacesFromList(
    int port_count_to_select, std::vector<std::string> interfaces) {
  if (interfaces.size() < port_count_to_select) {
    return std::vector<std::string>();
  }
  std::shuffle(interfaces.begin(), interfaces.end(), absl::BitGen());
  interfaces.resize(port_count_to_select);
  return interfaces;
}

bool IsListPartOfInterfaceList(const std::vector<std::string>& list,
                               const std::vector<std::string>& interface_list) {
  for (const std::string& interface : list) {
    if (IsInterfaceInList(interface, interface_list) == false) {
      return false;
    }
  }
  return true;
}

static absl::Status WaitForGnoiToBeUnavailable(
    gnoi::system::System::StubInterface& gnoi_system_stub) {
  absl::Time start_time = absl::Now();
  constexpr absl::Duration kFasterPoll = absl::Seconds(2);

  // Poll using Time() RPC to check if target is available: Time() is typically
  // used to test if a target is actually responding.
  while (absl::Now() < (start_time + kNsfActiveTimeout)) {
    absl::SleepFor(kFasterPoll);
    grpc::ClientContext context;
    gnoi::system::TimeRequest request;
    gnoi::system::TimeResponse response;

    // Invoke the RPC.
    auto status = gnoi_system_stub.Time(&context, request, &response);

    if (gutil::GrpcStatusToAbslStatus(status).code() ==
        absl::StatusCode::kUnavailable) {
      return absl::OkStatus();
    }
  }

  return absl::DeadlineExceededError("Timed-out to get GNOI unavailable.");
}

static void AddStartBertRequestForLink(
    gnoi::diag::StartBERTRequest *bert_request_sut,
    gnoi::diag::StartBERTRequest *bert_request_control_switch,
    absl::string_view sut_interface, absl::string_view control_switch_interface,
    absl::string_view op_id) {
  bert_request_sut->set_bert_operation_id(op_id);
  *(bert_request_sut->add_per_port_requests()) =
      gutil::ParseProtoOrDie<gnoi::diag::StartBERTRequest::PerPortRequest>(
          BuildPerPortStartBertRequest(sut_interface));
  bert_request_control_switch->set_bert_operation_id(op_id);
  *(bert_request_control_switch->add_per_port_requests()) =
      gutil::ParseProtoOrDie<gnoi::diag::StartBERTRequest::PerPortRequest>(
          BuildPerPortStartBertRequest(control_switch_interface));
}

static void
StartBertOnLink(gnoi::diag::StartBERTRequest &bert_request_sut,
                gnoi::diag::StartBERTRequest &bert_request_control_switch,
                gnoi::diag::Diag::StubInterface &sut_diag_stub,
                thinkit::ControlDevice &control_device) {
  LOG(INFO) << "Sending StartBERT request on SUT:";
  ASSERT_NO_FATAL_FAILURE(
      SendStartBertRequestSuccessfullyOnSut(bert_request_sut, sut_diag_stub));

  LOG(INFO) << "Sending StartBERT request on control switch:";
  ASSERT_NO_FATAL_FAILURE(SendStartBertRequestSuccessfullyOnControlSwitch(
      bert_request_control_switch, control_device));
}

// Get max poll count for polling to get BERT completion result.
static int GetMaxPollCount(absl::Time start_time) {
  return 1 + static_cast<int>((kDelayDuration + kWaitTime + kTestDuration -
                               (absl::Now() - start_time) - absl::Seconds(1)) /
                              kPollInterval);
}

// Test StartBERT with invalid request parameters.
TEST_P(BertTest, StartBertFailsIfRequestParametersInvalid) {
  ASSERT_NO_FATAL_FAILURE(
      InitializeTestEnvironment("c1dcb1cc-4806-45cc-8f8a-676beafde103"));

  // Test requires one SUT interface.
  if (sut_interfaces_.empty()) {
    GTEST_SKIP() << "No SUT interfaces to test";
  }
  thinkit::Switch& sut = generic_testbed_->Sut();
  ASSERT_OK(
      pins_test::PortsUp(sut, absl::Span<const std::string>(sut_interfaces_)));

  // Select one operational state "up" port.
  std::string interface = absl::GetFlag(FLAGS_interface);
  if (!interface.empty()) {
    // Verify that provided interfaces are part of SUT's UP interfaces.
    ASSERT_TRUE(IsInterfaceInList(interface, sut_interfaces_))
        << "SUT test interface selected for test: "
        << interface << "./n UP interfaces on SUT: "
        << absl::StrJoin(sut_interfaces_, ",");
  } else {
    sut_test_interfaces_ = SelectNInterfacesFromList(1, sut_interfaces_);
    interface = sut_test_interfaces_[0];
  }
  LOG(INFO) << "Selected interface: "
            << interface << ". To repeat the test with same interface, use "
            << "--test_arg=--interface=" << interface << " in test arguments.";

  gnoi::diag::StartBERTRequest valid_request;
  // Create the BERT request.
  valid_request.set_bert_operation_id(
      absl::StrCat("OpId-", absl::ToUnixMillis(absl::Now())));
  *(valid_request.add_per_port_requests()) =
      gutil::ParseProtoOrDie<gnoi::diag::StartBERTRequest::PerPortRequest>(
          BuildPerPortStartBertRequest(interface));
  gnoi::diag::StartBERTResponse response;

  // Case 1: BERT test duration is 0 secs.
  {
    gnoi::diag::StartBERTRequest too_short_time_request = valid_request;
    too_short_time_request.mutable_per_port_requests(0)
        ->set_test_duration_in_secs(0);
    grpc::ClientContext context;
    LOG(INFO) << "Sending StartBERT request: "
              << too_short_time_request.ShortDebugString();
    EXPECT_THAT(gutil::GrpcStatusToAbslStatus(sut_diag_stub_->StartBERT(
                    &context, too_short_time_request, &response)),
                gutil::StatusIs(absl::StatusCode::kInvalidArgument,
                                HasSubstr("is too short")));
  }

  // Case 2: BERT test duration is more than 24 hours: (24 hours + 1 sec).
  {
    gnoi::diag::StartBERTRequest too_long_time_request = valid_request;
    too_long_time_request.mutable_per_port_requests(0)
        ->set_test_duration_in_secs(
            ToInt64Seconds(absl::Hours(24) + absl::Seconds(1)));
    response.Clear();
    grpc::ClientContext context;
    LOG(INFO) << "Sending StartBERT request: "
              << too_long_time_request.ShortDebugString();
    EXPECT_THAT(gutil::GrpcStatusToAbslStatus(sut_diag_stub_->StartBERT(
                    &context, too_long_time_request, &response)),
                gutil::StatusIs(absl::StatusCode::kInvalidArgument,
                                HasSubstr("is too long")));
  }

  // Case 3: Invalid PRBS polynomial order.
  {
    gnoi::diag::StartBERTRequest unset_prbs_polynomial_request = valid_request;
    unset_prbs_polynomial_request.mutable_per_port_requests(0)
        ->clear_prbs_polynomial();
    response.Clear();
    grpc::ClientContext context;
    LOG(INFO) << "Sending StartBERT request: "
              << unset_prbs_polynomial_request.ShortDebugString();
    EXPECT_THAT(gutil::GrpcStatusToAbslStatus(sut_diag_stub_->StartBERT(
                    &context, unset_prbs_polynomial_request, &response)),
                gutil::StatusIs(absl::StatusCode::kInvalidArgument,
                                HasSubstr("PRBS polynomial is not set")));
  }

  // Case 4: Invalid interface.
  {
    gnoi::diag::StartBERTRequest invalid_interface_request = valid_request;
    *(invalid_interface_request.mutable_per_port_requests(0)
          ->mutable_interface()) =
        gutil::ParseProtoOrDie<gnoi::types::Path>(
            BuildOpenConfigInterface("InvalidPort"));
    response.Clear();
    grpc::ClientContext context;
    LOG(INFO) << "Sending StartBERT request: "
              << invalid_interface_request.ShortDebugString();
    EXPECT_THAT(gutil::GrpcStatusToAbslStatus(sut_diag_stub_->StartBERT(
                    &context, invalid_interface_request, &response)),
                gutil::StatusIs(absl::StatusCode::kInvalidArgument,
                                HasSubstr("Interface is invalid")));
  }
  ASSERT_OK(
      pins_test::PortsUp(sut, absl::Span<const std::string>(sut_interfaces_)));
}

// Test StopBERT RPC with invalid argument in the request.
// 1) If StopBERT RPC is requested on an invalid port, RPC should fail.
// 2) If StopBERT RPC is requested on a port that is not running BERT, RPC
// should fail.
TEST_P(BertTest, StopBertfailsIfRequestParametersInvalid) {
  ASSERT_NO_FATAL_FAILURE(
      InitializeTestEnvironment("224db9cf-c709-486d-a0d3-6ab64c1a1e1f"));

  // Test requires one SUT interface.
  if (sut_interfaces_.empty()) {
    GTEST_SKIP() << "No SUT interfaces to test";
  }
  thinkit::Switch& sut = generic_testbed_->Sut();
  ASSERT_OK(
      pins_test::PortsUp(sut, absl::Span<const std::string>(sut_interfaces_)));

  // Request StopBERT RPC on an invalid port, RPC should fail.
  {
    gnoi::diag::StopBERTRequest request;
    request.set_bert_operation_id(
        absl::StrCat("OpId-", absl::ToUnixMillis(absl::Now())));
    *(request.add_per_port_requests()->mutable_interface()) =
        gutil::ParseProtoOrDie<gnoi::types::Path>(
            BuildOpenConfigInterface("invalidPort"));

    gnoi::diag::StopBERTResponse response;
    grpc::ClientContext context;
    LOG(INFO) << "Sending StopBERT request: " << request.ShortDebugString();
    EXPECT_THAT(
        gutil::GrpcStatusToAbslStatus(
            sut_diag_stub_->StopBERT(&context, request, &response)),
        gutil::StatusIs(
            absl::StatusCode::kInvalidArgument,
            AllOf(HasSubstr("Interface is invalid"),
                  HasSubstr("Operation ID is not found on interface"))));
  }

  // Request StopBERT RPC on a port that is not running BERT, RPC should fail.
  {
    // Select one operational state "up" port.
    std::string interface = absl::GetFlag(FLAGS_interface);
    if (!interface.empty()) {
      // Verify that provided interfaces are part of SUT's UP interfaces.
      ASSERT_TRUE(IsInterfaceInList(interface, sut_interfaces_))
          << "SUT test interface selected for test: "
          << interface << "./n UP interfaces on SUT: "
          << absl::StrJoin(sut_interfaces_, ",");
    } else {
      sut_test_interfaces_ = SelectNInterfacesFromList(1, sut_interfaces_);
      interface = sut_test_interfaces_[0];
    }
    LOG(INFO) << "Selected interface: "
              << interface << ". To repeat the test with same interface, use "
              << "--test_arg=--interface="
              << interface << " in test arguments.";

    gnoi::diag::StopBERTRequest request;
    request.set_bert_operation_id(
        absl::StrCat("OpId-", absl::ToUnixMillis(absl::Now())));
    *(request.add_per_port_requests()->mutable_interface()) =
        gutil::ParseProtoOrDie<gnoi::types::Path>(
            BuildOpenConfigInterface(interface));
    gnoi::diag::StopBERTResponse response;
    grpc::ClientContext context;
    LOG(INFO) << "Sending StopBERT request: " << request.ShortDebugString();
    EXPECT_THAT(
        gutil::GrpcStatusToAbslStatus(
            sut_diag_stub_->StopBERT(&context, request, &response)),
        gutil::StatusIs(absl::StatusCode::kInvalidArgument,
                        HasSubstr("Operation ID is not found on interface")));
  }
  ASSERT_OK(
      pins_test::PortsUp(sut, absl::Span<const std::string>(sut_interfaces_)));
}

// Test GetBERTResult RPC with invalid argument in the request.
// 1) If GetBERTResult RPC is requested on an invalid port, RPC should fail.
// 2) If GetBERTResult RPC is requested on a port that never ran BERT before,
// RPC should fail.
TEST_P(BertTest, GetBertResultFailsIfRequestParametersInvalid) {
  ASSERT_NO_FATAL_FAILURE(
      InitializeTestEnvironment("4f837d7a-ab44-4694-9ca9-399d576757f4"));

  // Test requires one SUT interface.
  if (sut_interfaces_.empty()) {
    GTEST_SKIP() << "No SUT interfaces to test";
  }
  thinkit::Switch& sut = generic_testbed_->Sut();
  ASSERT_OK(
      pins_test::PortsUp(sut, absl::Span<const std::string>(sut_interfaces_)));

  // Request GetBERTResult RPC on an invalid port, RPC should fail.
  {
    gnoi::diag::GetBERTResultRequest result_request;
    result_request.set_bert_operation_id(
        absl::StrCat("OpId-", absl::ToUnixMillis(absl::Now())));
    *(result_request.add_per_port_requests()->mutable_interface()) =
        gutil::ParseProtoOrDie<gnoi::types::Path>(
            BuildOpenConfigInterface("InvalidPort"));

    gnoi::diag::GetBERTResultResponse result_response;
    grpc::ClientContext context;
    LOG(INFO) << "Sending GetBERTResult request: "
              << result_request.ShortDebugString();
    EXPECT_THAT(gutil::GrpcStatusToAbslStatus(sut_diag_stub_->GetBERTResult(
                    &context, result_request, &result_response)),
                gutil::StatusIs(
                    absl::StatusCode::kInvalidArgument,
                    AllOf(HasSubstr("Interface"), HasSubstr("is not valid"))));
  }
  // Request GetBERTResult RPC on a port that never ran BERT before, RPC should
  // fail.
  {
    // Select one operational state "up" port.
    std::string interface = absl::GetFlag(FLAGS_interface);
    if (!interface.empty()) {
      // Verify that provided interfaces are part of SUT's UP interfaces.
      ASSERT_TRUE(IsInterfaceInList(interface, sut_interfaces_))
          << "SUT test interface selected for test: "
          << interface << "./n UP interfaces on SUT: "
          << absl::StrJoin(sut_interfaces_, ",");
    } else {
      sut_test_interfaces_ = SelectNInterfacesFromList(1, sut_interfaces_);
      interface = sut_test_interfaces_[0];
    }
    LOG(INFO) << "Selected interface: "
              << interface << ". To repeat the test with same interface, use "
              << "--test_arg=--interface="
              << interface << " in test arguments.";

    gnoi::diag::GetBERTResultRequest result_request;
    result_request.set_bert_operation_id(
        absl::StrCat("OpId-", absl::ToUnixMillis(absl::Now())));
    *(result_request.add_per_port_requests()->mutable_interface()) =
        gutil::ParseProtoOrDie<gnoi::types::Path>(
            BuildOpenConfigInterface(interface));

    gnoi::diag::GetBERTResultResponse result_response;
    grpc::ClientContext context;
    LOG(INFO) << "Sending GetBERTResult request: "
              << result_request.ShortDebugString();
    EXPECT_THAT(gutil::GrpcStatusToAbslStatus(sut_diag_stub_->GetBERTResult(
                    &context, result_request, &result_response)),
                gutil::StatusIs(absl::StatusCode::kInvalidArgument,
                                AllOf(HasSubstr("Result is not found for intf"),
                                      HasSubstr(interface))));
  }
  ASSERT_OK(
      pins_test::PortsUp(sut, absl::Span<const std::string>(sut_interfaces_)));
}

// Test StartBERT fails if peer port is not running BERT.
TEST_P(BertTest, StartBertfailsIfPeerPortNotRunningBert) {
  ASSERT_NO_FATAL_FAILURE(
      InitializeTestEnvironment("37e48922-0616-4d16-8fd3-975897491956"));

  // Test requires one SUT interface.
  if (sut_interfaces_.empty()) {
    GTEST_SKIP() << "No SUT interfaces to test";
  }
  thinkit::Switch& sut = generic_testbed_->Sut();
  ASSERT_OK(
      pins_test::PortsUp(sut, absl::Span<const std::string>(sut_interfaces_)));

  // Select one operational state "up" port.
  std::string interface = absl::GetFlag(FLAGS_interface);
  if (!interface.empty()) {
    // Verify that provided interfaces are part of SUT's UP interfaces.
    ASSERT_TRUE(IsInterfaceInList(interface, sut_interfaces_))
        << "SUT test interface selected for test: "
        << interface << "./n UP interfaces on SUT: "
        << absl::StrJoin(sut_interfaces_, ",");
  } else {
    sut_test_interfaces_ = SelectNInterfacesFromList(1, sut_interfaces_);
    interface = sut_test_interfaces_[0];
  }
  LOG(INFO) << "Selected interface: "
            << interface << ". To repeat the test with same interface, use "
            << "--test_arg=--interface=" << interface << " in test arguments.";

  gnoi::diag::StartBERTRequest bert_request;
  // Create the BERT request.
  bert_request.set_bert_operation_id(
      absl::StrCat("OpId-", absl::ToUnixMillis(absl::Now())));
  *(bert_request.add_per_port_requests()) =
      gutil::ParseProtoOrDie<gnoi::diag::StartBERTRequest::PerPortRequest>(
          BuildPerPortStartBertRequest(interface));

  LOG(INFO) << "Sending StartBERT request on SUT:";
  ASSERT_NO_FATAL_FAILURE(
      SendStartBertRequestSuccessfullyOnSut(bert_request, *sut_diag_stub_));

  // Poll for allowed BERT delay duration.
  int max_poll_count =
      ceil(ToInt64Seconds(kDelayDuration) / ToInt64Seconds(kPollInterval));
  bool poll_timeout = true;
  for (int count = 0; count < max_poll_count; ++count) {
    absl::SleepFor(kPollInterval);
    ASSERT_OK_AND_ASSIGN(
        pins_test::OperStatus oper_status,
        pins_test::GetInterfaceOperStatusOverGnmi(*sut_gnmi_stub_, interface));
    // If port is "UP" and no longer in "TESTING" oper state, BERT has completed
    // on the port and full BERT result is ready for read.
    if (oper_status == pins_test::OperStatus::kUp) {
      poll_timeout = false;
      break;
    }
  }

  if (poll_timeout == true) {
    LOG(WARNING)
        << "BERT is not completed on the port in maximum allowed time.";
  }

  gnoi::diag::GetBERTResultRequest result_request;
  result_request.set_bert_operation_id(bert_request.bert_operation_id());
  *(result_request.add_per_port_requests()->mutable_interface()) =
      bert_request.per_port_requests(0).interface();
  gnoi::diag::GetBERTResultResponse result_response;
  grpc::ClientContext result_context;
  EXPECT_OK(sut_diag_stub_->GetBERTResult(&result_context, result_request,
                                          &result_response));
  LOG(INFO) << "Result: " << result_response.ShortDebugString();
  ASSERT_OK(
      pins_test::PortsUp(sut, absl::Span<const std::string>(sut_interfaces_)));
  // Verify the response.
  ASSERT_THAT(result_response.per_port_responses(), SizeIs(1));
  EXPECT_EQ(result_response.per_port_responses(0).status(),
            gnoi::diag::BERT_STATUS_PEER_LOCK_FAILURE);
}

// Since BERT test is a time consuming test, we decided to combine few tests
// together to save BERT test run time. This test runs and verifies following
// cases:
// 1) BERT runs successfully on 2 ports.
// 2) While BERT is running on ports, another attempt to start the BERT on these
// same ports should fail.
// 3) Operation id that was used earlier to start the BERT test will fail to
// start BERT if used again.
TEST_P(BertTest, StartBertSucceeds) {
  ASSERT_NO_FATAL_FAILURE(
      InitializeTestEnvironment("b31a796a-d078-4d45-b785-f09ec598e05a"));

  // Test requires 2 SUT interfaces.
  constexpr int kNumInterfaces = 2;
  if (sut_interfaces_.size() < kNumInterfaces) {
    GTEST_SKIP() << "Need at least " << kNumInterfaces
                 << " SUT interfaces to test but got: "
                 << sut_interfaces_.size();
  }
  thinkit::Switch& sut = generic_testbed_->Sut();
  thinkit::ControlDevice& control_device = generic_testbed_->ControlDevice();
  ASSERT_OK(
      ValidatePortsUp(sut, control_device, sut_interfaces_, peer_interfaces_));

  // Select kNumInterfaces operational state "up" ports.
  sut_test_interfaces_ = absl::GetFlag(FLAGS_interfaces);
  if (!sut_test_interfaces_.empty()) {
    // Verify that provided interfaces are part of SUT's UP interfaces.
    ASSERT_TRUE(
        IsListPartOfInterfaceList(sut_test_interfaces_, sut_interfaces_))
        << "SUT test infaces selected for test: "
        << absl::StrJoin(sut_test_interfaces_, ",")
        << "./n UP interfaces on SUT: " << absl::StrJoin(sut_interfaces_, ",");
  } else {
    sut_test_interfaces_ =
        SelectNInterfacesFromList(kNumInterfaces, sut_interfaces_);
  }
  ASSERT_THAT(sut_test_interfaces_, SizeIs(kNumInterfaces));
  // Get peer test interfaces corresponding to SUT test interfaces.
  ASSERT_OK_AND_ASSIGN(peer_test_interfaces_,
                       GetPeerInterfacesForSutInterfaces(sut_test_interfaces_));
  LOG(INFO) << "Selected {SUT, control_device} interfaces: ";
  for (size_t idx = 0; idx < sut_test_interfaces_.size(); ++idx) {
    LOG(INFO) << "{" << sut_test_interfaces_[idx] << ", "
              << peer_test_interfaces_[idx] << "}, ";
  }

  LOG(INFO) << "To repeat the test with same SUT interfaces, "
            << "use --test_arg=--interfaces="
            << absl::StrJoin(sut_test_interfaces_, ",")
            << " in test arguments.";

  gnoi::diag::StartBERTRequest bert_request_sut;
  gnoi::diag::StartBERTRequest bert_request_control_switch;
  std::string op_id = absl::StrCat("OpId-", absl::ToUnixMillis(absl::Now()));
  // Create the BERT request for SUT.
  bert_request_sut.set_bert_operation_id(op_id);
  for (const std::string& interface : sut_test_interfaces_) {
    *(bert_request_sut.add_per_port_requests()) =
        gutil::ParseProtoOrDie<gnoi::diag::StartBERTRequest::PerPortRequest>(
            BuildPerPortStartBertRequest(interface));
  }

  // Create the BERT request for control switch.
  bert_request_control_switch.set_bert_operation_id(op_id);
  for (const std::string& interface : peer_test_interfaces_) {
    *(bert_request_control_switch.add_per_port_requests()) =
        gutil::ParseProtoOrDie<gnoi::diag::StartBERTRequest::PerPortRequest>(
            BuildPerPortStartBertRequest(interface));
  }

  // Request StartBert on the SUT switch.
  LOG(INFO) << "Sending StartBERT request on SUT:";
  ASSERT_NO_FATAL_FAILURE(
      SendStartBertRequestSuccessfullyOnSut(bert_request_sut, *sut_diag_stub_));

  // Request StartBert on the control switch.
  LOG(INFO) << "Sending StartBERT request on control switch:";
  ASSERT_NO_FATAL_FAILURE(SendStartBertRequestSuccessfullyOnControlSwitch(
      bert_request_control_switch, control_device));

  // Get start timestamp.
  absl::Time start_time = absl::Now();
  // Wait before reading the oper status.
  absl::SleepFor(kWaitToReadOperStatus);

  // Verify TESTING operational state on SUT ports running linkqual.
  ASSERT_NO_FATAL_FAILURE(VerifyOperStatusOnSetOfSutInterfaces(
      *sut_gnmi_stub_, sut_test_interfaces_, /*oper_status=*/"TESTING"));

  // Request another StartBert on the same ports on SUT and it should fail.
  {
    gnoi::diag::StartBERTRequest second_bert_request = bert_request_sut;
    second_bert_request.set_bert_operation_id(
        absl::StrCat("OpId-", absl::ToUnixMillis(absl::Now())));
    // Request StartBert on the SUT switch.
    LOG(INFO) << "Sending second StartBERT request on SUT:";
    ASSERT_NO_FATAL_FAILURE(SendStartBertRequestSuccessfullyOnSut(
        second_bert_request, *sut_diag_stub_));

    // Wait some time before querying the result.
    absl::SleepFor(kWaitTime);
    gnoi::diag::GetBERTResultRequest result_request =
        GetBertResultRequestFromStartRequest(second_bert_request);
    gnoi::diag::GetBERTResultResponse result_response;
    grpc::ClientContext result_context;
    EXPECT_OK(sut_diag_stub_->GetBERTResult(&result_context, result_request,
                                            &result_response));
    LOG(INFO) << "Result: " << result_response.ShortDebugString();
    EXPECT_THAT(result_response.per_port_responses(),
                SizeIs(sut_test_interfaces_.size()));
    for (const auto& per_port_result : result_response.per_port_responses()) {
      EXPECT_EQ(per_port_result.status(),
                gnoi::diag::BERT_STATUS_PORT_ALREADY_IN_BERT)
          << "Port result: " << per_port_result.ShortDebugString();
    }
  }

  // Wait for BERT to finish on test interfaces.
  int max_poll_count = 1 + (kDelayDuration + kWaitTime + kTestDuration -
                            (absl::Now() - start_time) - absl::Seconds(1)) /
                               kPollInterval;

  ASSERT_NO_FATAL_FAILURE(WaitForBertToCompleteOnInterfaces(
      *sut_gnmi_stub_, sut_test_interfaces_, control_device,
      GetBertResultRequestFromStartRequest(bert_request_control_switch),
      max_poll_count));

  // Get the BERT result from the SUT.
  {
    gnoi::diag::GetBERTResultRequest result_request_sut =
        GetBertResultRequestFromStartRequest(bert_request_sut);
    gnoi::diag::GetBERTResultResponse result_response;
    grpc::ClientContext result_context;
    EXPECT_OK(sut_diag_stub_->GetBERTResult(&result_context, result_request_sut,
                                            &result_response));
    LOG(INFO) << "SUT BERT result: " << result_response.ShortDebugString();
    ASSERT_THAT(result_response.per_port_responses(),
                SizeIs(bert_request_sut.per_port_requests_size()));
    for (int idx = 0; idx < result_response.per_port_responses_size(); ++idx) {
      VerifyBertResultForSuccess(
          result_response.per_port_responses(idx),
          bert_request_sut.bert_operation_id(),
          bert_request_sut.per_port_requests(idx).interface(),
          bert_request_sut.per_port_requests(idx).prbs_polynomial());
    }
  }

  // Get the BERT result from the control switch.
  {
    gnoi::diag::GetBERTResultRequest result_request_control_switch =
        GetBertResultRequestFromStartRequest(bert_request_control_switch);
    ASSERT_OK_AND_ASSIGN(
        gnoi::diag::GetBERTResultResponse result_response,
        control_device.GetBERTResult(result_request_control_switch));
    LOG(INFO) << "Control switch BERT result: "
              << result_response.ShortDebugString();
    ASSERT_THAT(result_response.per_port_responses(),
                SizeIs(bert_request_control_switch.per_port_requests_size()));
    for (int idx = 0; idx < result_response.per_port_responses_size(); ++idx) {
      VerifyBertResultForSuccess(
          result_response.per_port_responses(idx),
          bert_request_control_switch.bert_operation_id(),
          bert_request_control_switch.per_port_requests(idx).interface(),
          bert_request_control_switch.per_port_requests(idx).prbs_polynomial());
    }
  }

  // Request another StartBert on the SUT with just used operation id, it should
  // fail.
  {
    gnoi::diag::StartBERTResponse bert_response;
    grpc::ClientContext context;
    LOG(INFO) << "Sending StartBERT request: "
              << bert_request_sut.ShortDebugString();
    EXPECT_THAT(
        gutil::GrpcStatusToAbslStatus(sut_diag_stub_->StartBERT(
            &context, bert_request_sut, &bert_response)),
        gutil::StatusIs(absl::StatusCode::kInvalidArgument,
                        AllOf(HasSubstr("Invalid request"),
                              HasSubstr(bert_request_sut.bert_operation_id()),
                              HasSubstr("exists"))))
        << "Response: " << bert_response.ShortDebugString();
  }

  ASSERT_OK(
      ValidatePortsUp(sut, control_device, sut_interfaces_, peer_interfaces_));
}

// Prune the interfaces that cannot allow disabling each lane independently.
// These interfaces are not supported for BERT.
// TODO: Add code to remove interfaces from sut_test_interfaces that are not applicable for BERT.
absl::Status PruneUnsupportedInterfaces(
    std::vector<std::string>& sut_test_interfaces,
    gnmi::gNMI::StubInterface& sut_gnmi_stub) {
  return absl::OkStatus();
}

// Runs the BERT test on current maximum allowed number of interfaces. During
// the BERT run:
// 1) Disable admin state of few ports on SUT,
// 2) Disable admin state of few ports on control switch,
// This helps us verify a mix of operation during BERT - unexpected software or
// hardware errors.
TEST_P(BertTest, RunBertOnMaximumAllowedPorts) {
  ASSERT_NO_FATAL_FAILURE(
      InitializeTestEnvironment("ce526e97-2a62-4044-9dce-8fc74b232e4b"));

  // For this test, we need at least 4 SUT interfaces.
  if (sut_interfaces_.size() < 4) {
    GTEST_SKIP() << "Need at least 4 SUT interfaces to test but got: "
                 << sut_interfaces_.size();
  }
  thinkit::Switch& sut = generic_testbed_->Sut();
  thinkit::ControlDevice& control_device = generic_testbed_->ControlDevice();
  ASSERT_OK(
      ValidatePortsUp(sut, control_device, sut_interfaces_, peer_interfaces_));

  // Get all the interfaces that are operational status "UP".
  sut_test_interfaces_ = sut_interfaces_;
  ASSERT_OK(PruneUnsupportedInterfaces(sut_test_interfaces_, *sut_gnmi_stub_));
  // Resize the interface list if UP ports are more than max number of allowed
  // ports.
  if (sut_test_interfaces_.size() > kMaxAllowedInterfacesToRunBert) {
    sut_test_interfaces_.resize(kMaxAllowedInterfacesToRunBert);
  }

  // Select 'N' ports on control switch and 'N' ports on SUT for admin down.
  int num_interfaces_to_disable = 1 + (sut_test_interfaces_.size() / 16);
  // Seed the std::rand().
  LOG(INFO) << "Seeding pseudo-random number generator with seed: "
            << absl::GetFlag(FLAGS_idx_seed);
  // Select SUT interfaces in the range [0..interfaces/2).
  std::vector<std::string> sut_interfaces_for_admin_down;
  std::sample(sut_test_interfaces_.begin(),
              sut_test_interfaces_.begin() + sut_test_interfaces_.size() / 2,
              std::back_inserter(sut_interfaces_for_admin_down),
              num_interfaces_to_disable,
              std::mt19937(absl::GetFlag(FLAGS_idx_seed)));
  // Get control switch interfaces connected to the admin down SUT interfaces.
  ASSERT_OK_AND_ASSIGN(
      std::vector<std::string> control_switch_interfaces_peer_admin_down,
      GetPeerInterfacesForSutInterfaces(sut_interfaces_for_admin_down));
  // Select SUT interfaces whose peer interfaces on control switch will be admin
  // disabled in the range
  // [sut_test_interfaces_/2..sut_test_interfaces_.size()).
  std::vector<std::string> sut_interfaces_peer_admin_down_candidates(
      sut_test_interfaces_.begin() + sut_test_interfaces_.size() / 2,
      sut_test_interfaces_.end());
  ASSERT_OK_AND_ASSIGN(std::vector<std::string>
                           control_switch_interfaces_for_admin_down_candidates,
                       GetPeerInterfacesForSutInterfaces(
                           sut_interfaces_peer_admin_down_candidates));
  ASSERT_OK_AND_ASSIGN(
      std::vector<std::string>
          control_switch_interfaces_for_admin_down_filtered_candidates,
      control_device.FilterCollateralDownOnAdminDownInterfaces(
          control_switch_interfaces_for_admin_down_candidates));
  std::vector<std::string> control_switch_interfaces_for_admin_down;
  std::sample(
      control_switch_interfaces_for_admin_down_filtered_candidates.begin(),
      control_switch_interfaces_for_admin_down_filtered_candidates.end(),
      std::back_inserter(control_switch_interfaces_for_admin_down),
      num_interfaces_to_disable, std::mt19937(absl::GetFlag(FLAGS_idx_seed)));
  ASSERT_OK_AND_ASSIGN(std::vector<std::string> sut_interfaces_peer_admin_down,
                       GetSutInterfacesForControlInterfaces(
                           control_switch_interfaces_for_admin_down));

  LOG(INFO) << "Starting BERT on " << sut_test_interfaces_.size()
            << " {SUT, control_device} links: ";
  for (const std::string& interface : sut_test_interfaces_) {
    LOG(INFO) << "{" << interface << ", "
              << sut_to_peer_interface_mapping_[interface] << "}, ";
  }
  LOG(INFO) << "Interfaces selected on SUT for admin down: "
            << absl::StrJoin(sut_interfaces_for_admin_down, ",");
  LOG(INFO) << "Interfaces selected on control switch for admin down: "
            << absl::StrJoin(control_switch_interfaces_for_admin_down, ",");

  gnoi::diag::StartBERTRequest bert_request_sut;
  gnoi::diag::StartBERTRequest bert_request_control_switch;
  // Create the BERT request for SUT and control switch.
  std::string op_id = absl::StrCat("OpId-", absl::ToUnixMillis(absl::Now()));
  bert_request_sut.set_bert_operation_id(op_id);
  bert_request_control_switch.set_bert_operation_id(op_id);
  for (const std::string& interface : sut_test_interfaces_) {
    // Since during test ports will be brought down, run test for longer
    // duration.
    *(bert_request_sut.add_per_port_requests()) =
        gutil::ParseProtoOrDie<gnoi::diag::StartBERTRequest::PerPortRequest>(
            BuildPerPortStartBertRequest(interface, kLongTestDuration));
    const std::string peer_interface =
        sut_to_peer_interface_mapping_[interface];
    *(bert_request_control_switch.add_per_port_requests()) =
        gutil::ParseProtoOrDie<gnoi::diag::StartBERTRequest::PerPortRequest>(
            BuildPerPortStartBertRequest(peer_interface, kLongTestDuration));
  }

  // Request StartBert on the SUT switch.
  LOG(INFO) << "Sending StartBERT request on SUT:";
  ASSERT_NO_FATAL_FAILURE(
      SendStartBertRequestSuccessfullyOnSut(bert_request_sut, *sut_diag_stub_));

  // Request StartBert on the control switch.
  LOG(INFO) << "Sending StartBERT request on control switch:";
  ASSERT_NO_FATAL_FAILURE(SendStartBertRequestSuccessfullyOnControlSwitch(
      bert_request_control_switch, control_device));

  absl::Time start_time = absl::Now();
  // Give some time to BERT to move in SYNC state.
  absl::SleepFor(absl::Seconds(90));
  ASSERT_NO_FATAL_FAILURE(CheckRunningBertAndForceAdminDown(
      *sut_diag_stub_, control_device, *sut_gnmi_stub_, op_id,
      sut_interfaces_for_admin_down, control_switch_interfaces_for_admin_down,
      sut_to_peer_interface_mapping_, control_to_peer_interface_mapping_));
  absl::Time end_time = absl::Now();

  // Wait for BERT to finish on test interfaces.
  int max_poll_count = 1 + (kDelayDuration + kWaitTime + kLongTestDuration -
                            (end_time - start_time) - absl::Seconds(1)) /
                               kPollInterval;

  ASSERT_NO_FATAL_FAILURE(WaitForBertToCompleteOnInterfaces(
      *sut_gnmi_stub_, sut_test_interfaces_, control_device,
      GetBertResultRequestFromStartRequest(bert_request_control_switch),
      max_poll_count, kLongTestDuration));

  // Get the BERT result from SUT and verify it.
  LOG(INFO) << "Verify BERT results on SUT interfaces.";
  grpc::ClientContext context;
  gnoi::diag::GetBERTResultResponse bert_response_sut;
  ASSERT_OK(sut_diag_stub_->GetBERTResult(
      &context, GetBertResultRequestFromStartRequest(bert_request_sut),
      &bert_response_sut));
  ASSERT_NO_FATAL_FAILURE(GetAndVerifyBertResultsWithAdminDownInterfaces(
      bert_request_sut, bert_response_sut, sut_interfaces_for_admin_down,
      sut_interfaces_peer_admin_down));
  // Get the BERT result from control switch and verify it.
  LOG(INFO) << "Verify BERT results on control switch interfaces.";
  ASSERT_OK_AND_ASSIGN(
      gnoi::diag::GetBERTResultResponse bert_response_control_switch,
      control_device.GetBERTResult(
          GetBertResultRequestFromStartRequest(bert_request_control_switch)));
  ASSERT_NO_FATAL_FAILURE(GetAndVerifyBertResultsWithAdminDownInterfaces(
      bert_request_control_switch, bert_response_control_switch,
      control_switch_interfaces_for_admin_down,
      control_switch_interfaces_peer_admin_down));

  // Enable admin state on SUT and control switch interfaces.
  ASSERT_NO_FATAL_FAILURE(SetAdminStateOnInterfaceList(
      *sut_gnmi_stub_, sut_interfaces_for_admin_down, kEnabledTrue));
  ASSERT_OK(control_device.SetAdminLinkState(
      control_switch_interfaces_for_admin_down, thinkit::LinkState::kUp));

  // Wait for some time before checking the port status.
  absl::SleepFor(kPortsUpWaitTime);

  ASSERT_OK(
      ValidatePortsUp(sut, control_device, sut_interfaces_, peer_interfaces_));
}

// Run BERT on a port. Issue StopBERT on the SUT port, this causes BERT to
// stop on SUT and this will cause BERT failure on control switch as control
// switch side port will lose lock with its peer port on SUT side.
TEST_P(BertTest, StopBertSucceeds) {
  ASSERT_NO_FATAL_FAILURE(
      InitializeTestEnvironment("be7b6653-51b9-4231-a438-d9589bbcb677"));

  // Test requires one SUT interface.
  if (sut_interfaces_.empty()) {
    GTEST_SKIP() << "No SUT interfaces to test";
  }
  thinkit::Switch& sut = generic_testbed_->Sut();
  thinkit::ControlDevice& control_device = generic_testbed_->ControlDevice();
  ASSERT_OK(
      ValidatePortsUp(sut, control_device, sut_interfaces_, peer_interfaces_));

  // Select one operational state "up" port.
  std::string interface = absl::GetFlag(FLAGS_interface);
  if (!interface.empty()) {
    // Verify that provided interfaces are part of SUT's UP interfaces.
    ASSERT_TRUE(IsInterfaceInList(interface, sut_interfaces_))
        << "SUT test interface selected for test: "
        << interface << "./n UP interfaces on SUT: "
        << absl::StrJoin(sut_interfaces_, ",");
  } else {
    sut_test_interfaces_ = SelectNInterfacesFromList(1, sut_interfaces_);
    interface = sut_test_interfaces_[0];
  }
  ASSERT_OK_AND_ASSIGN(peer_test_interfaces_,
                       GetPeerInterfacesForSutInterfaces(sut_test_interfaces_));
  std::string peer_interface = peer_test_interfaces_[0];
  LOG(INFO) << "Selected {SUT, control interface}: {" << interface << ", "
            << peer_interface
            << "}. To repeat the test with same SUT interface, use "
            << "--test_arg=--interface=" << interface << " in test arguments.";

  gnoi::diag::StartBERTRequest bert_request_sut;
  gnoi::diag::StartBERTRequest bert_request_control_switch;
  std::string op_id = absl::StrCat("OpId-", absl::ToUnixMillis(absl::Now()));
  // Create the BERT request.
  bert_request_sut.set_bert_operation_id(op_id);
  *(bert_request_sut.add_per_port_requests()) =
      gutil::ParseProtoOrDie<gnoi::diag::StartBERTRequest::PerPortRequest>(
          BuildPerPortStartBertRequest(interface));
  bert_request_control_switch.set_bert_operation_id(op_id);
  *(bert_request_control_switch.add_per_port_requests()) =
      gutil::ParseProtoOrDie<gnoi::diag::StartBERTRequest::PerPortRequest>(
          BuildPerPortStartBertRequest(peer_interface));

  // Request StartBert on the SUT switch.
  LOG(INFO) << "Sending StartBERT request on SUT:";
  ASSERT_NO_FATAL_FAILURE(
      SendStartBertRequestSuccessfullyOnSut(bert_request_sut, *sut_diag_stub_));

  // Request StartBert on the control switch.
  LOG(INFO) << "Sending StartBERT request on control switch:";
  ASSERT_NO_FATAL_FAILURE(SendStartBertRequestSuccessfullyOnControlSwitch(
      bert_request_control_switch, control_device));

  absl::Time start_time = absl::Now();
  // Wait before reading the oper status.
  absl::SleepFor(kWaitToReadOperStatus);

  // Verify that SUT port should be in TESTING mode now.
  {
    ASSERT_OK_AND_ASSIGN(
        pins_test::OperStatus oper_status,
        pins_test::GetInterfaceOperStatusOverGnmi(*sut_gnmi_stub_, interface));
    ASSERT_EQ(oper_status, pins_test::OperStatus::kTesting);
  }

  gnoi::diag::GetBERTResultRequest result_request_control_switch;
  result_request_control_switch.set_bert_operation_id(op_id);
  *(result_request_control_switch.add_per_port_requests()
        ->mutable_interface()) =
      bert_request_control_switch.per_port_requests(0).interface();

  // Verify control switch side BERT has acquired the lock and is running now.
  {
    int remaining_poll_count =
        1 + (kDelayDuration - absl::Seconds(1)) / kPollInterval;

    while (remaining_poll_count > 0) {
      absl::SleepFor(kPollInterval);
      gnoi::diag::GetBERTResultResponse response;
      ASSERT_OK_AND_ASSIGN(response, control_device.GetBERTResult(
                                         result_request_control_switch));
      ASSERT_THAT(response.per_port_responses(),
                  SizeIs(bert_request_control_switch.per_port_requests_size()));
      ASSERT_EQ(response.per_port_responses(0).status(),
                gnoi::diag::BERT_STATUS_OK);
      if (response.per_port_responses(0).peer_lock_established()) {
        break;
      }
      --remaining_poll_count;
    }
    // Assert if timed out to get the lock.
    ASSERT_GT(remaining_poll_count, 0);
  }

  // Request StopBERT on SUT.
  {
    gnoi::diag::StopBERTRequest stop_request;
    stop_request.set_bert_operation_id(op_id);
    *(stop_request.add_per_port_requests()->mutable_interface()) =
        bert_request_sut.per_port_requests(0).interface();
    gnoi::diag::StopBERTResponse response;
    grpc::ClientContext context;
    LOG(INFO) << "Sending StopBERT request on SUT: "
              << stop_request.ShortDebugString();
    EXPECT_OK(sut_diag_stub_->StopBERT(&context, stop_request, &response));

    // Verify response.
    ASSERT_THAT(response.per_port_responses(),
                SizeIs(stop_request.per_port_requests_size()));
    EXPECT_EQ(response.bert_operation_id(), stop_request.bert_operation_id());

    for (int idx = 0; idx < response.per_port_responses_size(); ++idx) {
      const StopBERTResponse_PerPortResponse &per_port_response =
          response.per_port_responses(idx);
      SCOPED_TRACE(absl::StrCat("Verifying StopBERT port response: ",
                                per_port_response.ShortDebugString()));
      EXPECT_EQ(per_port_response.status(), gnoi::diag::BERT_STATUS_OK);
      EXPECT_TRUE(MessageDifferencer::Equals(
          per_port_response.interface(),
          stop_request.per_port_requests(idx).interface()));
    }
  }

  // Wait for BERT to finish on test interfaces.
  int max_poll_count = 1 + (kDelayDuration + kWaitTime + kTestDuration -
                            (absl::Now() - start_time) - absl::Seconds(1)) /
                               kPollInterval;

  std::vector<std::string> interfaces_running_bert = {interface};
  ASSERT_NO_FATAL_FAILURE(WaitForBertToCompleteOnInterfaces(
      *sut_gnmi_stub_, sut_test_interfaces_, control_device,
      GetBertResultRequestFromStartRequest(bert_request_control_switch),
      max_poll_count));

  // Get the BERT result from the SUT. BERT status should be OK.
  {
    gnoi::diag::GetBERTResultRequest result_request_sut =
        GetBertResultRequestFromStartRequest(bert_request_sut);
    gnoi::diag::GetBERTResultResponse response;
    grpc::ClientContext context;
    EXPECT_OK(
        sut_diag_stub_->GetBERTResult(&context, result_request_sut, &response));
    LOG(INFO) << "SUT BERT Result: " << response.ShortDebugString();
    ASSERT_THAT(response.per_port_responses(),
                SizeIs(bert_request_sut.per_port_requests_size()));
    EXPECT_EQ(response.per_port_responses(0).status(),
              gnoi::diag::BERT_STATUS_OK);
  }

  // Get the BERT result from the control switch. It should have failed due to
  // peer lock loss.
  {
    gnoi::diag::GetBERTResultResponse response;
    ASSERT_OK_AND_ASSIGN(
        response, control_device.GetBERTResult(result_request_control_switch));
    LOG(INFO) << "Control switch BERT Result: " << response.ShortDebugString();
    ASSERT_THAT(response.per_port_responses(),
                SizeIs(bert_request_control_switch.per_port_requests_size()));
    EXPECT_EQ(response.per_port_responses(0).status(),
              gnoi::diag::BERT_STATUS_PEER_LOCK_LOST);
  }

  ASSERT_OK(
      ValidatePortsUp(sut, control_device, sut_interfaces_, peer_interfaces_));
}

// Tests that if BERT is in progress, NSF reboot request is rejected.
// If NSF reboot is in progress, BERT start request is rejected.
// After NSF reboot is successfully completed, LQ should run properly.
TEST_P(BertTest, BertWithNsf) {
  ASSERT_NO_FATAL_FAILURE(
      InitializeTestEnvironment("1319dffa-2931-4e2e-9b31-27ab163d4fc4"));

  if (!GetParam().nsf_supported) {
    GTEST_SKIP() << "NSF is not supported.";
  }

  // Test requires one SUT interface.
  if (sut_interfaces_.empty()) {
    GTEST_SKIP() << "No SUT interfaces to test";
  }
  thinkit::Switch &sut = generic_testbed_->Sut();
  thinkit::ControlDevice &control_device = generic_testbed_->ControlDevice();
  ASSERT_OK(
      ValidatePortsUp(sut, control_device, sut_interfaces_, peer_interfaces_));

  // Select one operational state "up" port.
  std::string interface = absl::GetFlag(FLAGS_interface);
  if (!interface.empty()) {
    // Verify that provided interfaces are part of SUT's UP interfaces.
    ASSERT_TRUE(IsInterfaceInList(interface, sut_interfaces_))
        << "SUT test interface selected for test: "
        << interface << "./n UP interfaces on SUT: "
        << absl::StrJoin(sut_interfaces_, ",");
  } else {
    sut_test_interfaces_ = SelectNInterfacesFromList(1, sut_interfaces_);
    interface = sut_test_interfaces_[0];
  }
  ASSERT_OK_AND_ASSIGN(peer_test_interfaces_,
                       GetPeerInterfacesForSutInterfaces(sut_test_interfaces_));
  std::string peer_interface = peer_test_interfaces_[0];
  LOG(INFO) << "Selected {SUT, control interface}: {" << interface << ", "
            << peer_interface
            << "}. To repeat the test with same SUT interface, use "
            << "--test_arg=--interface=" << interface << " in test arguments.";

  gnoi::diag::StartBERTRequest bert_request_sut;
  gnoi::diag::StartBERTRequest bert_request_control_switch;
  std::string op_id = absl::StrCat("OpId-", absl::ToUnixMillis(absl::Now()));

  ASSERT_NO_FATAL_FAILURE(AddStartBertRequestForLink(
      &bert_request_sut, &bert_request_control_switch, interface,
      peer_interface, op_id));

  ASSERT_NO_FATAL_FAILURE(StartBertOnLink(bert_request_sut,
                                          bert_request_control_switch,
                                          *sut_diag_stub_, control_device));

  // Get start timestamp.
  absl::Time start_time = absl::Now();
  // Wait before reading the oper status.
  absl::SleepFor(kWaitToReadOperStatus);

  // Verify that SUT port should be in TESTING mode now.
  {
    ASSERT_OK_AND_ASSIGN(
        pins_test::OperStatus oper_status,
        pins_test::GetInterfaceOperStatusOverGnmi(*sut_gnmi_stub_, interface));
    ASSERT_EQ(oper_status, pins_test::OperStatus::kTesting);
  }

  // Request NSF on SUT and it should be rejected.
  EXPECT_THAT(pins_test::NsfReboot(generic_testbed_.get()),
              gutil::StatusIs(absl::StatusCode::kUnavailable));

  // Wait for BERT to finish on test interface or timeout.
  int max_poll_count = GetMaxPollCount(start_time);

  ASSERT_NO_FATAL_FAILURE(WaitForBertToCompleteOnInterfaces(
      *sut_gnmi_stub_, {interface}, control_device,
      GetBertResultRequestFromStartRequest(bert_request_control_switch),
      max_poll_count));

  ASSERT_NO_FATAL_FAILURE(GetAndVerifyResultForSuccess(
      bert_request_sut, bert_request_control_switch, *sut_diag_stub_,
      control_device, kTestDuration));
  // Request NSF on SUT and it should be accepted.
  ASSERT_OK(pins_test::NsfReboot(generic_testbed_.get()));

  ASSERT_OK_AND_ASSIGN(auto sut_gnoi_system_stub, sut.CreateGnoiSystemStub());
  absl::Status status = WaitForGnoiToBeUnavailable(*sut_gnoi_system_stub);
  EXPECT_OK(status);

  // Request BERT start request while NSF is in progress, it should be rejected.
  if (status.ok()) {
    gnoi::diag::StartBERTRequest sut_request_during_nsf;
    sut_request_during_nsf.set_bert_operation_id(
        absl::StrCat("Id-", absl::ToUnixMicros(absl::Now())));
    *(sut_request_during_nsf.add_per_port_requests()) =
        gutil::ParseProtoOrDie<gnoi::diag::StartBERTRequest::PerPortRequest>(
            BuildPerPortStartBertRequest(interface));

    gnoi::diag::StartBERTResponse sut_response;
    grpc::ClientContext context;
    LOG(INFO) << "Sending StartBERT request: "
              << sut_request_during_nsf.ShortDebugString();
    EXPECT_THAT(
        gutil::GrpcStatusToAbslStatus(sut_diag_stub_->StartBERT(
            &context, sut_request_during_nsf, &sut_response)),
        gutil::StatusIs(absl::StatusCode::kUnavailable, HasSubstr("NSF")))
        << "Response: " << sut_response.ShortDebugString();
  }

  // Wait for NSF reboot to complete.
  EXPECT_OK(pins_test::WaitForNsfReboot(generic_testbed_.get(),
                                        *GetParam().ssh_client));
  ASSERT_OK(
      ValidatePortsUp(sut, control_device, sut_interfaces_, peer_interfaces_));

  // Verify BERT is still working after NSF reboot.
  gnoi::diag::StartBERTRequest bert_request_sut_after_nsf;
  gnoi::diag::StartBERTRequest bert_request_control_switch_after_nsf;
  op_id = absl::StrCat("OpId-", absl::ToUnixMillis(absl::Now()));

  ASSERT_NO_FATAL_FAILURE(AddStartBertRequestForLink(
      &bert_request_sut_after_nsf, &bert_request_control_switch_after_nsf,
      interface, peer_interface, op_id));

  ASSERT_NO_FATAL_FAILURE(StartBertOnLink(bert_request_sut_after_nsf,
                                          bert_request_control_switch_after_nsf,
                                          *sut_diag_stub_, control_device));

  // Get start timestamp.
  start_time = absl::Now();

  // Wait before reading the oper status on the port.
  absl::SleepFor(kWaitToReadOperStatus);
  ASSERT_THAT(
      pins_test::GetInterfaceOperStatusOverGnmi(*sut_gnmi_stub_, interface),
      IsOkAndHolds(pins_test::OperStatus::kTesting));

  // Wait for BERT to finish on test interface or timeout.
  max_poll_count = GetMaxPollCount(start_time);

  ASSERT_NO_FATAL_FAILURE(WaitForBertToCompleteOnInterfaces(
      *sut_gnmi_stub_, {interface}, control_device,
      GetBertResultRequestFromStartRequest(
          bert_request_control_switch_after_nsf),
      max_poll_count));

  ASSERT_NO_FATAL_FAILURE(GetAndVerifyResultForSuccess(
      bert_request_sut_after_nsf, bert_request_control_switch_after_nsf,
      *sut_diag_stub_, control_device, kTestDuration));

  // Wait for some time before checking the port status.
  absl::SleepFor(kPortsUpWaitTime);

  EXPECT_OK(
      ValidatePortsUp(sut, control_device, sut_interfaces_, peer_interfaces_));
}

} // namespace
}  // namespace bert
