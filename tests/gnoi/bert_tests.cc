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

#include "tests/gnoi/bert_tests.h"

#include <random>
#include "absl/container/flat_hash_set.h"
#include "absl/flags/flag.h"
#include "absl/random/random.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/substitute.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "diag/diag.pb.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "google/protobuf/text_format.h"
#include "google/protobuf/util/message_differencer.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/validator/validator_lib.h"
#include "thinkit/test_environment.h"

ABSL_FLAG(uint32_t, idx_seed, static_cast<uint32_t>(std::time(nullptr)),
          "Seed to randomly generate interface index.");

ABSL_FLAG(std::string, interface, "",
          "Interface to run qualification on. If unspecified, random port "
          "will be chosen.");

ABSL_FLAG(std::vector<std::string>, interfaces, std::vector<std::string>(),
          "Interfaces to run qualification on. If unspecified, random ports "
          "will be chosen.");

namespace bert {

using ::google::protobuf::util::MessageDifferencer;
using ::testing::HasSubstr;
using ::testing::SizeIs;

// BERT test duration.
constexpr absl::Duration kTestDuration = absl::Seconds(180);
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

constexpr uint8_t kMaxAllowedInterfacesToRunBert = 96;

constexpr char kEnabledFalse[] = "{\"enabled\":false}";
constexpr char kEnabledTrue[] = "{\"enabled\":true}";

const std::string BuildPerPortStartBertRequest(
    absl::string_view interface_name) {
  return absl::Substitute(R"pb(
                            interface {
                              origin: "openconfig"
                              elem { name: "interfaces" }
                              elem {
                                name: "interface"
                                key { key: "name" value: '$0' }
                              }
                            }
                            prbs_polynomial: PRBS_POLYNOMIAL_PRBS23
                            test_duration_in_secs: $1
                          )pb",
                          interface_name, ToInt64Seconds(kTestDuration));
}

const std::string BuildOpenConfigInterface(absl::string_view interface_name) {
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

void SendStartBertRequestSuccessfully(
    gnoi::diag::StartBERTRequest& request,
    gnoi::diag::Diag::StubInterface& gnoi_diag_stub) {
  gnoi::diag::StartBERTResponse response;
  grpc::ClientContext context;
  LOG(INFO) << "StartBERT request: " << request.ShortDebugString();
  ASSERT_OK(gnoi_diag_stub.StartBERT(&context, request, &response));

  // Verify response.
  ASSERT_THAT(response.per_port_responses(),
              SizeIs(request.per_port_requests_size()));
  EXPECT_EQ(response.bert_operation_id(), request.bert_operation_id());

  for (int idx = 0; idx < response.per_port_responses_size(); ++idx) {
    auto per_port_response = response.per_port_responses(idx);
    SCOPED_TRACE(absl::StrCat("Verifying StartBERT port response: ",
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
                       std::vector<std::string>& interfaces) {
  return std::find(interfaces.begin(), interfaces.end(), interface) !=
         interfaces.end();
}

void WaitForBertToCompleteOnInterfaces(
    gnmi::gNMI::StubInterface& sut_gnmi_stub,
    gnmi::gNMI::StubInterface& control_switch_gnmi_stub,
    std::vector<std::string>& interfaces, int max_poll_count) {
  for (int count = 0; count < max_poll_count; ++count) {
    absl::SleepFor(kPollInterval);
    // If port is no longer in "TESTING" oper state on both sides of the link,
    // linkqual has completed on the link and full result is ready.
    for (auto it = interfaces.begin(); it != interfaces.end();) {
      ASSERT_OK_AND_ASSIGN(
          pins_test::OperStatus oper_status,
          pins_test::GetInterfaceOperStatusOverGnmi(sut_gnmi_stub, *it));
      if (oper_status != pins_test::OperStatus::kTesting) {
        ASSERT_OK_AND_ASSIGN(oper_status,
                             pins_test::GetInterfaceOperStatusOverGnmi(
                                 control_switch_gnmi_stub, *it));
        if (oper_status != pins_test::OperStatus::kTesting) {
          it = interfaces.erase(it);
          continue;
        }
      }
      ++it;
    }
    if (interfaces.empty()) break;
  }

  EXPECT_THAT(interfaces, testing::IsEmpty());
}

void VerifyBertResultForSuccess(
    const gnoi::diag::GetBERTResultResponse::PerPortResponse& bert_result,
    absl::string_view op_id, const gnoi::types::Path& interface,
    gnoi::diag::PrbsPolynomial prbs_order) {
  EXPECT_EQ(bert_result.status(), gnoi::diag::BERT_STATUS_OK);
  EXPECT_TRUE(MessageDifferencer::Equals(bert_result.interface(), interface));
  EXPECT_EQ(bert_result.bert_operation_id(), op_id);
  EXPECT_EQ(bert_result.prbs_polynomial(), prbs_order);
  EXPECT_TRUE(bert_result.peer_lock_established());
  EXPECT_FALSE(bert_result.peer_lock_lost());
  // Check the timestamps to verify if time taken for BERT is between test
  // duration and (test duration + 60 seconds).
  EXPECT_GE(bert_result.last_bert_get_result_timestamp() -
                bert_result.last_bert_start_timestamp(),
            absl::ToInt64Microseconds(kTestDuration));
  EXPECT_LE(bert_result.last_bert_get_result_timestamp() -
                bert_result.last_bert_start_timestamp(),
            absl::ToInt64Microseconds(kTestDuration + absl::Seconds(60)));

  EXPECT_THAT(bert_result.error_count_per_minute(),
              SizeIs(absl::ToInt64Minutes(kTestDuration)));
  uint64_t total_errors = 0;
  for (const uint32_t error_count : bert_result.error_count_per_minute()) {
    total_errors += error_count;
  }
  EXPECT_EQ(bert_result.total_errors(), total_errors);
}

// Helps in getting the BERT result on a set of ports and if BERT is running on
// the port, forces admin status down by disabling it. It also modifies the
// list of ports in request by removing the port that was running BERT.
void CheckRunningBertAndForceAdminDownHelper(
    gnoi::diag::Diag::StubInterface& gnoi_diag_stub,
    gnmi::gNMI::StubInterface& gnmi_stub,
    gnoi::diag::GetBERTResultRequest* request) {
  gnoi::diag::GetBERTResultResponse response;
  grpc::ClientContext context;
  ASSERT_OK(gnoi_diag_stub.GetBERTResult(&context, *request, &response));

    ASSERT_THAT(response.per_port_responses(),
              SizeIs(request->per_port_requests_size()));
  request->clear_per_port_requests();
  for (const auto& result : response.per_port_responses()) {
    // Check if BERT is running.
    if ((result.status() == gnoi::diag::BERT_STATUS_OK) &&
        (result.peer_lock_established())) {
      ASSERT_OK_AND_ASSIGN(
          const std::string interface,
          GetInterfaceNameFromOcInterfacePath(result.interface()));
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
    }
  }
}

// Checks if BERT is running on the ports where we are supposed to force admin
// status DOWN. If BERT is running, force admin status to DOWN on port.
void CheckRunningBertAndForceAdminDown(
    gnoi::diag::Diag::StubInterface& sut_gnoi_diag_stub,
    gnoi::diag::Diag::StubInterface& control_switch_gnoi_diag_stub,
    gnmi::gNMI::StubInterface& sut_gnmi_stub,
    gnmi::gNMI::StubInterface& control_switch_gnmi_stub,
    absl::string_view op_id, std::vector<std::string>& sut_interfaces,
    std::vector<std::string>& control_switch_interfaces) {
  gnoi::diag::GetBERTResultRequest sut_request;
  sut_request.set_bert_operation_id(std::string(op_id));
  for (const std::string& interface : sut_interfaces) {
    *(sut_request.add_per_port_requests()->mutable_interface()) =
        gutil::ParseProtoOrDie<gnoi::types::Path>(
            BuildOpenConfigInterface(interface));
  }

  gnoi::diag::GetBERTResultRequest control_switch_request;
  control_switch_request.set_bert_operation_id(std::string(op_id));
  for (const std::string& interface : control_switch_interfaces) {
    *(control_switch_request.add_per_port_requests()->mutable_interface()) =
        gutil::ParseProtoOrDie<gnoi::types::Path>(
            BuildOpenConfigInterface(interface));
  }

  int max_poll_count =
      1 + (absl::ToInt64Seconds(kSyncDuration - absl::Seconds(1)) /
           absl::ToInt64Seconds(kPollInterval));

  while (max_poll_count > 0) {
    absl::SleepFor(kPollInterval);
    if (sut_request.per_port_requests_size() > 0) {
      // Check BERT status on SUT and force admin status down.
      ASSERT_NO_FATAL_FAILURE(CheckRunningBertAndForceAdminDownHelper(
          sut_gnoi_diag_stub, sut_gnmi_stub, &sut_request));
    }

    if (control_switch_request.per_port_requests_size() > 0) {
      // Check BERT status on control switch and force admin status down.
      ASSERT_NO_FATAL_FAILURE(CheckRunningBertAndForceAdminDownHelper(
          control_switch_gnoi_diag_stub, control_switch_gnmi_stub,
          &control_switch_request));
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
    gnoi::diag::Diag::StubInterface& gnoi_diag_stub,
    gnoi::diag::StartBERTRequest& bert_request,
    std::vector<std::string>& sut_admin_down_interfaces,
    std::vector<std::string>& control_switch_admin_down_interfaces) {
  gnoi::diag::GetBERTResultRequest result_request;
  result_request.set_bert_operation_id(bert_request.bert_operation_id());
  for (unsigned idx = 0; idx < bert_request.per_port_requests_size(); ++idx) {
    *(result_request.add_per_port_requests()->mutable_interface()) =
        bert_request.per_port_requests(idx).interface();
  }
  gnoi::diag::GetBERTResultResponse result_response;
  grpc::ClientContext result_context;
  ASSERT_OK(gnoi_diag_stub.GetBERTResult(&result_context, result_request,
                                         &result_response));
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
    // Check if interface is part of list where admin state was disabled.
    if (IsInterfaceInList(interface_name, sut_admin_down_interfaces) ||
        IsInterfaceInList(interface_name,
                          control_switch_admin_down_interfaces)) {
      // Verify BERT failure.
      EXPECT_EQ(result_response.per_port_responses(idx).status(),
                gnoi::diag::BERT_STATUS_PEER_LOCK_LOST);
      EXPECT_TRUE(
          result_response.per_port_responses(idx).peer_lock_established());
      EXPECT_TRUE(result_response.per_port_responses(idx).peer_lock_lost());
      continue;
    }
    // If it is normal BERT running port, verify normal SUCCESS result.
    VerifyBertResultForSuccess(
        result_response.per_port_responses(idx),
        bert_request.bert_operation_id(),
        bert_request.per_port_requests(idx).interface(),
        bert_request.per_port_requests(idx).prbs_polynomial());
  }
}

void SelectNUpInterfaces(int port_count_to_select,
                         gnmi::gNMI::StubInterface& gnmi_stub,
                         std::vector<std::string>* interfaces) {
  // Get all the interfaces that are operational status "UP".
  ASSERT_OK_AND_ASSIGN(*interfaces,
                       pins_test::GetUpInterfacesOverGnmi(gnmi_stub));
  // Choose random ports.
  ASSERT_GE(interfaces->size(), port_count_to_select);
  std::shuffle(interfaces->begin(), interfaces->end(), absl::BitGen());
  interfaces->resize(port_count_to_select);
}

// Test StartBERT with invalid request parameters.
TEST_P(BertTest, StartBertFailsIfRequestParametersInvalid) {
  GetMirrorTestbed().Environment().SetTestCaseID(
      "c1dcb1cc-4806-45cc-8f8a-676beafde103");
  thinkit::Switch& sut = GetMirrorTestbed().Sut();
  ASSERT_OK(pins_test::PortsUp(sut));
  ASSERT_OK_AND_ASSIGN(auto sut_gnoi_diag_stub, sut.CreateGnoiDiagStub());

  // Select one operational state "up" port.
  std::string interface = absl::GetFlag(FLAGS_interface);
  if (interface.empty()) {
    std::vector<std::string> interfaces;
    ASSERT_OK_AND_ASSIGN(
        std::unique_ptr<gnmi::gNMI::StubInterface> sut_gnmi_stub,
        sut.CreateGnmiStub());
    ASSERT_NO_FATAL_FAILURE(
        SelectNUpInterfaces(1, *sut_gnmi_stub, &interfaces));
    interface = interfaces[0];
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
           BuildPerPortStartBertRequest("interface"));
  gnoi::diag::StartBERTResponse response;

  // Case 1: BERT test duration is 0 secs.
  {
    gnoi::diag::StartBERTRequest too_short_time_request = valid_request;
    too_short_time_request.mutable_per_port_requests(0)
        ->set_test_duration_in_secs(0);
    grpc::ClientContext context;
    LOG(INFO) << "Sending StartBERT request: "
              << too_short_time_request.ShortDebugString();
    EXPECT_THAT(gutil::GrpcStatusToAbslStatus(sut_gnoi_diag_stub->StartBERT(
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
    EXPECT_THAT(gutil::GrpcStatusToAbslStatus(sut_gnoi_diag_stub->StartBERT(
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
    EXPECT_THAT(gutil::GrpcStatusToAbslStatus(sut_gnoi_diag_stub->StartBERT(
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
    EXPECT_THAT(gutil::GrpcStatusToAbslStatus(sut_gnoi_diag_stub->StartBERT(
                    &context, invalid_interface_request, &response)),
                gutil::StatusIs(absl::StatusCode::kInvalidArgument,
                                HasSubstr("Interface is invalid")));
  }
  // TODO (b/176913347): Enable the all ports UP check.
  // ASSERT_OK(pins_test::PortsUp(sut));
}

// Test StopBERT RPC with invalid argument in the request.
// 1) If StopBERT RPC is requested on an invalid port, RPC should fail.
// 2) If StopBERT RPC is requested on a port that is not running BERT, RPC
// should fail.
TEST_P(BertTest, StopBertfailsIfRequestParametersInvalid) {
  GetMirrorTestbed().Environment().SetTestCaseID(
      "224db9cf-c709-486d-a0d3-6ab64c1a1e1f");
  thinkit::Switch& sut = GetMirrorTestbed().Sut();

  ASSERT_OK(pins_test::PortsUp(sut));
  ASSERT_OK_AND_ASSIGN(auto sut_gnoi_diag_stub, sut.CreateGnoiDiagStub());

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
            sut_gnoi_diag_stub->StopBERT(&context, request, &response)),
        gutil::StatusIs(
            absl::StatusCode::kInvalidArgument,
            AllOf(HasSubstr("Interface is invalid"),
                  HasSubstr("Operation ID is not found on interface"))));
  }

  // Request StopBERT RPC on a port that is not running BERT, RPC should fail.
  {
    // Select one operational state "up" port.
    std::string interface = absl::GetFlag(FLAGS_interface);
    if (interface.empty()) {
      std::vector<std::string> interfaces;
      ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());
      ASSERT_NO_FATAL_FAILURE(
          SelectNUpInterfaces(1, *sut_gnmi_stub, &interfaces));
      interface = interfaces[0];
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
            sut_gnoi_diag_stub->StopBERT(&context, request, &response)),
        gutil::StatusIs(absl::StatusCode::kInvalidArgument,
                        HasSubstr("Operation ID is not found on interface")));
  }

  // TODO (b/176913347): Enable the all ports UP check.
  // ASSERT_OK(pins_test::PortsUp(sut));
}

// Test GetBERTResult RPC with invalid argument in the request.
// 1) If GetBERTResult RPC is requested on an invalid port, RPC should fail.
// 2) If GetBERTResult RPC is requested on a port that never ran BERT before,
// RPC should fail.
TEST_P(BertTest, GetBertResultFailsIfRequestParametersInvalid) {
  GetMirrorTestbed().Environment().SetTestCaseID(
      "4f837d7a-ab44-4694-9ca9-399d576757f4");
  thinkit::Switch& sut = GetMirrorTestbed().Sut();
  ASSERT_OK(pins_test::PortsUp(sut));
  ASSERT_OK_AND_ASSIGN(auto sut_gnoi_diag_stub, sut.CreateGnoiDiagStub());

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
    EXPECT_THAT(gutil::GrpcStatusToAbslStatus(sut_gnoi_diag_stub->GetBERTResult(
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
    if (interface.empty()) {
      std::vector<std::string> interfaces;
      ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());
      ASSERT_NO_FATAL_FAILURE(
          SelectNUpInterfaces(1, *sut_gnmi_stub, &interfaces));
      interface = interfaces[0];
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
    EXPECT_THAT(gutil::GrpcStatusToAbslStatus(sut_gnoi_diag_stub->GetBERTResult(
                    &context, result_request, &result_response)),
                gutil::StatusIs(absl::StatusCode::kInvalidArgument,
                                AllOf(HasSubstr("Result is not found for intf"),
                                      HasSubstr(interface))));
  }

  ASSERT_OK(pins_test::PortsUp(sut));
}


// Test StartBERT fails if peer port is not running BERT.
TEST_P(BertTest, StartBertfailsIfPeerPortNotRunningBert) {
  GetMirrorTestbed().Environment().SetTestCaseID(
      "37e48922-0616-4d16-8fd3-975897491956");
  thinkit::Switch& sut = GetMirrorTestbed().Sut();
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());
  ASSERT_OK(pins_test::PortsUp(sut));
  ASSERT_OK_AND_ASSIGN(auto sut_gnoi_diag_stub, sut.CreateGnoiDiagStub());

  // Select one operational state "up" port.
  std::string interface = absl::GetFlag(FLAGS_interface);
  if (interface.empty()) {
    std::vector<std::string> interfaces;
    ASSERT_NO_FATAL_FAILURE(
        SelectNUpInterfaces(1, *sut_gnmi_stub, &interfaces));
    interface = interfaces[0];
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
  gnoi::diag::StartBERTResponse bert_response;
  grpc::ClientContext context;
  LOG(INFO) << "Sending StartBERT request: " << bert_request.ShortDebugString();

  // Poll for allowed BERT delay duration.
  int max_poll_count =
      ceil(ToInt64Seconds(kDelayDuration) / ToInt64Seconds(kPollInterval));
  bool poll_timeout = true;
  for (int count = 0; count < max_poll_count; ++count) {  
    absl::SleepFor(kPollInterval);
    ASSERT_OK_AND_ASSIGN(
        pins_test::OperStatus oper_status,
        pins_test::GetInterfaceOperStatusOverGnmi(*sut_gnmi_stub, interface));
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
  EXPECT_OK(sut_gnoi_diag_stub->GetBERTResult(&result_context, result_request,
                                              &result_response));
  LOG(INFO) << "Result: " << result_response.ShortDebugString();
  // TODO (b/176913347): Enable the all ports UP check.
  // ASSERT_OK(pins_test::PortsUp(sut));
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
  GetMirrorTestbed().Environment().SetTestCaseID(
      "b31a796a-d078-4d45-b785-f09ec598e05a");
  thinkit::Switch& sut = GetMirrorTestbed().Sut();
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());
  ASSERT_OK(pins_test::PortsUp(sut));
  ASSERT_OK_AND_ASSIGN(auto sut_gnoi_diag_stub, sut.CreateGnoiDiagStub());

  thinkit::Switch& control_switch = GetMirrorTestbed().ControlSwitch();
  ASSERT_OK_AND_ASSIGN(auto control_switch_gnmi_stub,
                       control_switch.CreateGnmiStub());
  ASSERT_OK(pins_test::PortsUp(control_switch));
  ASSERT_OK_AND_ASSIGN(auto control_switch_gnoi_diag_stub,
                       control_switch.CreateGnoiDiagStub());

  // Select 2 operational state "up" ports.
  std::vector<std::string> interfaces = absl::GetFlag(FLAGS_interfaces);
  if (interfaces.empty()) {
    ASSERT_OK_AND_ASSIGN(std::unique_ptr<gnmi::gNMI::StubInterface> sut_gnmi_stub,
                         sut.CreateGnmiStub());
    ASSERT_NO_FATAL_FAILURE(
        SelectNUpInterfaces(2, *sut_gnmi_stub, &interfaces));
  }
  ASSERT_THAT(interfaces, SizeIs(2));
  LOG(INFO) << "Selected interfaces: " << absl::StrJoin(interfaces, ",")
            << ". To repeat the test with same interfaces, "
            << "use --test_arg=--interfaces=" << absl::StrJoin(interfaces, ",")
            << " in test arguments.";

  gnoi::diag::StartBERTRequest bert_request;
  // Create the BERT request.
  bert_request.set_bert_operation_id(
      absl::StrCat("OpId-", absl::ToUnixMillis(absl::Now())));
  for (const std::string& interface : interfaces) {
    *(bert_request.add_per_port_requests()) =
        gutil::ParseProtoOrDie<gnoi::diag::StartBERTRequest::PerPortRequest>(
            BuildPerPortStartBertRequest(interface));
  }

  // Request StartBert on the SUT switch.
  LOG(INFO) << "Sending StartBERT request on SUT:";
  ASSERT_NO_FATAL_FAILURE(
      SendStartBertRequestSuccessfully(bert_request, *sut_gnoi_diag_stub));

  // Request StartBert on the control switch.
  LOG(INFO) << "Sending StartBERT request on control switch:";
  ASSERT_NO_FATAL_FAILURE(SendStartBertRequestSuccessfully(
      bert_request, *control_switch_gnoi_diag_stub));

  // Get start timestamp.
  absl::Time start_time = absl::Now();
  // Wait before reading the oper status.
  absl::SleepFor(kWaitToReadOperStatus);

  // Verify that ports should be in TESTING mode now.
  for (const std::string& interface : interfaces) {
    SCOPED_TRACE(
        absl::StrCat("Getting operational status for interface: ", interface));
    ASSERT_OK_AND_ASSIGN(
        pins_test::OperStatus oper_status,
        pins_test::GetInterfaceOperStatusOverGnmi(*sut_gnmi_stub, interface));
    ASSERT_EQ(oper_status, pins_test::OperStatus::kTesting);
    ASSERT_OK_AND_ASSIGN(oper_status,
                         pins_test::GetInterfaceOperStatusOverGnmi(
                             *control_switch_gnmi_stub, interface));
    ASSERT_EQ(oper_status, pins_test::OperStatus::kTesting);
  }

  // Request another StartBert on the same ports on SUT and it should fail.
  {
    gnoi::diag::StartBERTRequest second_bert_request = bert_request;
    second_bert_request.set_bert_operation_id(
        absl::StrCat("OpId-", absl::ToUnixMillis(absl::Now())));
    // Request StartBert on the SUT switch.
    LOG(INFO) << "Sending second StartBERT request on SUT:";
    ASSERT_NO_FATAL_FAILURE(SendStartBertRequestSuccessfully(
        second_bert_request, *sut_gnoi_diag_stub));

    // Wait some time before querying the result.
    absl::SleepFor(kWaitTime);
    gnoi::diag::GetBERTResultRequest result_request;
    result_request.set_bert_operation_id(
        second_bert_request.bert_operation_id());
    for (int idx = 0; idx < interfaces.size(); ++idx) {
      *(result_request.add_per_port_requests()->mutable_interface()) =
          second_bert_request.per_port_requests(idx).interface();
    }

    gnoi::diag::GetBERTResultResponse result_response;
    grpc::ClientContext result_context;
    EXPECT_OK(sut_gnoi_diag_stub->GetBERTResult(&result_context, result_request,
                                                &result_response));
    LOG(INFO) << "Result: " << result_response.ShortDebugString();
    EXPECT_THAT(result_response.per_port_responses(),
                SizeIs(interfaces.size()));
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

  std::vector<std::string> interfaces_running_bert = interfaces;
  ASSERT_NO_FATAL_FAILURE(WaitForBertToCompleteOnInterfaces(
      *sut_gnmi_stub, *control_switch_gnmi_stub, interfaces_running_bert,
      max_poll_count));

  gnoi::diag::GetBERTResultRequest result_request;
  result_request.set_bert_operation_id(bert_request.bert_operation_id());
  for (int idx = 0; idx < interfaces.size(); ++idx) {
    *(result_request.add_per_port_requests()->mutable_interface()) =
        bert_request.per_port_requests(idx).interface();
  }
  // Get the BERT result from the SUT.

  {
    gnoi::diag::GetBERTResultResponse result_response;
    grpc::ClientContext result_context;
    EXPECT_OK(sut_gnoi_diag_stub->GetBERTResult(&result_context, result_request,
                                                &result_response));
    LOG(INFO) << "Result: " << result_response.ShortDebugString();
    ASSERT_THAT(result_response.per_port_responses(),
                SizeIs(bert_request.per_port_requests_size()));
    for (int idx = 0; idx < result_response.per_port_responses_size(); ++idx) {
      VerifyBertResultForSuccess(
          result_response.per_port_responses(idx),
          bert_request.bert_operation_id(),
          bert_request.per_port_requests(idx).interface(),
          bert_request.per_port_requests(idx).prbs_polynomial());
    }
  }
 
  // Get the BERT result from the control switch.
  {
    gnoi::diag::GetBERTResultResponse result_response;
    grpc::ClientContext result_context;
    EXPECT_OK(control_switch_gnoi_diag_stub->GetBERTResult(
        &result_context, result_request, &result_response));
    LOG(INFO) << "Result: " << result_response.ShortDebugString();
    ASSERT_THAT(result_response.per_port_responses(),
                SizeIs(bert_request.per_port_requests_size()));
    for (int idx = 0; idx < result_response.per_port_responses_size(); ++idx) {
      VerifyBertResultForSuccess(
          result_response.per_port_responses(idx),
          bert_request.bert_operation_id(),
          bert_request.per_port_requests(idx).interface(),
          bert_request.per_port_requests(idx).prbs_polynomial());
    }
  }

  // Request another StartBert on the SUT with just used operation id, it should
  // fail.
  {
    gnoi::diag::StartBERTResponse bert_response;
    grpc::ClientContext context;
    LOG(INFO) << "Sending StartBERT request: "
              << bert_request.ShortDebugString();
    EXPECT_THAT(
        gutil::GrpcStatusToAbslStatus(sut_gnoi_diag_stub->StartBERT(
            &context, bert_request, &bert_response)),
        gutil::StatusIs(absl::StatusCode::kInvalidArgument,
                        AllOf(HasSubstr("Invalid request"),
                              HasSubstr(bert_request.bert_operation_id()),
                              HasSubstr("exists"))))
        << "Response: " << bert_response.ShortDebugString();
  }
  // TODO (b/176913347): Enable the all ports UP check.
  // ASSERT_OK(pins_test::PortsUp(sut));
  // ASSERT_OK(pins_test::PortsUp(control_switch));
}

// Runs the BERT test on current maximum allowed number of interfaces. During
// the BERT run:
// 1) Disable admin state of few ports on SUT,
// 2) Disable admin state of few ports on control switch,
// This helps us verify a mix of operation during BERT - unexpected software or
// hardware errors.
TEST_P(BertTest, RunBertOnMaximumAllowedPorts) {
  GetMirrorTestbed().Environment().SetTestCaseID(
      "ce526e97-2a62-4044-9dce-8fc74b232e4b");
  thinkit::Switch& sut = GetMirrorTestbed().Sut();
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());
  ASSERT_OK(pins_test::PortsUp(sut));
  ASSERT_OK_AND_ASSIGN(auto sut_gnoi_diag_stub, sut.CreateGnoiDiagStub());

  thinkit::Switch& control_switch = GetMirrorTestbed().ControlSwitch();
  ASSERT_OK_AND_ASSIGN(auto control_switch_gnmi_stub,
                       control_switch.CreateGnmiStub());
  ASSERT_OK(pins_test::PortsUp(control_switch));
  ASSERT_OK_AND_ASSIGN(auto control_switch_gnoi_diag_stub,
                       control_switch.CreateGnoiDiagStub());

  // Get all the interfaces that are operational status "UP".
  ASSERT_OK_AND_ASSIGN(std::vector<std::string> interfaces,
                       pins_test::GetUpInterfacesOverGnmi(*sut_gnmi_stub));
  // For this test, we need at least 5 UP interfaces.
  ASSERT_GE(interfaces.size(), 5);
  // Resize the interface list if UP ports are more than max number of allowed
  // ports.
  if (interfaces.size() > kMaxAllowedInterfacesToRunBert) {
    interfaces.resize(kMaxAllowedInterfacesToRunBert);
  }

  // Select 'N' ports on control switch and 'N' ports on SUT for admin down.
  int num_interfaces_to_disable = 1 + (interfaces.size() / 16);
  // Seed the std::rand().
  LOG(INFO) << "Seeding pseudo-random number generator with seed: "
            << absl::GetFlag(FLAGS_idx_seed);
  // Select SUT interfaces in the range [0..interfaces/2).
  std::vector<std::string> sut_interfaces_for_admin_down;
  std::sample(interfaces.begin(), interfaces.begin() + interfaces.size() / 2,
              std::back_inserter(sut_interfaces_for_admin_down),
              num_interfaces_to_disable,
              std::mt19937(absl::GetFlag(FLAGS_idx_seed)));
  // Select control switch interfaces in the range [interfaces/2..interfaces].
  std::vector<std::string> control_switch_interfaces_for_admin_down;
  std::sample(interfaces.begin() + interfaces.size() / 2, interfaces.end(),
              std::back_inserter(control_switch_interfaces_for_admin_down),
              num_interfaces_to_disable,
              std::mt19937(absl::GetFlag(FLAGS_idx_seed)));

  LOG(INFO) << "Starting BERT on " << interfaces.size()
            << " interfaces: " << absl::StrJoin(interfaces, ",");
  LOG(INFO) << "Interfaces selected on SUT for admin down: "
            << absl::StrJoin(sut_interfaces_for_admin_down, ",");
  LOG(INFO) << "Interfaces selected on control switch for admin down: "
            << absl::StrJoin(control_switch_interfaces_for_admin_down, ",");

    gnoi::diag::StartBERTRequest bert_request;
  // Create the BERT request.
  bert_request.set_bert_operation_id(
      absl::StrCat("OpId-", absl::ToUnixMillis(absl::Now())));
  for (const std::string& interface : interfaces) {
    *(bert_request.add_per_port_requests()) =
        gutil::ParseProtoOrDie<gnoi::diag::StartBERTRequest::PerPortRequest>(
            BuildPerPortStartBertRequest(interface));
  }

  // Request StartBert on the SUT switch.
  LOG(INFO) << "Sending StartBERT request on SUT:";
  ASSERT_NO_FATAL_FAILURE(
      SendStartBertRequestSuccessfully(bert_request, *sut_gnoi_diag_stub));

  // Request StartBert on the control switch.
  LOG(INFO) << "Sending StartBERT request on control switch:";
  ASSERT_NO_FATAL_FAILURE(SendStartBertRequestSuccessfully(
      bert_request, *control_switch_gnoi_diag_stub));

  absl::Time start_time = absl::Now();
  // Give some time to BERT to move in SYNC state.
  absl::SleepFor(absl::Seconds(90));
  
  absl::Time end_time = absl::Now();

  // Wait for BERT to finish on test interfaces.
  int max_poll_count = 1 + (kDelayDuration + kWaitTime + kTestDuration -
                            (end_time - start_time) - absl::Seconds(1)) /
                               kPollInterval;

  std::vector<std::string> interfaces_running_bert = interfaces;
  ASSERT_NO_FATAL_FAILURE(WaitForBertToCompleteOnInterfaces(
      *sut_gnmi_stub, *control_switch_gnmi_stub, interfaces_running_bert,
      max_poll_count));

  // Wait for some time before checking the port status.
  absl::SleepFor(kPortsUpWaitTime);

  ASSERT_OK(pins_test::PortsUp(sut));
  ASSERT_OK(pins_test::PortsUp(control_switch));
}

// Run BERT on a port. Issue StopBERT on the SUT port, this causes BERT to
// stop on SUT and this will cause BERT failure on control switch as control
// switch side port will lose lock with its peer port on SUT side.
TEST_P(BertTest, StopBertSucceeds) {
  GetMirrorTestbed().Environment().SetTestCaseID(
      "be7b6653-51b9-4231-a438-d9589bbcb677");
  thinkit::Switch& sut = GetMirrorTestbed().Sut();
  ASSERT_OK_AND_ASSIGN(auto sut_gnmi_stub, sut.CreateGnmiStub());
  ASSERT_OK(pins_test::PortsUp(sut));
  ASSERT_OK_AND_ASSIGN(auto sut_gnoi_diag_stub, sut.CreateGnoiDiagStub());

  thinkit::Switch& control_switch = GetMirrorTestbed().ControlSwitch();
  ASSERT_OK_AND_ASSIGN(auto control_switch_gnmi_stub,
                       control_switch.CreateGnmiStub());
  ASSERT_OK(pins_test::PortsUp(control_switch));
  ASSERT_OK_AND_ASSIGN(auto control_switch_gnoi_diag_stub,
                       control_switch.CreateGnoiDiagStub());

  // Select one operational state "up" port.
  std::string interface = absl::GetFlag(FLAGS_interface);
  if (interface.empty()) {
    std::vector<std::string> interfaces;
    ASSERT_NO_FATAL_FAILURE(SelectNUpInterfaces(/*port_count_to_select=*/1,
                                                *sut_gnmi_stub, &interfaces));
    interface = interfaces[0];
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

  // Request StartBert on the SUT switch.
  LOG(INFO) << "Sending StartBERT request on SUT:";
  ASSERT_NO_FATAL_FAILURE(
      SendStartBertRequestSuccessfully(bert_request, *sut_gnoi_diag_stub));

  // Request StartBert on the control switch.
  LOG(INFO) << "Sending StartBERT request on control switch:";
  ASSERT_NO_FATAL_FAILURE(SendStartBertRequestSuccessfully(
      bert_request, *control_switch_gnoi_diag_stub));

  absl::Time start_time = absl::Now();
  // Wait before reading the oper status.
  absl::SleepFor(kWaitToReadOperStatus);

  // Verify that port should be in TESTING mode now.
  {
    ASSERT_OK_AND_ASSIGN(
        pins_test::OperStatus oper_status,
        pins_test::GetInterfaceOperStatusOverGnmi(*sut_gnmi_stub, interface));
    ASSERT_EQ(oper_status, pins_test::OperStatus::kTesting);
    ASSERT_OK_AND_ASSIGN(oper_status,
                         pins_test::GetInterfaceOperStatusOverGnmi(
                             *control_switch_gnmi_stub, interface));
    ASSERT_EQ(oper_status, pins_test::OperStatus::kTesting);
  }

  gnoi::diag::GetBERTResultRequest result_request;
  result_request.set_bert_operation_id(bert_request.bert_operation_id());
  *(result_request.add_per_port_requests()->mutable_interface()) =
      bert_request.per_port_requests(0).interface();

  // Verify control switch side BERT has acquired the lock and is running now.
  {
    int remaining_poll_count =
        1 + (kDelayDuration - absl::Seconds(1)) / kPollInterval;

    while (remaining_poll_count > 0) {
      absl::SleepFor(kPollInterval);
      gnoi::diag::GetBERTResultResponse response;
      grpc::ClientContext context;
      EXPECT_OK(control_switch_gnoi_diag_stub->GetBERTResult(
          &context, result_request, &response));
      ASSERT_THAT(response.per_port_responses(),
                  SizeIs(bert_request.per_port_requests_size()));
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
    stop_request.set_bert_operation_id(bert_request.bert_operation_id());
    *(stop_request.add_per_port_requests()->mutable_interface()) =
        bert_request.per_port_requests(0).interface();
    gnoi::diag::StopBERTResponse response;
    grpc::ClientContext context;
    LOG(INFO) << "Sending StopBERT request on SUT: "
              << stop_request.ShortDebugString();
    EXPECT_OK(sut_gnoi_diag_stub->StopBERT(&context, stop_request, &response));

    // Verify response.
    ASSERT_THAT(response.per_port_responses(),
                SizeIs(stop_request.per_port_requests_size()));
    EXPECT_EQ(response.bert_operation_id(), stop_request.bert_operation_id());

    for (int idx = 0; idx < response.per_port_responses_size(); ++idx) {
      auto per_port_response = response.per_port_responses(idx);
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
      *sut_gnmi_stub, *control_switch_gnmi_stub, interfaces_running_bert,
      max_poll_count));

  // Get the BERT result from the SUT. BERT status should be OK.
  {
    gnoi::diag::GetBERTResultResponse response;
    grpc::ClientContext context;
    EXPECT_OK(
        sut_gnoi_diag_stub->GetBERTResult(&context, result_request, &response));
    LOG(INFO) << "SUT BERT Result: " << response.ShortDebugString();
    ASSERT_THAT(response.per_port_responses(),
                SizeIs(bert_request.per_port_requests_size()));
    EXPECT_EQ(response.per_port_responses(0).status(),
              gnoi::diag::BERT_STATUS_OK);
  }

  // Get the BERT result from the control switch. It should have failed due to
  // peer lock loss.
  {
    gnoi::diag::GetBERTResultResponse response;
    grpc::ClientContext context;
    EXPECT_OK(control_switch_gnoi_diag_stub->GetBERTResult(
        &context, result_request, &response));
    LOG(INFO) << "Control switch BERT Result: " << response.ShortDebugString();
    ASSERT_THAT(response.per_port_responses(),
                SizeIs(bert_request.per_port_requests_size()));
    EXPECT_EQ(response.per_port_responses(0).status(),
              gnoi::diag::BERT_STATUS_PEER_LOCK_LOST);
    EXPECT_TRUE(response.per_port_responses(0).peer_lock_established());
    EXPECT_TRUE(response.per_port_responses(0).peer_lock_lost());
  }

  ASSERT_OK(pins_test::PortsUp(sut));
  ASSERT_OK(pins_test::PortsUp(control_switch));
}

}  // namespace bert
