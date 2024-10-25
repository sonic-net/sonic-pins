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

#include "absl/strings/str_cat.h"
#include "absl/strings/substitute.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "diag/diag.pb.h"
#include "glog/logging.h"
#include "google/protobuf/text_format.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"

namespace bert {

using ::testing::HasSubstr;

// Test StartBERT with invalid request parameters.
TEST_P(BertTest, StartBertFailsIfRequestParametersInvalid) {
  thinkit::Switch& sut = GetMirrorTestbed().Sut();
  ASSERT_OK_AND_ASSIGN(auto sut_gnoi_diag_stub, sut.CreateGnoiDiagStub());

  // TODO (b/182417612) : Select one admin state "up" port.
  gnoi::diag::StartBERTRequest valid_request =
      gutil::ParseProtoOrDie<gnoi::diag::StartBERTRequest>(R"PROTO(
        bert_operation_id: "OpId-1"
        per_port_requests {
          interface {
            origin: "openconfig"
            elem { name: "interfaces" }
            elem {
              name: "interface"
              key { key: "name" value: "Ethernet0" }
            }
          }
          prbs_polynomial: PRBS_POLYNOMIAL_PRBS23
          test_duration_in_secs: 600
        }
      )PROTO");
  // Set a unique BERT operation id using current time.
  valid_request.set_bert_operation_id(
      absl::StrCat("OpId-", absl::ToUnixMillis(absl::Now())));
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
    gnoi::types::Path invalid_interface =
        gutil::ParseProtoOrDie<gnoi::types::Path>(
            R"PROTO(
              origin: "openconfig"
              elem { name: "interfaces" }
              elem {
                name: "interface"
                key { key: "name" value: "InvalidPort" }
              }
            )PROTO");
    invalid_interface_request.mutable_per_port_requests(0)
        ->mutable_interface()
        ->CopyFrom(invalid_interface);
    response.Clear();
    grpc::ClientContext context;
    LOG(INFO) << "Sending StartBERT request: "
              << invalid_interface_request.ShortDebugString();
    EXPECT_THAT(gutil::GrpcStatusToAbslStatus(sut_gnoi_diag_stub->StartBERT(
                    &context, invalid_interface_request, &response)),
                gutil::StatusIs(absl::StatusCode::kInvalidArgument,
                                HasSubstr("Interface is invalid")));
  }
}

}  // namespace bert
