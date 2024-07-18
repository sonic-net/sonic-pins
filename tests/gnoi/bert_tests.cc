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

#include "absl/strings/substitute.h"
#include "diag/diag.pb.h"
#include "glog/logging.h"
#include "google/protobuf/text_format.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"

namespace bert {

// Test StartBERT with test duration longer than maximum allowed duration.
TEST_P(BertTest, StartBertFailsIfTestDurationTooLong) {
  thinkit::Switch& sut = GetMirrorTestbed().Sut();
  ASSERT_OK_AND_ASSIGN(auto sut_gnoi_diag_stub, sut.CreateGnoiDiagStub());

  // Set BERT test duration to more than 24 hours: (24 hours + 1 sec).
  constexpr uint32_t kTesDurationInSecs = (60 * 60 * 24) + 1;

  // TODO (ashishksingh) : Before using the "Ethernet0", run sanity test to
  // ensure the ports are oper-state "up" on the SUT switch.
  const std::string kStartBertRequest =
      absl::Substitute(R"PROTO(
                         bert_operation_id: "OpId-1"
                         per_port_requests {
                           interface {
                             origin: "openconfig"
                             elem {
                               name: "interface"
                               key { key: "name" value: "Ethernet0" }
                             }
                           }
                           prbs_polynomial: PRBS_POLYNOMIAL_PRBS23
                           test_duration_in_secs: $0
                         }
                       )PROTO",
                       kTesDurationInSecs);

  gnoi::diag::StartBERTRequest request;
  ASSERT_TRUE(google::protobuf::TextFormat::ParseFromString(kStartBertRequest,
                                                            &request));

  gnoi::diag::StartBERTResponse response;
  grpc::ClientContext context;
  LOG(INFO) << "Sending StartBERT request: " << request.ShortDebugString();

  EXPECT_THAT(gutil::GrpcStatusToAbslStatus(
                  sut_gnoi_diag_stub->StartBERT(&context, request, &response)),
              gutil::StatusIs(absl::StatusCode::kInvalidArgument,
                              testing::HasSubstr("too long")));
}

}  // namespace bert
