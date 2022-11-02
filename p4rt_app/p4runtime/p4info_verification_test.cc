// Copyright 2020 Google LLC
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
#include "p4rt_app/p4runtime/p4info_verification.h"

#include "absl/status/status.h"
#include "absl/strings/match.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "google/protobuf/text_format.h"
#include "gtest/gtest.h"
#include "gutil/proto.h"
#include "gutil/proto_matchers.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/utils/ir.h"
#include "p4rt_app/utils/status_utility.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace p4rt_app {
namespace {

using ::gutil::EqualsProto;
using ::gutil::StatusIs;
using ::testing::Eq;
using ::testing::HasSubstr;
using ::testing::Not;
using ::testing::Optional;

class InstantiationTest : public testing::TestWithParam<sai::Instantiation> {};
TEST_P(InstantiationTest, SaiP4InfoIsOk) {
  EXPECT_OK(ValidateP4Info(sai::GetP4Info(GetParam())));
}

INSTANTIATE_TEST_SUITE_P(P4InfoVerificationTest, InstantiationTest,
                         testing::ValuesIn(sai::AllInstantiations()),
                         [](testing::TestParamInfo<sai::Instantiation> info) {
                           return sai::InstantiationToString(info.param);
                         });

TEST(P4InfoVerificationTest, MissingPacketIoMetadata) {
  p4::config::v1::P4Info p4info =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  // Use the expected packet in/out metadata, but remove the first metadata
  // field.
  auto& metadata =
      *p4info.mutable_controller_packet_metadata(0)->mutable_metadata();
  metadata.erase(metadata.begin());

  EXPECT_THAT(ValidateP4Info(p4info),
              gutil::StatusIs(absl::StatusCode::kInvalidArgument,
                              HasSubstr("PacketIO")));
}

TEST(P4InfoVerificationTest, ReturnsErrorWhenIrParsingFails) {
  p4::config::v1::P4Info p4info =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);
  p4info.mutable_actions()->erase(p4info.mutable_actions()->begin());
  auto validate_p4info_status = ValidateP4Info(p4info);
  EXPECT_FALSE(validate_p4info_status.ok());
  EXPECT_THAT(validate_p4info_status.GetPayload(kLibraryUrl),
              Optional(Eq("PDPI")))
      << "Error was not from the PDPI call as expected.";
}

TEST(P4InfoVerificationTest, ReturnsErrorWhenSchemaVerificationFails) {
  p4::config::v1::P4Info p4info =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);
  // Change the match type of amatch field from a fixed routing table.
  for (auto& table : *p4info.mutable_tables()) {
    if (absl::StartsWith(table.preamble().name(), "ingress.routing")) {
      for (auto& match_field : *table.mutable_match_fields()) {
        if (match_field.match_type() == match_field.LPM) {
          match_field.set_match_type(match_field.EXACT);
          break;
        }
      }
    }
  }
  ASSERT_THAT(
      p4info,
      Not(EqualsProto(sai::GetP4Info(sai::Instantiation::kMiddleblock))))
      << "Failed to find candidate LPM match field to modify for the test.";

  EXPECT_THAT(
      ValidateP4Info(p4info),
      gutil::StatusIs(absl::StatusCode::kInvalidArgument, HasSubstr("LPM")));
}

}  // namespace
}  // namespace p4rt_app
