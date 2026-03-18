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

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "gmock/gmock.h"
#include "google/protobuf/descriptor.h"
#include "google/protobuf/message.h"
#include "google/rpc/code.pb.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/main_p4_pd.pb.h"
#include "p4_infra/p4_pdpi/pd.h"

constexpr char kPdUpdatestatus[] =
    R"pb(code: UNKNOWN, message: "some_message")pb";

namespace pdpi {
namespace {

TEST(GetEnumValueInProtoByReflectionTest, GetValidValue) {
  auto pd_update_status =
      gutil::ParseProtoOrDie<pdpi::UpdateStatus>(kPdUpdatestatus);
  ASSERT_OK_AND_ASSIGN(int enum_code, GetEnumField(pd_update_status, "code"));
  EXPECT_EQ(static_cast<google::rpc::Code>(enum_code), pd_update_status.code());
}

TEST(GetEnumValueInProtoByReflectionTest, GetInvalidField) {
  auto pd_update_status =
      gutil::ParseProtoOrDie<pdpi::UpdateStatus>(kPdUpdatestatus);
  auto status_or_enum_code =
      GetEnumField(pd_update_status, "non_existing_field");
  EXPECT_THAT(status_or_enum_code,
              gutil::StatusIs(absl::StatusCode::kInvalidArgument));
}

// For proto with invalid enum value, GetEnumField should return non-ok status.
TEST(GetEnumValueInProtoByReflectionTest, GetInvalidValue) {
  auto pd_update_status =
      gutil::ParseProtoOrDie<pdpi::UpdateStatus>(kPdUpdatestatus);
  auto* field_descriptor =
      pd_update_status.GetDescriptor()->FindFieldByName("code");
  ASSERT_NE(field_descriptor, nullptr);
  int invalid_enum_value = 42;
  pd_update_status.GetReflection()->SetEnumValue(
      &pd_update_status, field_descriptor, invalid_enum_value);
  int returned_enum_value = pd_update_status.GetReflection()->GetEnumValue(
      pd_update_status, field_descriptor);
  ASSERT_EQ(returned_enum_value, invalid_enum_value);
  EXPECT_THAT(GetEnumField(pd_update_status, "code"),
              gutil::StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(SetEnumValueInProtoByReflectionTest, SetEnumWithValidEnumValue) {
  auto pd_update_status =
      gutil::ParseProtoOrDie<pdpi::UpdateStatus>(kPdUpdatestatus);
  ASSERT_OK(SetEnumField(&pd_update_status, "code",
                         static_cast<int>(google::rpc::Code::UNIMPLEMENTED)));
  EXPECT_EQ(pd_update_status.code(), google::rpc::Code::UNIMPLEMENTED);
}

TEST(SetEnumValueInProtoByReflectionTest, SetEnumWithInvalidEnumValue) {
  auto pd_update_status =
      gutil::ParseProtoOrDie<pdpi::UpdateStatus>(kPdUpdatestatus);
  int invalid_enum_value = 42;
  auto status_or_enum_code =
      SetEnumField(&pd_update_status, "code", invalid_enum_value);
  ASSERT_FALSE(status_or_enum_code.ok());
}

TEST(SetEnumValueInProtoByReflectionTest, SetEnumWithInvalidFieldName) {
  auto pd_update_status =
      gutil::ParseProtoOrDie<pdpi::UpdateStatus>(kPdUpdatestatus);
  auto status_or_enum_code =
      SetEnumField(&pd_update_status, "non_existing_field",
                   static_cast<int>(google::rpc::OK));
  ASSERT_FALSE(status_or_enum_code.ok());
}

}  // namespace
}  // namespace pdpi
