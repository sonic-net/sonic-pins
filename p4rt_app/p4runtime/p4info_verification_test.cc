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

#include "absl/algorithm/container.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
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
using ::gutil::IsOk;
using ::gutil::StatusIs;
using ::testing::Eq;
using ::testing::HasSubstr;
using ::testing::Not;
using ::testing::Optional;

bool IsAclTable(const p4::config::v1::Table& table) {
  return absl::c_any_of(table.preamble().annotations(),
                        [](absl::string_view annotation) {
                          return absl::StartsWith(annotation, "@sai_acl");
                        });
}

bool IsAclAction(const p4::config::v1::Action& action) {
  return absl::c_any_of(action.preamble().annotations(),
                        [](absl::string_view annotation) {
                          return absl::StartsWith(annotation, "@sai_action");
                        });
}

template <class Entity>
bool IsSupported(const Entity& entity) {
  return !absl::c_any_of(entity.preamble().annotations(),
                         [](absl::string_view annotation) {
                           return annotation == "@unsupported";
                         });
}

p4::config::v1::Table* GetSupportedAclTable(p4::config::v1::P4Info& p4info) {
  for (auto& table : *p4info.mutable_tables()) {
    if (IsAclTable(table) && IsSupported(table)) return &table;
  }
  return nullptr;
}

p4::config::v1::Table* GetSupportedNonAclTable(p4::config::v1::P4Info& p4info) {
  for (auto& table : *p4info.mutable_tables()) {
    if (!IsAclTable(table) && IsSupported(table)) return &table;
  }
  return nullptr;
}

p4::config::v1::Action* GetRemovableAclAction(p4::config::v1::P4Info& p4info) {
  // We want an ACL action that is not the only action of any table.
  // `acl_forward` is currently guaranteed to have this property.
  for (auto& action : *p4info.mutable_actions()) {
    if (action.preamble().alias() == "acl_forward") return &action;
  }
  return nullptr;
}

p4::config::v1::Action* GetSupportedNonAclAction(
    p4::config::v1::P4Info& p4info) {
  for (auto& action : *p4info.mutable_actions()) {
    if (!IsAclAction(action) && IsSupported(action)) return &action;
  }
  return nullptr;
}

class InstantiationTest : public testing::TestWithParam<sai::Instantiation> {};
TEST_P(InstantiationTest, SaiP4InfoIsOk) {
  EXPECT_OK(ValidateP4Info(sai::GetP4Info(GetParam())));
}

INSTANTIATE_TEST_SUITE_P(P4InfoVerificationTest, InstantiationTest,
                         testing::ValuesIn(sai::AllSaiInstantiations()),
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

TEST(P4InfoVerificationTest, ToleratesUnsupportedTable) {
  p4::config::v1::P4Info p4info =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  // A random `@unsupported` table is tolerated.
  *p4info.add_tables()->mutable_preamble()->add_annotations() = "@unsupported";
  EXPECT_THAT(ValidateP4Info(p4info), IsOk());

  // In contrast, a random table without that annotation is not tolerated.
  p4info.add_tables();
  EXPECT_THAT(ValidateP4Info(p4info), Not(IsOk()));
}

TEST(P4InfoVerificationTest, ToleratesUnsupportedAclMatchField) {
  p4::config::v1::P4Info p4info =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  // Pick a random ACL table.
  auto* acl_table = GetSupportedAclTable(p4info);
  ASSERT_NE(acl_table, nullptr);
  SCOPED_TRACE(absl::StrCat("table name: ", acl_table->preamble().name()));

  // Add a random match field.
  auto& match_field = *acl_table->add_match_fields();
  ASSERT_OK_AND_ASSIGN(match_field,
                       gutil::ParseTextProto<p4::config::v1::MatchField>(R"pb(
                         id: 12345678
                         name: "unsupported_match_field"
                         bitwidth: 10
                         match_type: TERNARY
                       )pb"));

  // Validation fails because match field is invalid...
  EXPECT_THAT(
      ValidateP4Info(p4info),
      StatusIs(absl::StatusCode::kInvalidArgument,
               HasSubstr("failed ACL table verification. Failed to process "
                         "match field 'unsupported_match_field'")));

  // ...unless we add an `@unsupported` annotation.
  *match_field.add_annotations() = "@unsupported";
  EXPECT_THAT(ValidateP4Info(p4info), IsOk());
}

TEST(P4InfoVerificationTest, ToleratesUnsupportedNonAclMatchField) {
  p4::config::v1::P4Info p4info =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  // Pick a random non-ACL table.
  auto* table = GetSupportedNonAclTable(p4info);
  ASSERT_NE(table, nullptr);
  SCOPED_TRACE(absl::StrCat("table name: ", table->preamble().name()));

  // Add a unknown match field.
  auto& match_field = *table->add_match_fields();
  ASSERT_OK_AND_ASSIGN(match_field,
                       gutil::ParseTextProto<p4::config::v1::MatchField>(R"pb(
                         id: 12345678
                         name: "unsupported_match_field"
                         bitwidth: 10
                         match_type: TERNARY
                       )pb"));

  // Validation fails because match field is unknown...
  EXPECT_THAT(
      ValidateP4Info(p4info),
      StatusIs(
          absl::StatusCode::kNotFound,
          HasSubstr("contains unknown match field 'unsupported_match_field'")));

  // ...unless we add an `@unsupported` annotation.
  *match_field.add_annotations() = "@unsupported";
  EXPECT_THAT(ValidateP4Info(p4info), IsOk());
}

TEST(P4InfoVerificationTest, ToleratesUnsupportedAclAction) {
  p4::config::v1::P4Info p4info =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  // Pick a random ACL table.
  auto* acl_table = GetSupportedAclTable(p4info);
  ASSERT_NE(acl_table, nullptr);
  SCOPED_TRACE(absl::StrCat("table name: ", acl_table->preamble().name()));

  // Pick a random non-ACL action. This cannot be an ACL action, because adding
  // those is always allowed anyhow.
  auto* action = GetSupportedNonAclAction(p4info);
  ASSERT_NE(action, nullptr);
  SCOPED_TRACE(absl::StrCat("action: ", action->preamble().name()));

  // Add action to table.
  p4::config::v1::ActionRef& action_ref = *acl_table->add_action_refs();
  action_ref.set_id(action->preamble().id());
  action_ref.set_scope(p4::config::v1::ActionRef::TABLE_ONLY);
  *action_ref.add_annotations() = "@proto_id(42)";

  // Validation fails because action is unknown...
  EXPECT_THAT(ValidateP4Info(p4info),
              StatusIs(absl::StatusCode::kInvalidArgument,
                       HasSubstr("failed ACL table verification")));

  // ...unless we mark the action as @unsupported.
  *action->mutable_preamble()->add_annotations() = "@unsupported";
  EXPECT_THAT(ValidateP4Info(p4info), IsOk());
}

TEST(P4InfoVerificationTest, ToleratesUnsupportedNonAclAction) {
  p4::config::v1::P4Info p4info =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  // Pick a random non-ACL table.
  auto* table = GetSupportedNonAclTable(p4info);
  ASSERT_NE(table, nullptr);
  SCOPED_TRACE(absl::StrCat("table = ", table->preamble().name()));

  // Choose an action that is both not supported by this table and safe to
  // remove from the overall P4 program.
  p4::config::v1::Action* unexpected_action = GetRemovableAclAction(p4info);
  ASSERT_NE(unexpected_action, nullptr);
  SCOPED_TRACE(absl::StrCat("action = ", unexpected_action->preamble().name()));

  // Add action to table.
  p4::config::v1::ActionRef& action_ref = *table->add_action_refs();
  action_ref.set_id(unexpected_action->preamble().id());
  action_ref.set_scope(p4::config::v1::ActionRef::TABLE_ONLY);
  *action_ref.add_annotations() = "@proto_id(42)";

  // Validation fails because action is unknown...
  EXPECT_THAT(ValidateP4Info(p4info), StatusIs(absl::StatusCode::kNotFound,
                                               HasSubstr("unknown action")));

  // ...unless we mark the action as @unsupported.
  *unexpected_action->mutable_preamble()->add_annotations() = "@unsupported";
  EXPECT_THAT(ValidateP4Info(p4info), IsOk());
}

}  // namespace
}  // namespace p4rt_app
