// Copyright 2021 Google LLC
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
#include <string>
#include <type_traits>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "google/protobuf/map.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/utils/ir.h"

namespace pdpi {
namespace {

using ::p4::v1::Action;
using ::p4::v1::ActionProfileAction;
using ::p4::v1::FieldMatch;
using ::p4::v1::TableAction;
using ::p4::v1::TableEntry;

absl::Status PadByteString(int bitwidth, std::string& bytes) {
  ASSIGN_OR_RETURN(bytes, ArbitraryToNormalizedByteString(bytes, bitwidth));
  return absl::OkStatus();
}

absl::Status PadFieldMatch(const IrTableDefinition& table, FieldMatch& match) {
  ASSIGN_OR_RETURN(
      const IrMatchFieldDefinition* match_field,
      gutil::FindPtrOrStatus(table.match_fields_by_id(), match.field_id()),
      _ << " while trying to lookup FieldMatch in IrTableDefinition: "
        << match.DebugString());
  int bitwidth = match_field->match_field().bitwidth();

  switch (match.field_match_type_case()) {
    case FieldMatch::kExact:
      RETURN_IF_ERROR(
          PadByteString(bitwidth, *match.mutable_exact()->mutable_value()))
              .SetAppend()
          << " in match field '" << match_field->match_field().name() << "'";
      break;
    case FieldMatch::kTernary:
      RETURN_IF_ERROR(
          PadByteString(bitwidth, *match.mutable_ternary()->mutable_value()))
              .SetAppend()
          << " in match field '" << match_field->match_field().name() << "'";
      RETURN_IF_ERROR(
          PadByteString(bitwidth, *match.mutable_ternary()->mutable_mask()))
              .SetAppend()
          << " in match field '" << match_field->match_field().name() << "'";
      break;
    case FieldMatch::kLpm:
      RETURN_IF_ERROR(
          PadByteString(bitwidth, *match.mutable_lpm()->mutable_value()))
              .SetAppend()
          << " in match field '" << match_field->match_field().name() << "'";
      break;
    case FieldMatch::kRange:
      RETURN_IF_ERROR(
          PadByteString(bitwidth, *match.mutable_range()->mutable_low()))
              .SetAppend()
          << " in match field '" << match_field->match_field().name() << "'";
      RETURN_IF_ERROR(
          PadByteString(bitwidth, *match.mutable_range()->mutable_high()))
              .SetAppend()
          << " in match field '" << match_field->match_field().name() << "'";
      break;
      break;
    case FieldMatch::kOptional:
      RETURN_IF_ERROR(
          PadByteString(bitwidth, *match.mutable_optional()->mutable_value()))
              .SetAppend()
          << " in match field '" << match_field->match_field().name() << "'";
      break;
    case FieldMatch::kOther:
    case FieldMatch::FIELD_MATCH_TYPE_NOT_SET:
      break;
  }
  return absl::OkStatus();
}

absl::Status PadAction(const IrP4Info& info, Action& action) {
  ASSIGN_OR_RETURN(
      const IrActionDefinition* action_info,
      gutil::FindPtrOrStatus(info.actions_by_id(), action.action_id()),
      _ << " while trying to lookup action in IrP4Info: "
        << action.DebugString());
  for (Action::Param& param : *action.mutable_params()) {
    ASSIGN_OR_RETURN(
        const auto* param_info,
        gutil::FindPtrOrStatus(action_info->params_by_id(), param.param_id()),
        _ << " while trying to lookup action param in IrP4Info: "
          << param.DebugString());
    int bitwidth = param_info->param().bitwidth();
    RETURN_IF_ERROR(PadByteString(bitwidth, *param.mutable_value())).SetAppend()
        << " in '" << param_info->param().name() << "' parameter of action '"
        << action_info->preamble().name() << "'";
  }
  return absl::OkStatus();
}

}  // namespace

absl::Status ZeroPadPiTableEntry(const IrP4Info& info, TableEntry& pi_entry) {
  ASSIGN_OR_RETURN(
      const IrTableDefinition* table_info,
      gutil::FindPtrOrStatus(info.tables_by_id(), pi_entry.table_id()),
      _ << " while trying to lookup table for entry in IrP4Info: "
        << pi_entry.DebugString());

  for (FieldMatch& match : *pi_entry.mutable_match()) {
    RETURN_IF_ERROR(PadFieldMatch(*table_info, match)).SetAppend()
        << " in table '" << table_info->preamble().name() << "'";
  }

  TableAction& action = *pi_entry.mutable_action();
  switch (action.type_case()) {
    case TableAction::kActionProfileMemberId:
    case TableAction::kActionProfileGroupId:
    case TableAction::TYPE_NOT_SET:
      break;
    case TableAction::kAction:
      RETURN_IF_ERROR(PadAction(info, *action.mutable_action())).SetAppend()
          << " in table '" << table_info->preamble().name() << "'";
      break;
    case TableAction::kActionProfileActionSet: {
      auto& action_set = *action.mutable_action_profile_action_set();
      for (ActionProfileAction& action :
           *action_set.mutable_action_profile_actions()) {
        RETURN_IF_ERROR(PadAction(info, *action.mutable_action())).SetAppend()
            << " in table '" << table_info->preamble().name() << "'";
      }
      break;
    }
  }

  return absl::OkStatus();
}

}  // namespace pdpi
