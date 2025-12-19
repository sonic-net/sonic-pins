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

#include "p4_pdpi/ir_tools.h"

#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/config/v1/p4types.pb.h"
#include "p4_pdpi/ir.pb.h"

namespace pdpi {
namespace {

// Calls given `transformer` on any parameters of `target_type` in
// `action`.
absl::Status TransformValuesOfType(
    const IrP4Info& info, const p4::config::v1::P4NamedType& target_type,
    IrActionInvocation& action,
    const std::function<absl::StatusOr<std::string>(absl::string_view)>&
        transformer) {
  ASSIGN_OR_RETURN(const IrActionDefinition& action_def,
                   gutil::FindOrStatus(info.actions_by_name(), action.name()));
  // For every parameter in the action, call the `transformer` on it if it has
  // `target_type`.
  for (auto& param : *action.mutable_params()) {
    ASSIGN_OR_RETURN(
        const pdpi::IrActionDefinition::IrActionParamDefinition& param_def,
        gutil::FindOrStatus(action_def.params_by_name(), param.name()));
    if (param_def.param().type_name().name() == target_type.name()) {
      ASSIGN_OR_RETURN(*param.mutable_value()->mutable_str(),
                       transformer(param.value().str()));
    }
  }
  return absl::OkStatus();
}

// Calls given `transformer` on the `match` value if it has `target_type`.
absl::Status TransformValuesOfType(
    const IrTableDefinition& table_def,
    const p4::config::v1::P4NamedType& target_type, IrMatch& match,
    const std::function<absl::StatusOr<std::string>(absl::string_view)>&
        transformer) {
  ASSIGN_OR_RETURN(
      const pdpi::IrMatchFieldDefinition& match_def,
      gutil::FindOrStatus(table_def.match_fields_by_name(), match.name()));

  // If the match is of named type, call the function on it.
  if (match_def.match_field().type_name().name() == target_type.name()) {
    switch (match.match_value_case()) {
      case IrMatch::kExact: {
        ASSIGN_OR_RETURN(*match.mutable_exact()->mutable_str(),
                         transformer(match.exact().str()));
        return absl::OkStatus();
      }
      case IrMatch::kOptional:
        if (match.optional().has_value()) {
          ASSIGN_OR_RETURN(
              *match.mutable_optional()->mutable_value()->mutable_str(),
              transformer(match.optional().value().str()));
        }
        return absl::OkStatus();
      case IrMatch::kLpm:
        // Note that it is unclear what the semantics of this should be due to
        // masks.
        if (match.lpm().has_value()) {
          ASSIGN_OR_RETURN(*match.mutable_lpm()->mutable_value()->mutable_str(),
                           transformer(match.lpm().value().str()));
        }
        return absl::OkStatus();
      case IrMatch::kTernary:
        // Note that it is unclear what the semantics of this should be due to
        // masks.
        if (match.ternary().has_value()) {
          ASSIGN_OR_RETURN(
              *match.mutable_ternary()->mutable_value()->mutable_str(),
              transformer(match.ternary().value().str()));
        }
        return absl::OkStatus();
      default:
        return absl::OkStatus();
    }
  }
  return absl::OkStatus();
}

}  // namespace

absl::Status TransformValuesOfType(
    const IrP4Info& info, const p4::config::v1::P4NamedType& target_type,
    IrTableEntry& entry,
    const std::function<absl::StatusOr<std::string>(absl::string_view)>&
        transformer) {
  ASSIGN_OR_RETURN(
      const pdpi::IrTableDefinition& table_def,
      gutil::FindOrStatus(info.tables_by_name(), entry.table_name()));

  // If the entry has an action set, then call function on every action.
  if (entry.has_action_set()) {
    for (auto& action : *entry.mutable_action_set()->mutable_actions()) {
      RETURN_IF_ERROR(TransformValuesOfType(
          info, target_type, *action.mutable_action(), transformer));
    }
  }

  if (entry.has_action()) {
    RETURN_IF_ERROR(TransformValuesOfType(
        info, target_type, *entry.mutable_action(), transformer));
  }

  for (auto& match : *entry.mutable_matches()) {
    RETURN_IF_ERROR(
        TransformValuesOfType(table_def, target_type, match, transformer));
  }
  return absl::OkStatus();
}

absl::Status TransformValuesOfType(
    const IrP4Info& info, const p4::config::v1::P4NamedType& target_type,
    std::vector<IrTableEntry>& entries,
    const std::function<absl::StatusOr<std::string>(absl::string_view)>&
        transformer) {
  for (IrTableEntry& entry : entries) {
    RETURN_IF_ERROR(
        TransformValuesOfType(info, target_type, entry, transformer));
  }
  return absl::OkStatus();
}

// This implementation is inefficient because it uses `TransformValuesOfType`,
// which also means that it needs to copy its input entries, in order to not
// transform them.
// TODO: Implement a more efficient version if required.
absl::Status VisitValuesOfType(
    const IrP4Info& info, const p4::config::v1::P4NamedType& target_type,
    std::vector<IrTableEntry> entries,
    const absl::AnyInvocable<absl::Status(absl::string_view) const>& visitor) {
  return TransformValuesOfType(
      info, target_type, entries,
      /*transformer=*/
      [&](absl::string_view input) -> absl::StatusOr<std::string> {
        RETURN_IF_ERROR(visitor(input));
        return "";
      });
}

}  // namespace pdpi
