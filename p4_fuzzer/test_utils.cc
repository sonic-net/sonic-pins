// Copyright 2024 Google LLC
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
#include "p4_fuzzer/test_utils.h"

#include <string>

#include "absl/random/random.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/substitute.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_fuzzer/fuzz_util.h"
#include "p4_fuzzer/fuzzer_config.h"
#include "p4_fuzzer/switch_state.h"
#include "p4_pdpi/internal/ordered_map.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace p4_fuzzer {

FuzzerTestState ConstructFuzzerTestState(const pdpi::IrP4Info& ir_info,
                                         const std::string& role) {
  const FuzzerConfig config{
      .info = ir_info,
      .ports = {"1"},
      .qos_queues = {"0x1"},
      .role = role,
  };
  return FuzzerTestState{
      .config = config,
      .switch_state = SwitchState(ir_info),
  };
}

absl::StatusOr<pdpi::IrMatchFieldDefinition>
GetAMatchFieldDefinitionWithMatchType(
    const pdpi::IrTableDefinition& table_definition,
    p4::config::v1::MatchField::MatchType match_type) {
  for (const auto& [unused, match_field] :
       Ordered(table_definition.match_fields_by_id())) {
    if (match_field.match_field().match_type() == match_type) {
      return match_field;
    }
  }
  return absl::InvalidArgumentError(absl::Substitute(
      "The $0 table does not contain a match field of type $1.",
      table_definition.preamble().alias(),
      p4::config::v1::MatchField::MatchType_Name(match_type)));
}

absl::StatusOr<pdpi::IrTableDefinition> GetATableDefinitionWithMatchType(
    const FuzzerTestState& fuzzer_state,
    p4::config::v1::MatchField::MatchType match_type) {
  for (const auto& [unused, table] :
       Ordered(fuzzer_state.config.info.tables_by_id())) {
    if (GetAMatchFieldDefinitionWithMatchType(table, match_type).ok()) {
      return table;
    }
  }
  return absl::InvalidArgumentError(absl::StrCat(
      "The p4info does not contain a table that with a match of type ",
      p4::config::v1::MatchField::MatchType_Name(match_type)));
}

absl::StatusOr<pdpi::IrTableDefinition> GetAOneShotTableDefinition(
    const pdpi::IrP4Info& info) {
  for (const auto& [unused, table] : Ordered(info.tables_by_id())) {
    if (table.uses_oneshot()) {
      return table;
    }
  }
  return absl::InvalidArgumentError(
      "The p4info does not contain a table that uses one-shot action profile "
      "programming.");
}

absl::StatusOr<pdpi::IrActionProfileDefinition>
GetActionProfileImplementingTable(const pdpi::IrP4Info& info,
                                  const pdpi::IrTableDefinition& table) {
  if (table.implementation_id_case() !=
      pdpi::IrTableDefinition::kActionProfileId) {
    return absl::InvalidArgumentError(absl::Substitute(
        "The given table `$0` is not implemented by an action profile.",
        table.preamble().alias()));
  }
  auto action_profile_definition_iter =
      info.action_profiles_by_id().find(table.action_profile_id());
  if (action_profile_definition_iter != info.action_profiles_by_id().end()) {
    return action_profile_definition_iter->second;
  } else {
    return absl::InvalidArgumentError(absl::Substitute(
        "The action profile with id `$0` that implements the `$1` "
        "table does not exist in the p4info.",
        table.action_profile_id(), table.preamble().alias()));
  }
}

void SetMaxGroupSizeInActionProfile(
    pdpi::IrP4Info& info, pdpi::IrActionProfileDefinition& action_profile,
    const int max_group_size) {
  action_profile.mutable_action_profile()->set_max_group_size(max_group_size);

  const uint32_t id = action_profile.action_profile().preamble().id();
  const std::string name = action_profile.action_profile().preamble().alias();

  (*info.mutable_action_profiles_by_id())[id] = action_profile;
  (*info.mutable_action_profiles_by_name())[name] = action_profile;
}

}  // namespace p4_fuzzer
