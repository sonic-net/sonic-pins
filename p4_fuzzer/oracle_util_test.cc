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
#include "p4_fuzzer/oracle_util.h"

#include <bitset>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "gmock/gmock.h"
#include "google/rpc/code.pb.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"  // IWYU pragma: keep
#include "gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_fuzzer/fuzz_util.h"
#include "p4_fuzzer/fuzzer.pb.h"
#include "p4_fuzzer/switch_state.h"
#include "p4_fuzzer/test_utils.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

namespace p4_fuzzer {
namespace {

using ::absl::StatusCode;
using ::p4::v1::TableEntry;

int AclIngressTableSize() {
  return sai::GetIrP4Info(sai::Instantiation::kMiddleblock)
      .tables_by_name()
      .at("acl_ingress_table")
      .size();
}

// Return an Action Selector with >=2 actions to make it a more useful helper
// function.
absl::StatusOr<TableEntry> GetValidActionSelectorTableEntry(
    FuzzerTestState& fuzzer_state) {
  // If we want two or more actions, the max cardinality better be at least 2.
  CHECK_GE(kActionProfileActionSetMaxCardinality, 2);

  ASSIGN_OR_RETURN(
      const auto table_definition,
      GetAOneShotTableDefinition(fuzzer_state.config.GetIrP4Info()));

  ASSIGN_OR_RETURN(
      TableEntry table_entry,
      FuzzValidTableEntry(&fuzzer_state.gen, fuzzer_state.config,
                          fuzzer_state.switch_state, table_definition));

  // It is probabilistically highly unlikely that we don't get at least 2
  // actions in 1000 iterations, but this prevents infinite loops if there is a
  // bug.
  for (int loop_counter = 0; loop_counter < 1000; loop_counter++) {
    if (table_entry.action()
            .action_profile_action_set()
            .action_profile_actions_size() >= 2) {
      return table_entry;
    }
    ASSIGN_OR_RETURN(
        *table_entry.mutable_action()->mutable_action_profile_action_set(),
        FuzzActionProfileActionSet(&fuzzer_state.gen, fuzzer_state.config,
                                   fuzzer_state.switch_state,
                                   table_definition));
  }
  return absl::InternalError(
      "Failed to generate an action profile action set with more than "
      "two actions after 1000 iterations.");
}

// Return an Action Selector with >=2 actions, each with weight =
// max_group_size - 1.
absl::StatusOr<TableEntry> GetInvalidActionSelectorExceedingMaxGroupSize(
    FuzzerTestState& fuzzer_state) {
  ASSIGN_OR_RETURN(auto table_entry,
                   GetValidActionSelectorTableEntry(fuzzer_state));
  ASSIGN_OR_RETURN(
      const auto table_definition,
      GetAOneShotTableDefinition(fuzzer_state.config.GetIrP4Info()));

  ASSIGN_OR_RETURN(const auto action_profile,
                   GetActionProfileImplementingTable(
                       fuzzer_state.config.GetIrP4Info(), table_definition));

  int max_group_size = action_profile.action_profile().max_group_size();
  for (auto& action : *table_entry.mutable_action()
                           ->mutable_action_profile_action_set()
                           ->mutable_action_profile_actions()) {
    action.set_weight(max_group_size - 1);
  }
  return table_entry;
}

// Returns a ingress ACL table entry. Use integer arguments to vary match or
// action arguments.
TableEntry GetIngressAclTableEntry(int match, int action) {
  pdpi::IrTableEntry ir_table_entry =
      gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
        table_name: "acl_ingress_table"
        matches {
          name: "is_ipv4"
          optional { value { hex_str: "0x1" } }
        }
        matches {
          name: "dst_ip"
          ternary {
            value { ipv4: "0.0.0.0" }
            mask { ipv4: "255.255.255.255" }
          }
        }
        priority: 10
        action {
          name: "mirror"
          params {
            name: "mirror_session_id"
            value { str: "session" }
          }
        }
      )pb");
  *ir_table_entry.mutable_action()
       ->mutable_params(0)
       ->mutable_value()
       ->mutable_str() = absl::StrCat("session-", action);
  *ir_table_entry.mutable_matches(1)
       ->mutable_ternary()
       ->mutable_value()
       ->mutable_ipv4() =
      netaddr::Ipv4Address::OfBitset(std::bitset<32>(match)).ToString();
  auto result = pdpi::IrTableEntryToPi(
      sai::GetIrP4Info(sai::Instantiation::kMiddleblock), ir_table_entry);
  CHECK(result.ok()) << result.status();  // Crash OK
  return *result;
}

// An update and it's corresponding status.
struct UpdateStatus {
  AnnotatedUpdate update;
  StatusCode status;
};

// Checks whether the update+state combo is plausible or not
absl::Status Check(const std::vector<UpdateStatus>& updates,
                   const FuzzerTestState& fuzzer_state, bool valid) {
  AnnotatedWriteRequest request;
  std::vector<pdpi::IrUpdateStatus> statuses;
  for (const auto& [update, status] : updates) {
    *request.add_updates() = update;
    pdpi::IrUpdateStatus ir_update_status;
    ir_update_status.set_code(static_cast<google::rpc::Code>(status));
    statuses.push_back(ir_update_status);
  }
  std::optional<std::vector<std::string>> oracle =
      WriteRequestOracle(fuzzer_state.config.GetIrP4Info(), request, statuses,
                         fuzzer_state.switch_state);
  if (valid) {
    if (oracle.has_value()) {
      std::string explanation = absl::StrCat(
          "Expected the write request and statuses to be a valid combination, "
          "but they are not.",
          "\n", "errors reported:");
      for (const auto& error : oracle.value()) {
        explanation += absl::StrCat("\n", error);
      }
      return gutil::InvalidArgumentErrorBuilder() << explanation;
    }
  } else {
    if (!oracle.has_value()) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Expected the write request and statuses to not be a valid "
                "combination, "
                "but they are according to the oracle.";
    }
  }
  return absl::OkStatus();
}

UpdateStatus MakeInsert(const TableEntry& table_entry, StatusCode status) {
  AnnotatedUpdate annotated_update;
  p4::v1::Update* update = annotated_update.mutable_pi();
  update->set_type(p4::v1::Update::INSERT);
  *update->mutable_entity()->mutable_table_entry() = table_entry;
  return {annotated_update, status};
}

UpdateStatus MakeDelete(const TableEntry& table_entry, StatusCode status) {
  AnnotatedUpdate annotated_update;
  p4::v1::Update* update = annotated_update.mutable_pi();
  update->set_type(p4::v1::Update::DELETE);
  *update->mutable_entity()->mutable_table_entry() = table_entry;
  return {annotated_update, status};
}

// Add a table entry to a state.
void AddTableEntry(const TableEntry& table_entry, SwitchState* state) {
  auto status = state->ApplyUpdate(
      MakeInsert(table_entry, absl::StatusCode::kOk).update.pi());
  CHECK(status.ok());
}

// TODO: Enable this test after batching is handled correctly.
TEST(OracleUtilTest, DISABLED_SameKeyInBatch) {
  // Two entries, same key but different values/actions.
  TableEntry table_entry_1 = GetIngressAclTableEntry(/*match=*/0, /*action=*/1);
  TableEntry table_entry_2 = GetIngressAclTableEntry(/*match=*/0, /*action=*/2);
  FuzzerTestState fuzzer_state = ConstructFuzzerTestStateFromSaiMiddleBlock();

  // Same key should be rejected.
  EXPECT_OK(
      Check({MakeInsert(table_entry_1, absl::StatusCode::kOk),
             MakeInsert(table_entry_2, absl::StatusCode::kInvalidArgument)},
            fuzzer_state, /*valid=*/false));
  EXPECT_OK(
      Check({MakeInsert(table_entry_1, absl::StatusCode::kInvalidArgument),
             MakeInsert(table_entry_2, absl::StatusCode::kOk)},
            fuzzer_state, /*valid=*/false));
  EXPECT_OK(
      Check({MakeInsert(table_entry_1, absl::StatusCode::kInvalidArgument),
             MakeInsert(table_entry_2, absl::StatusCode::kInvalidArgument)},
            fuzzer_state, /*valid=*/true));

  // Even if some are insert and some are delete
  EXPECT_OK(
      Check({MakeDelete(table_entry_1, absl::StatusCode::kInvalidArgument),
             MakeInsert(table_entry_2, absl::StatusCode::kInvalidArgument)},
            fuzzer_state, /*valid=*/true));
}

TEST(OracleUtilTest, ResourcesCanBeExhaustedInFullState) {
  FuzzerTestState full_state = ConstructStandardFuzzerTestState();

  // Get a prototype table entry.
  ASSERT_OK_AND_ASSIGN(
      const auto table,
      GetATableDefinitionWithMatchType(
          full_state, p4::config::v1::MatchField_MatchType_EXACT));
  ASSERT_OK_AND_ASSIGN(const auto match_field,
                       GetAMatchFieldDefinitionWithMatchType(
                           table, p4::config::v1::MatchField_MatchType_EXACT));
  ASSERT_OK_AND_ASSIGN(auto table_entry_prototype,
                       FuzzValidTableEntry(&full_state.gen, full_state.config,
                                           full_state.switch_state, table));

  // Ensure that the parameter number matches up with the field id. This is a
  // convenience and can be replaced with a loop if it ever turns out to be
  // false.
  const int match_field_index = match_field.match_field().id() - 1;
  ASSERT_EQ(table_entry_prototype.mutable_match(match_field_index)->field_id(),
            match_field.match_field().id());

  // Fill up the state.
  for (int i = 1; i <= table.size(); i++) {
    TableEntry table_entry = table_entry_prototype;
    table_entry.mutable_match(match_field_index)
        ->mutable_exact()
        ->set_value(absl::StrCat(i));
    AddTableEntry(table_entry, &full_state.switch_state);
  }

  TableEntry next = table_entry_prototype;
  next.mutable_match(match_field_index)
      ->mutable_exact()
      ->set_value(absl::StrCat(table.size() + 1));

  // Inserting into full table is okay.
  EXPECT_OK(Check({MakeInsert(next, absl::StatusCode::kOk)}, full_state,
                  /*valid=*/true));

  // Resource exhasted is okay too.
  EXPECT_OK(Check({MakeInsert(next, absl::StatusCode::kResourceExhausted)},
                  full_state,
                  /*valid=*/true));
}

TEST(OracleUtilTest, ResourcesCanBeExhaustedInAlmostFullStateWithBatch) {
  FuzzerTestState almost_full_state = ConstructStandardFuzzerTestState();

  // Get a prototype table entry.
  ASSERT_OK_AND_ASSIGN(
      const auto table,
      GetATableDefinitionWithMatchType(
          almost_full_state, p4::config::v1::MatchField_MatchType_EXACT));
  ASSERT_OK_AND_ASSIGN(const auto match_field,
                       GetAMatchFieldDefinitionWithMatchType(
                           table, p4::config::v1::MatchField_MatchType_EXACT));
  ASSERT_OK_AND_ASSIGN(
      auto table_entry_prototype,
      FuzzValidTableEntry(&almost_full_state.gen, almost_full_state.config,
                          almost_full_state.switch_state, table));

  // Ensure that the parameter number matches up with the field id. This is a
  // convenience and can be replaced with a loop if it ever turns out to be
  // false.
  const int match_field_index = match_field.match_field().id() - 1;
  ASSERT_TRUE(
      table_entry_prototype.mutable_match(match_field_index)->field_id() ==
      match_field.match_field().id());

  // Make the state almost full (1 entry remaining).
  for (int i = 1; i <= table.size() - 1; i++) {
    TableEntry table_entry = table_entry_prototype;
    table_entry.mutable_match(match_field_index)
        ->mutable_exact()
        ->set_value(absl::StrCat(i));
    AddTableEntry(table_entry, &almost_full_state.switch_state);
  }

  TableEntry next1 = table_entry_prototype;
  TableEntry next2 = table_entry_prototype;
  next1.mutable_match(match_field_index)
      ->mutable_exact()
      ->set_value(absl::StrCat(table.size() + 1));
  next2.mutable_match(match_field_index)
      ->mutable_exact()
      ->set_value(absl::StrCat(table.size() + 2));

  // Resource exhausted is not okay.
  EXPECT_OK(Check({MakeInsert(next1, absl::StatusCode::kResourceExhausted)},
                  almost_full_state, /*valid=*/false));

  // Inserting two flows, one of them can fail.
  EXPECT_OK(Check({MakeInsert(next1, absl::StatusCode::kOk),
                   MakeInsert(next2, absl::StatusCode::kResourceExhausted)},
                  almost_full_state, /*valid=*/true));
  EXPECT_OK(Check({MakeInsert(next1, absl::StatusCode::kResourceExhausted),
                   MakeInsert(next2, absl::StatusCode::kOk)},
                  almost_full_state, /*valid=*/true));
  EXPECT_OK(Check({MakeInsert(next1, absl::StatusCode::kOk),
                   MakeInsert(next2, absl::StatusCode::kOk)},
                  almost_full_state, /*valid=*/true));
}

// TODO: Enable this test once the Oracle properly rejects empty
// strings for values.
TEST(OracleUtilTest, DISABLED_EmptyValuesAreInvalid) {
  FuzzerTestState fuzzer_state = ConstructStandardFuzzerTestState();
  ASSERT_OK_AND_ASSIGN(TableEntry entry,
                       GetValidActionSelectorTableEntry(fuzzer_state));

  // TODO: The fuzzer currently sometimes constructs empty values.
  // This assertion, and the one below, may fail until this bug is fixed.
  // The table entry should be valid before we make it invalid.
  ASSERT_OK(Check({MakeInsert(entry, absl::StatusCode::kOk)}, fuzzer_state,
                  /*valid=*/true));

  // Set all values to be empty.
  for (auto& action : *entry.mutable_action()
                           ->mutable_action_profile_action_set()
                           ->mutable_action_profile_actions()) {
    ASSERT_STRNE(action.action().params(0).value().c_str(), "");
    action.mutable_action()->mutable_params(0)->set_value("");
  }

  // Empty values are malformed.
  EXPECT_OK(Check({MakeInsert(entry, absl::StatusCode::kInvalidArgument)},
                  fuzzer_state, /*valid=*/true));
  EXPECT_OK(Check({MakeInsert(entry, absl::StatusCode::kOk)}, fuzzer_state,
                  /*valid=*/false));
}

// TODO: Enable this test once the oracle correctly rules out
// action selectors with total weight > the max_group_size
// parameter.
TEST(OracleUtilTest, DISABLED_ActionSelectorWeightSumCannotExceedMaxGroupSize) {
  FuzzerTestState fuzzer_state = ConstructStandardFuzzerTestState();
  ASSERT_OK_AND_ASSIGN(
      TableEntry entry,
      GetInvalidActionSelectorExceedingMaxGroupSize(fuzzer_state));

  // Weight > max_group_size is malformed.
  EXPECT_OK(Check({MakeInsert(entry, absl::StatusCode::kInvalidArgument)},
                  fuzzer_state, /*valid=*/true));
  EXPECT_OK(Check({MakeInsert(entry, absl::StatusCode::kOk)}, fuzzer_state,
                  /*valid=*/false));
}

}  // namespace
}  // namespace p4_fuzzer
