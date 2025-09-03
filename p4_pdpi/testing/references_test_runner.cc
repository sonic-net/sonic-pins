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

#include <iostream>
#include <string>
#include <vector>

#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/pd.h"
#include "p4_pdpi/references.h"
#include "p4_pdpi/testing/main_p4_pd.pb.h"
#include "p4_pdpi/testing/test_helper.h"
#include "p4_pdpi/testing/test_p4info.h"

namespace pdpi {
namespace {

constexpr absl::string_view kInputBanner =
    "-- INPUT --------------------------------------------------------------\n";
const absl::string_view kOutputBanner =
    "-- OUTPUT -------------------------------------------------------------\n";

struct ConcreteTableReferenceTestCase {
  // PD representation of PI entity used to generate outgoing/possible-incoming
  // table references. Valid entities must meet the following requirements:
  // - Entity must be valid for main.p4 program.
  // - Must belong to `reference_info.source_table` when creating outgoing
  // references.
  // - Must belong to `reference_info.destination_table` when creating possible
  // incoming references.
  pdpi::TableEntry entity;
  // Reference information used to to create table references from `entity`.
  IrTableReference reference_info;
  // Description of test case.
  std::string description;
};

std::vector<ConcreteTableReferenceTestCase>
OutgoingConcreteTableReferencesTestCases() {
  std::vector<ConcreteTableReferenceTestCase> test_cases;

  pdpi::TableEntry p4_entry = gutil::ParseProtoOrDie<pdpi::TableEntry>(
      R"pb(golden_test_friendly_table_entry {
             match { key1: "key-a" key2: "key-b" }
             action {
               golden_test_friendly_action { arg1: "arg1" arg2: "arg2" }
             }
           })pb");

  // Error test cases.
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { p4_table { table_name: "wrong_table" table_id: 7 } }
        destination_table { p4_table { table_name: "other_table" } }
        field_references {
          source {
            match_field { p4_match_field { field_name: "key1" field_id: 1 } }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
      )pb"),
      .description = "Fails if entity does not belong to source table",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table {
          p4_table {
            table_name: "golden_test_friendly_table"
            table_id: 50151603
          }
        }
        destination_table { p4_table { table_name: "other_table" } }
        field_references {
          source {
            match_field {
              p4_match_field { field_name: "missing_field" field_id: 7 }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
      )pb"),
      .description = "Fails if entity is missing non-optional field",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table {
          p4_table {
            table_name: "golden_test_friendly_table"
            table_id: 50151603
          }
        }
        destination_table { p4_table { table_name: "other_table" } }
        field_references {
          source {
            match_field { p4_match_field { field_name: "key_1" field_id: 1 } }
          }
          destination {
            match_field {
              p4_match_field { field_name: "optional_field" is_optional: true }
            }
          }
        }
      )pb"),
      .description = "Fails if entity refers to optional field",
  });
  // NOTE: Similar errors are encountered for the following:
  // P4MatchField-Refers-To-P4ActionField
  // P4MatchField-Refers-To-BuiltInActionField
  // BuiltInMatchField-Refers-To-P4ActionField
  // BuiltInMatchField-Refers-To-BuiltInActionField
  // P4ActionField-Refers-To-P4ActionField
  // P4ActionField-Refers-To-BuiltInActionField
  // BuiltInActionField-Refers-To-P4ActionField
  // BuiltInField-Refers-To-BuiltInActionField
  // Only the first is tested to avoid redundancy.
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table {
          p4_table {
            table_name: "golden_test_friendly_table"
            table_id: 50151603
          }
        }
        destination_table { p4_table { table_name: "other_table" } }
        field_references {
          source {
            match_field { p4_match_field { field_name: "key1" field_id: 1 } }
          }
          destination {
            action_field {
              p4_action_field {
                action_name: "other_action"
                parameter_name: "other_arg"
              }
            }
          }
        }
      )pb"),
      .description = "Fails for unsupported reference type (i.e. "
                     "P4MatchField-Refers-To-P4ActionField)",
  });

  // Fundamental test cases testing single field relationships.
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table {
          p4_table {
            table_name: "golden_test_friendly_table"
            table_id: 50151603
          }
        }
        destination_table { p4_table { table_name: "other_table" } }
      )pb"),
      .description = "No field references creates no concrete references",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table {
          p4_table {
            table_name: "golden_test_friendly_table"
            table_id: 50151603
          }
        }
        destination_table { p4_table { table_name: "other_table" } }
        field_references {
          source {
            match_field { p4_match_field { field_name: "key1" field_id: 1 } }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
      )pb"),
      .description =
          "P4MatchField-Refers-To-P4MatchField reference creates a single "
          "concrete reference.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table {
          p4_table {
            table_name: "golden_test_friendly_table"
            table_id: 50151603
          }
        }
        destination_table { p4_table { table_name: "other_table" } }
        field_references {
          source {
            match_field {
              p4_match_field {
                field_name: "key1"
                field_id: 1
                is_optional: true
              }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
      )pb"),
      .description =
          "P4MatchField-Refers-To-P4MatchField reference creates a single "
          "concrete reference for present optional field.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table {
          p4_table {
            table_name: "golden_test_friendly_table"
            table_id: 50151603
          }
        }
        destination_table { p4_table { table_name: "other_table" } }
        field_references {
          source {
            match_field {
              p4_match_field {
                field_name: "optional_field"
                field_id: 7
                is_optional: true
              }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
      )pb"),
      .description = "P4MatchField-Refers-To-P4MatchField reference creates no "
                     "concrete reference for absent optional field.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table {
          p4_table {
            table_name: "golden_test_friendly_table"
            table_id: 50151603
          }
        }
        destination_table { p4_table { table_name: "other_table" } }
        field_references {
          source {
            match_field { p4_match_field { field_name: "key1" field_id: 1 } }
          }
          destination {
            match_field {
              built_in_match_field: BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID
            }
          }
        }
      )pb"),
      .description =
          "P4MatchField-Refers-To-BuiltInMatchField reference creates a "
          "single concrete reference.",
  });
  
    pdpi::TableEntry built_in_entry_with_multiple_actions =
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        multicast_group_table_entry {
          match { multicast_group_id: "0x0037" }
          action {
            replicate {
              replicas { port: "port_1" instance: "0x0031" }
              replicas { port: "port_2" instance: "0x0032" }
            }
          }
        }
      )pb");

  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = built_in_entry_with_multiple_actions,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { built_in_table: BUILT_IN_TABLE_MULTICAST_GROUP_TABLE }
        destination_table { p4_table { table_name: "other_table" } }
        field_references {
          source {
            match_field {
              built_in_match_field: BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID
            }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
      )pb"),
      .description =
          "BuiltInMatchField-Refers-To-P4MatchField reference creates a "
          "single concrete reference.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = built_in_entry_with_multiple_actions,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { built_in_table: BUILT_IN_TABLE_MULTICAST_GROUP_TABLE }
        destination_table {
          built_in_table: BUILT_IN_TABLE_MULTICAST_GROUP_TABLE
        }
        field_references {
          source {
            match_field {
              built_in_match_field: BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID
            }
          }
          destination {
            match_field {
              built_in_match_field: BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID
            }
          }
        }
      )pb"),
      .description =
          "BuiltInMatchField-Refers-To-BuiltInMatchField reference creates "
          "a single concrete reference.",
  });

    pdpi::TableEntry p4_group_entry_with_multiple_actions =
      gutil::ParseProtoOrDie<pdpi::TableEntry>(
          R"pb(golden_test_friendly_wcmp_table_entry {
                 match { key1: "key-a" key2: "key-b" }
                 wcmp_actions {
                   action {
                     golden_test_friendly_action {
                       arg1: "act1-arg1"
                       arg2: "act1-arg2"
                     }
                   }
                   weight: 1
                 }
                 wcmp_actions {
                   action {
                     golden_test_friendly_action {
                       arg1: "act2-arg1"
                       arg2: "act2-arg2"
                     }
                   }
                   weight: 2
                 }
                 wcmp_actions {
                   action {
                     other_golden_test_friendly_action {
                       arg1: "act3-arg1"
                       arg2: "act3-arg2"
                     }
                   }
                   weight: 3
                 }
               })pb");

  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_group_entry_with_multiple_actions,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table {
          p4_table {
            table_name: "golden_test_friendly_wcmp_table"
            table_id: 37604604
          }
        }
        destination_table { p4_table { table_name: "other_table" } }
        field_references {
          source {
            action_field {
              p4_action_field {
                action_name: "golden_test_friendly_action"
                action_id: 31939749
                parameter_name: "arg1"
                parameter_id: 1
              }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
      )pb"),
      .description = "P4ActionField-Refers-To-P4MatchField reference creates a "
                     "concrete reference for every instance of the action.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_group_entry_with_multiple_actions,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table {
          p4_table {
            table_name: "golden_test_friendly_wcmp_table"
            table_id: 37604604
          }
        }
        destination_table { p4_table { table_name: "other_table" } }
        field_references {
          source {
            action_field {
              p4_action_field {
                action_name: "golden_test_friendly_action"
                action_id: 31939749
                parameter_name: "arg1"
                parameter_id: 1
              }
            }
          }
          destination {
            match_field {
              built_in_match_field: BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID
            }
          }
        }
      )pb"),
      .description =
          "P4ActionField-Refers-To-BuiltInMatchField reference creates a "
          "concrete reference for every instance of the action.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = built_in_entry_with_multiple_actions,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { built_in_table: BUILT_IN_TABLE_MULTICAST_GROUP_TABLE }
        destination_table { p4_table { table_name: "other_table" } }
        field_references {
          source {
            action_field {
              built_in_action_field {
                action: BUILT_IN_ACTION_REPLICA
                parameter: BUILT_IN_PARAMETER_REPLICA_PORT
              }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
      )pb"),
      .description =
          "BuiltInActionField-Refers-To-P4MatchField reference creates a "
          "concrete reference for every instance of the action.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = built_in_entry_with_multiple_actions,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { built_in_table: BUILT_IN_TABLE_MULTICAST_GROUP_TABLE }
        destination_table { p4_table { table_name: "other_table" } }
        field_references {
          source {
            action_field {
              built_in_action_field {
                action: BUILT_IN_ACTION_REPLICA
                parameter: BUILT_IN_PARAMETER_REPLICA_PORT
              }
            }
          }
          destination {
            match_field {
              built_in_match_field: BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID
            }
          }
        }
      )pb"),
      .description =
          "BuiltInActionField-Refers-To-BuiltInMatchField reference creates a "
          "concrete reference for every instance of the action.",
  });

    pdpi::TableEntry built_in_entry_with_multiple_backup_actions =
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        multicast_group_table_entry {
          match { multicast_group_id: "0x0037" }
          action {
            replicate {
              replicas {
                port: "port_1"
                instance: "0x0031"
                backup_replicas { port: "port_3" instance: "0x0033" }
                backup_replicas { port: "port_4" instance: "0x0034" }
              }
              replicas {
                port: "port_2"
                instance: "0x0032"
                backup_replicas { port: "port_5" instance: "0x0035" }
              }
            }
          }
        }
      )pb");

  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = built_in_entry_with_multiple_backup_actions,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { built_in_table: BUILT_IN_TABLE_MULTICAST_GROUP_TABLE }
        destination_table { p4_table { table_name: "other_table" } }
        field_references {
          source {
            action_field {
              built_in_action_field {
                action: BUILT_IN_ACTION_REPLICA
                parameter: BUILT_IN_PARAMETER_REPLICA_PORT
              }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
      )pb"),
      .description =
          "BuiltInActionField-Refers-To-P4MatchField reference creates a "
          "concrete reference for every instance of the backup-action.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = built_in_entry_with_multiple_backup_actions,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { built_in_table: BUILT_IN_TABLE_MULTICAST_GROUP_TABLE }
        destination_table { p4_table { table_name: "other_table" } }
        field_references {
          source {
            action_field {
              built_in_action_field {
                action: BUILT_IN_ACTION_REPLICA
                parameter: BUILT_IN_PARAMETER_REPLICA_PORT
              }
            }
          }
          destination {
            match_field {
              built_in_match_field: BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID
            }
          }
        }
      )pb"),
      .description =
          "BuiltInActionField-Refers-To-BuiltInMatchField reference creates a "
          "concrete reference for every instance of the backup-action.",
  });

  // NOTE: For all following test cases, output is similar whether destination
  // field is P4-defined or built-in so only the first is used to avoid
  // redundancy.
  // Composite test cases testing multi-field relationships
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table {
          p4_table {
            table_name: "golden_test_friendly_table"
            table_id: 50151603
          }
        }
        destination_table { p4_table { table_name: "other_table" } }
        field_references {
          source {
            match_field { p4_match_field { field_name: "key1" field_id: 1 } }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
        field_references {
          source {
            match_field { p4_match_field { field_name: "key2" field_id: 2 } }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
      )pb"),
      .description =
          "Multi P4MatchField-Refers-To-MatchField references create a "
          "single concrete reference.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table {
          p4_table {
            table_name: "golden_test_friendly_table"
            table_id: 50151603
          }
        }
        destination_table { p4_table { table_name: "other_table" } }
        field_references {
          source {
            match_field { p4_match_field { field_name: "key1" field_id: 1 } }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
        field_references {
          source {
            match_field {
              p4_match_field {
                field_name: "key2"
                field_id: 2
                is_optional: true
              }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
      )pb"),
      .description = "Two P4MatchField-Refers-To-MatchField references "
                     "including optional create a single concrete reference "
                     "with 2 ConcreteFieldReferences if optional is present.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table {
          p4_table {
            table_name: "golden_test_friendly_table"
            table_id: 50151603
          }
        }
        destination_table { p4_table { table_name: "other_table" } }
        field_references {
          source {
            match_field { p4_match_field { field_name: "key1" field_id: 1 } }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
        field_references {
          source {
            match_field {
              p4_match_field { field_name: "optional_field" is_optional: true }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
      )pb"),
      .description = "Two P4MatchField-Refers-To-MatchField references "
                     "including optional create a single concrete reference "
                     "with 1 ConcreteFieldReference if optional is absent.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_group_entry_with_multiple_actions,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table {
          p4_table {
            table_name: "golden_test_friendly_wcmp_table"
            table_id: 37604604
          }
        }
        destination_table { p4_table { table_name: "other_table" } }
        field_references {
          source {
            action_field {
              p4_action_field {
                action_name: "golden_test_friendly_action"
                action_id: 31939749
                parameter_name: "arg1"
                parameter_id: 1
              }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
        field_references {
          source {
            action_field {
              p4_action_field {
                action_name: "golden_test_friendly_action"
                action_id: 31939749
                parameter_name: "arg2"
                parameter_id: 2
              }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
      )pb"),
      .description =
          "Multi P4ActionField-Refers-To-MatchField references for the "
          "same action create a concrete reference containing all "
          "fields for every instance of the action.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_group_entry_with_multiple_actions,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table {
          p4_table {
            table_name: "golden_test_friendly_wcmp_table"
            table_id: 37604604
          }
        }
        destination_table { p4_table { table_name: "other_table" } }
        field_references {
          source {
            action_field {
              p4_action_field {
                action_name: "golden_test_friendly_action"
                action_id: 31939749
                parameter_name: "arg1"
                parameter_id: 1
              }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
        field_references {
          source {
            action_field {
              p4_action_field {
                action_name: "other_golden_test_friendly_action"
                action_id: 25225410
                parameter_name: "arg2"
                parameter_id: 2
              }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
      )pb"),
      .description =
          "Multi P4ActionField-Refers-To-MatchField references for the "
          "different "
          "actions create a concrete reference containing respective fields "
          "for every instance of the respective action.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_group_entry_with_multiple_actions,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table {
          p4_table {
            table_name: "golden_test_friendly_wcmp_table"
            table_id: 37604604
          }
        }
        destination_table { p4_table { table_name: "other_table" } }
        field_references {
          source {
            match_field { p4_match_field { field_name: "key1" field_id: 1 } }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
        field_references {
          source {
            action_field {
              p4_action_field {
                action_name: "golden_test_friendly_action"
                action_id: 31939749
                parameter_name: "arg1"
                parameter_id: 1
              }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
      )pb"),
      .description =
          "P4MatchField-Refers-To-MatchField + "
          "P4ActionField-Refers-To-MatchField references "
          "create a concrete reference for every action (including action with "
          "no reference info).",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_group_entry_with_multiple_actions,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table {
          p4_table {
            table_name: "golden_test_friendly_wcmp_table"
            table_id: 37604604
          }
        }
        destination_table { p4_table { table_name: "other_table" } }
        field_references {
          source {
            match_field {
              p4_match_field {
                field_name: "key1"
                field_id: 1
                is_optional: true
              }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
        field_references {
          source {
            action_field {
              p4_action_field {
                action_name: "golden_test_friendly_action"
                action_id: 31939749
                parameter_name: "arg1"
                parameter_id: 1
              }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
      )pb"),
      .description =
          "P4MatchField-Refers-To-MatchField + "
          "P4ActionField-Refers-To-MatchField references including optional "
          "create a concrete reference for every action (including action with "
          "no reference info) if optional present.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_group_entry_with_multiple_actions,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table {
          p4_table {
            table_name: "golden_test_friendly_wcmp_table"
            table_id: 37604604
          }
        }
        destination_table { p4_table { table_name: "other_table" } }
        field_references {
          source {
            match_field {
              p4_match_field { field_name: "optional_field" is_optional: true }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
        field_references {
          source {
            action_field {
              p4_action_field {
                action_name: "golden_test_friendly_action"
                action_id: 31939749
                parameter_name: "arg1"
                parameter_id: 1
              }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
      )pb"),
      .description =
          "P4MatchField-Refers-To-MatchField + "
          "P4ActionField-Refers-To-MatchField references including optional "
          "create a concrete reference for every action (except action with "
          "no reference info) if optional absent.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = built_in_entry_with_multiple_actions,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { built_in_table: BUILT_IN_TABLE_MULTICAST_GROUP_TABLE }
        destination_table { p4_table { table_name: "other_table" } }
        field_references {
          source {
            match_field {
              built_in_match_field: BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID
            }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
        field_references {
          source {
            action_field {
              built_in_action_field {
                action: BUILT_IN_ACTION_REPLICA
                parameter: BUILT_IN_PARAMETER_REPLICA_PORT
              }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "some_other_field" } }
          }
        }
      )pb"),
      .description =
          "BuiltInMatchField-Refers-To-MatchField + "
          "BuiltInActionField-Refers-To-MatchField references create a "
          "concrete reference for every instance of the action.",
  });

  // Test cases on entries with no actions.
  pdpi::TableEntry p4_group_entry_with_no_actions =
      gutil::ParseProtoOrDie<pdpi::TableEntry>(
          R"pb(golden_test_friendly_wcmp_table_entry {
                 match { key1: "key-a" key2: "key-b" }
               })pb");

  pdpi::TableEntry built_in_entry_with_no_actions =
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        multicast_group_table_entry {
          match { multicast_group_id: "0x0037" }
          action { replicate {} }
        }
      )pb");

  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_group_entry_with_no_actions,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table {
          p4_table {
            table_name: "golden_test_friendly_wcmp_table"
            table_id: 37604604
          }
        }
        destination_table { p4_table { table_name: "other_table" } }
        field_references {
          source {
            match_field { p4_match_field { field_name: "key1" field_id: 1 } }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
        field_references {
          source {
            action_field {
              p4_action_field {
                action_name: "golden_test_friendly_action"
                action_id: 31939749
                parameter_name: "arg1"
                parameter_id: 1
              }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
      )pb"),
      .description =
          "P4MatchField-Refers-To-MatchField + "
          "P4ActionField-Refers-To-MatchField references "
          "create a single concrete reference for match fields when no actions "
          "are present",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = built_in_entry_with_no_actions,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { built_in_table: BUILT_IN_TABLE_MULTICAST_GROUP_TABLE }
        destination_table { p4_table { table_name: "other_table" } }
        field_references {
          source {
            match_field {
              built_in_match_field: BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID
            }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
        field_references {
          source {
            action_field {
              built_in_action_field {
                action: BUILT_IN_ACTION_REPLICA
                parameter: BUILT_IN_PARAMETER_REPLICA_PORT
              }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "some_other_field" } }
          }
        }
      )pb"),
      .description =
          "BuiltInMatchField-Refers-To-MatchField + "
          "BuiltInActionField-Refers-To-MatchField "
          "references create a single concrete reference for match fields when "
          "no actions are present",
  });

  // Test cases on entries with duplicate references.
  pdpi::TableEntry p4_group_entry_duplicate_info =
      gutil::ParseProtoOrDie<pdpi::TableEntry>(
          R"pb(golden_test_friendly_wcmp_table_entry {
                 match { key1: "key-a" key2: "key-b" }
                 wcmp_actions {
                   action {
                     golden_test_friendly_action {
                       arg1: "arg-dupe"
                       arg2: "act1-arg2"
                     }
                   }
                   weight: 1
                 }
                 wcmp_actions {
                   action {
                     golden_test_friendly_action {
                       arg1: "arg-dupe"
                       arg2: "act2-arg2"
                     }
                   }
                   weight: 2
                 }
               })pb");

  pdpi::TableEntry built_in_entry_with_duplicate_info =
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        multicast_group_table_entry {
          match { multicast_group_id: "0x0037" }
          action {
            replicate {
              replicas { port: "port_dupe" instance: "0x0031" }
              replicas { port: "port_dupe" instance: "0x0032" }
            }
          }
        }
      )pb");

  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_group_entry_duplicate_info,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table {
          p4_table {
            table_name: "golden_test_friendly_wcmp_table"
            table_id: 37604604
          }
        }
        destination_table { p4_table { table_name: "other_table" } }
        field_references {
          source {
            match_field { p4_match_field { field_name: "key1" field_id: 1 } }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
        field_references {
          source {
            action_field {
              p4_action_field {
                action_name: "golden_test_friendly_action"
                action_id: 31939749
                parameter_name: "arg1"
                parameter_id: 1
              }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
      )pb"),
      .description = "A single reference is created for P4 actions with "
                     "duplicate referring values.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = built_in_entry_with_duplicate_info,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { built_in_table: BUILT_IN_TABLE_MULTICAST_GROUP_TABLE }
        destination_table { p4_table { table_name: "other_table" } }
        field_references {
          source {
            match_field {
              built_in_match_field: BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID
            }
          }
          destination {
            match_field { p4_match_field { field_name: "other_field" } }
          }
        }
        field_references {
          source {
            action_field {
              built_in_action_field {
                action: BUILT_IN_ACTION_REPLICA
                parameter: BUILT_IN_PARAMETER_REPLICA_PORT
              }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "some_other_field" } }
          }
        }
      )pb"),
      .description = "A single reference is created for built-in actions with "
                     "duplicate referring values.",
  });

  return test_cases;
}  // NOLINT(readability/fn_size)

std::vector<ConcreteTableReferenceTestCase>
PossibleIncomingConcreteTableReferencesTestCases() {
  std::vector<ConcreteTableReferenceTestCase> test_cases;

  pdpi::TableEntry p4_entry = gutil::ParseProtoOrDie<pdpi::TableEntry>(
      R"pb(golden_test_friendly_table_entry {
             match { key1: "key-a" key2: "key-b" }
             action {
               golden_test_friendly_action { arg1: "arg1" arg2: "arg2" }
             }
           })pb");

  pdpi::TableEntry built_in_entry =
      gutil::ParseProtoOrDie<pdpi::TableEntry>(R"pb(
        multicast_group_table_entry {
          match { multicast_group_id: "0x0037" }
          action { replicate { replicas { port: "port" instance: "0x0031" } } }
        }
      )pb");

  // Error test cases
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { p4_table { table_name: "other_table" } }
        destination_table { p4_table { table_name: "wrong_table" table_id: 7 } }
        field_references {
          source {
            match_field { p4_match_field { field_name: "other_field" } }
          }
          destination {
            match_field { p4_match_field { field_name: "key1" field_id: 1 } }
          }
        }
      )pb"),
      .description = "Fails if entity does not belong to destination table",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { p4_table { table_name: "other_table" } }
        destination_table {
          p4_table {
            table_name: "golden_test_friendly_table"
            table_id: 50151603
          }
        }
        field_references {
          source { match_field { p4_match_field { field_name: "some_field" } } }
          destination {
            match_field { p4_match_field { field_name: "missing_field" } }
          }
        }
      )pb"),
      .description = "Fails if referenced field is missing",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { p4_table { table_name: "other_table" } }
        destination_table {
          p4_table {
            table_name: "golden_test_friendly_table"
            table_id: 50151603
          }
        }
        field_references {
          source { match_field { p4_match_field { field_name: "some_field" } } }
          destination {
            match_field {
              p4_match_field { field_name: "key_1" is_optional: true }
            }
          }
        }
      )pb"),
      .description = "Fails if referenced field is optional",
  });
  // NOTE: Similar errors are encountered for the following:
  // P4ActionField-Referenced-By-P4MatchField
  // P4ActionField-Referenced-By-BuiltInMatchField
  // BuiltInActionField-Referenced-By-P4MatchField
  // BuiltInActionField-Referenced-By-BuiltInMatchField
  // P4ActionField-Referenced-By-P4ActionField
  // P4ActionField-Referenced-By-BuiltInActionField
  // BuiltInActionField-Referenced-By-P4ActionField
  // BuiltInActionField-Referenced-By-BuiltInField
  // Only the first is tested to avoid redundancy.
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { p4_table { table_name: "other_table" } }
        destination_table {
          p4_table {
            table_name: "golden_test_friendly_table"
            table_id: 50151603
          }
        }
        field_references {
          source {
            action_field {
              p4_action_field {
                action_name: "other_action"
                parameter_name: "other_arg"
              }
            }
          }
          destination {
            action_field {
              p4_action_field {
                action_name: "golden_test_friendly_action"
                action_id: 31939749
                parameter_name: "arg1"
                parameter_id: 1
              }
            }
          }
        }
      )pb"),
      .description = "Fails for unsupported reference type (i.e. "
                     "Action-Referenced-By-Action)",
  });

  // Fundamental test cases testing single field relationships.
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { p4_table { table_name: "other_table" } }
        destination_table {
          p4_table {
            table_name: "golden_test_friendly_table"
            table_id: 50151603
          }
        }
      )pb"),
      .description = "No field references creates no concrete references",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { p4_table { table_name: "other_table" } }
        destination_table {
          p4_table {
            table_name: "golden_test_friendly_table"
            table_id: 50151603
          }
        }
        field_references {
          source {
            match_field { p4_match_field { field_name: "other_field" } }
          }
          destination {
            match_field { p4_match_field { field_name: "key1" field_id: 1 } }
          }
        }
      )pb"),
      .description =
          "P4MatchField-Referenced-By-P4MatchField reference creates a single "
          "concrete reference.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { p4_table { table_name: "other_table" } }
        destination_table {
          p4_table {
            table_name: "golden_test_friendly_table"
            table_id: 50151603
          }
        }
        field_references {
          source {
            match_field {
              built_in_match_field: BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID
            }
          }
          destination {
            match_field { p4_match_field { field_name: "key1" field_id: 1 } }
          }

        }
      )pb"),
      .description =
          "P4MatchField-Referenced-By-BuiltInField reference creates a "
          "single concrete reference.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = built_in_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { p4_table { table_name: "other_table" } }
        destination_table {
          built_in_table: BUILT_IN_TABLE_MULTICAST_GROUP_TABLE
        }
        field_references {
          source {
            match_field { p4_match_field { field_name: "other_field" } }
          }
          destination {
            match_field {
              built_in_match_field: BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID
            }
          }
        }
      )pb"),
      .description =
          "BuiltInMatchField-Referenced-By-P4MatchField reference creates a "
          "single concrete reference.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = built_in_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { p4_table { table_name: "other_table" } }
        destination_table {
          built_in_table: BUILT_IN_TABLE_MULTICAST_GROUP_TABLE
        }
        field_references {
          source {
            match_field {
              p4_match_field { field_name: "optional_field" is_optional: true }
            }
          }
          destination {
            match_field {
              built_in_match_field: BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID
            }
          }
        }
      )pb"),
      .description = "BuiltInMatchField-Referenced-By-OptionalP4MatchField "
                     "reference creates a single concrete reference.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = built_in_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { built_in_table: BUILT_IN_TABLE_MULTICAST_GROUP_TABLE }
        destination_table {
          built_in_table: BUILT_IN_TABLE_MULTICAST_GROUP_TABLE
        }
        field_references {
          source {
            match_field {
              built_in_match_field: BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID
            }
          }
          destination {
            match_field {
              built_in_match_field: BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID
            }
          }
        }
      )pb"),
      .description =
          "BuiltInMatchField-Referenced-By-BuiltInMatchField reference creates "
          "a single concrete reference.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { p4_table { table_name: "other_table" } }
        destination_table {
          p4_table {
            table_name: "golden_test_friendly_table"
            table_id: 50151603
          }
        }
        field_references {
          source {
            action_field {
              p4_action_field {
                action_name: "some_action"
                parameter_name: "some_arg"
              }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "key1" field_id: 1 } }
          }
        }
      )pb"),
      .description = "P4MatchField-To-P4ActionField reference creates a single "
                     "concrete reference.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { p4_table { table_name: "other_table" } }
        destination_table {
          p4_table {
            table_name: "golden_test_friendly_table"
            table_id: 50151603
          }
        }
        field_references {
          source {
            match_field {
              built_in_match_field: BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID
            }
          }
          destination {
            match_field { p4_match_field { field_name: "key1" field_id: 1 } }
          }
        }
      )pb"),
      .description =
          "P4MatchField-Referenced-By-BuiltInActionField reference creates a "
          "single concrete reference.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = built_in_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { p4_table { table_name: "other_table" } }
        destination_table {
          built_in_table: BUILT_IN_TABLE_MULTICAST_GROUP_TABLE
        }
        field_references {
          source {
            action_field {
              p4_action_field {
                action_name: "some_action"
                parameter_name: "some_arg"
              }
            }
          }
          destination {
            match_field {
              built_in_match_field: BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID
            }
          }
        }
      )pb"),
      .description =
          "BuiltInMatchField-Referenced-By-P4ActionField reference creates a "
          "single concrete reference.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = built_in_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { built_in_table: BUILT_IN_TABLE_MULTICAST_GROUP_TABLE }
        destination_table {
          built_in_table: BUILT_IN_TABLE_MULTICAST_GROUP_TABLE
        }
        field_references {
          source {
            action_field {
              built_in_action_field {
                action: BUILT_IN_ACTION_REPLICA
                parameter: BUILT_IN_PARAMETER_REPLICA_PORT
              }
            }
          }
          destination {
            match_field {
              built_in_match_field: BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID
            }
          }
        }
      )pb"),
      .description = "BuiltInMatchField-Referenced-By-BuiltInActionField "
                     "reference creates a single"
                     "concrete reference.",
  });

  // NOTE: For all following test cases, output is similar whether source field
  // is P4-defined or built-in so only the first is used to avoid redundancy.
  // Composite test cases testing multi-field relationships
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { p4_table { table_name: "other_table" } }
        destination_table {
          p4_table {
            table_name: "golden_test_friendly_table"
            table_id: 50151603
          }
        }
        field_references {
          source {
            match_field { p4_match_field { field_name: "other_field" } }
          }
          destination {
            match_field { p4_match_field { field_name: "key1" field_id: 1 } }
          }
        }
        field_references {
          source {
            match_field { p4_match_field { field_name: "some_other_field" } }
          }
          destination {
            match_field { p4_match_field { field_name: "key2" field_id: 2 } }
          }
        }
      )pb"),
      .description =
          "Multi P4MatchField-Referenced-By-MatchField references create a "
          "single concrete reference.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { p4_table { table_name: "other_table" } }
        destination_table {
          p4_table {
            table_name: "golden_test_friendly_table"
            table_id: 50151603
          }
        }
        field_references {
          source {
            match_field { p4_match_field { field_name: "other_field" } }
          }
          destination {
            match_field { p4_match_field { field_name: "key1" field_id: 1 } }
          }
        }
        field_references {
          source {
            match_field {
              p4_match_field {
                field_name: "optional_field_1"
                is_optional: true
              }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "key2" field_id: 2 } }
          }
        }
        field_references {
          source {
            match_field {
              p4_match_field {
                field_name: "optional_field_2"
                is_optional: true
              }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "key2" field_id: 2 } }
          }
        }
      )pb"),
      .description =
          "Multi P4MatchField-Referenced-By-MatchField including "
          "multiple optional references creates several concrete references.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { p4_table { table_name: "other_table" } }
        destination_table {
          p4_table {
            table_name: "golden_test_friendly_table"
            table_id: 50151603
          }
        }
        field_references {
          source {
            action_field {
              p4_action_field { action_name: "action" parameter_name: "arg1" }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "key1" field_id: 1 } }
          }
        }
        field_references {
          source {
            action_field {
              p4_action_field { action_name: "action" parameter_name: "arg2" }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "key2" field_id: 2 } }
          }
        }
      )pb"),
      .description =
          "Multi P4MatchField-Referenced-By-ActionField references from the "
          "same action create a single concrete reference.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { p4_table { table_name: "other_table" } }
        destination_table {
          p4_table {
            table_name: "golden_test_friendly_table"
            table_id: 50151603
          }
        }
        field_references {
          source {
            action_field {
              p4_action_field { action_name: "action" parameter_name: "arg1" }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "key1" field_id: 1 } }
          }
        }
        field_references {
          source {
            action_field {
              p4_action_field {
                action_name: "other_action"
                parameter_name: "arg2"
              }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "key2" field_id: 2 } }
          }
        }
      )pb"),
      .description = "Multi P4MatchField-Referenced-By-ActionField references "
                     "from different "
                     "actions create a concrete reference for every action.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { p4_table { table_name: "other_table" } }
        destination_table {
          p4_table {
            table_name: "golden_test_friendly_table"
            table_id: 50151603
          }
        }
        field_references {
          source {
            match_field { p4_match_field { field_name: "other_field" } }
          }
          destination {
            match_field { p4_match_field { field_name: "key1" field_id: 1 } }
          }
        }
        field_references {
          source {
            action_field {
              p4_action_field { action_name: "action" parameter_name: "arg1" }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "key1" field_id: 1 } }
          }
        }
        field_references {
          source {
            action_field {
              p4_action_field {
                action_name: "other_action"
                parameter_name: "arg2"
              }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "key2" field_id: 2 } }
          }
        }
      )pb"),
      .description =
          "P4MatchField-Referenced-By-MatchField + Multi "
          "P4MatchField-Referenced-By-ActionField "
          "references from different actions create a concrete reference for "
          "every action plus an additional reference for match field only.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = p4_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { p4_table { table_name: "other_table" } }
        destination_table {
          p4_table {
            table_name: "golden_test_friendly_table"
            table_id: 50151603
          }
        }
        field_references {
          source {
            match_field {
              p4_match_field { field_name: "optional_field" is_optional: true }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "key1" field_id: 1 } }
          }
        }
        field_references {
          source {
            action_field {
              p4_action_field {
                action_name: "source_action"
                parameter_name: "source_arg1"
              }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "key1" field_id: 1 } }
          }
        }
        field_references {
          source {
            action_field {
              p4_action_field {
                action_name: "other_source_action"
                parameter_name: "source_arg2"
              }
            }
          }
          destination {
            match_field { p4_match_field { field_name: "key2" field_id: 2 } }
          }
        }
      )pb"),
      .description = "P4MatchField-Referenced-By-OptionalMatchField + Multi "
                     "P4MatchField-Referenced-By-ActionField references from "
                     "different actions create a concrete reference for "
                     "every action plus additional copies including and not "
                     "including the optional.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = built_in_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { p4_table { table_name: "other_table" } }
        destination_table {
          built_in_table: BUILT_IN_TABLE_MULTICAST_GROUP_TABLE
        }
        field_references {
          source {
            match_field { p4_match_field { field_name: "other_field" } }
          }
          destination {
            match_field {
              built_in_match_field: BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID
            }
          }
        }
        field_references {
          source {
            match_field { p4_match_field { field_name: "some_other_field" } }
          }
          destination {
            match_field {
              built_in_match_field: BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID
            }
          }
        }
      )pb"),
      .description =
          "Multi BuiltInMatchField-Referenced-By-MatchField references create "
          "a single concrete reference.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = built_in_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { p4_table { table_name: "other_table" } }
        destination_table {
          built_in_table: BUILT_IN_TABLE_MULTICAST_GROUP_TABLE
        }
        field_references {
          source {
            action_field {
              p4_action_field { action_name: "action" parameter_name: "arg1" }
            }
          }
          destination {
            match_field {
              built_in_match_field: BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID
            }
          }
        }
        field_references {
          source {
            action_field {
              p4_action_field { action_name: "action" parameter_name: "arg2" }
            }
          }
          destination {
            match_field {
              built_in_match_field: BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID
            }
          }
        }
      )pb"),
      .description =
          "Multi BuiltInMatchField-Referenced-By-ActionField references from "
          "the same action create a single concrete reference.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = built_in_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { p4_table { table_name: "other_table" } }
        destination_table {
          built_in_table: BUILT_IN_TABLE_MULTICAST_GROUP_TABLE
        }
        field_references {
          source {
            action_field {
              p4_action_field { action_name: "action" parameter_name: "arg1" }
            }
          }
          destination {
            match_field {
              built_in_match_field: BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID
            }
          }
        }
        field_references {
          source {
            action_field {
              p4_action_field {
                action_name: "other_action"
                parameter_name: "arg2"
              }
            }
          }
          destination {
            match_field {
              built_in_match_field: BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID
            }
          }
        }
      )pb"),
      .description = "Multi BuiltInMatchField-Referenced-By-ActionField "
                     "references from different "
                     "actions create a concrete reference for every action.",
  });
  test_cases.push_back(ConcreteTableReferenceTestCase{
      .entity = built_in_entry,
      .reference_info = gutil::ParseProtoOrDie<IrTableReference>(R"pb(
        source_table { p4_table { table_name: "other_table" } }
        destination_table {
          built_in_table: BUILT_IN_TABLE_MULTICAST_GROUP_TABLE
        }
        field_references {
          source {
            match_field { p4_match_field { field_name: "other_field" } }
          }
          destination {
            match_field {
              built_in_match_field: BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID
            }
          }
        }
        field_references {
          source {
            action_field {
              p4_action_field { action_name: "action" parameter_name: "arg1" }
            }
          }
          destination {
            match_field {
              built_in_match_field: BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID
            }
          }
        }
        field_references {
          source {
            action_field {
              p4_action_field {
                action_name: "other_action"
                parameter_name: "arg2"
              }
            }
          }
          destination {
            match_field {
              built_in_match_field: BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID
            }
          }
        }
      )pb"),
      .description =
          "BuiltInMatchField-Referenced-By-MatchField + Multi "
          "BuiltInMatchField-Referenced-By-ActionField references from "
          "different actions "
          "create a concrete reference for every action plus an additional "
          "reference for match field only.",
  });

  return test_cases;
}  // NOLINT(readability/fn_size)

absl::Status OutgoingConcreteTableReferencesTest() {
  for (const auto& test_case : OutgoingConcreteTableReferencesTestCases()) {
    std::cout << TestHeader(absl::StrCat("OutgoingConcreteTableReferences: ",
                                         test_case.description))
              << "\n";
    std::cout << kInputBanner << "-- PD table entry --\n";
    std::cout << gutil::PrintTextProto(test_case.entity) << "\n";
    std::cout << "-- ReferenceInfo --\n";
    std::cout << gutil::PrintTextProto(test_case.reference_info) << "\n";

    ASSIGN_OR_RETURN(
        const p4::v1::Entity pi_entity,
        PdTableEntryToPiEntity(GetTestIrP4Info(), test_case.entity));

    absl::StatusOr<absl::flat_hash_set<ConcreteTableReference>>
        reference_entries = OutgoingConcreteTableReferences(
            test_case.reference_info, pi_entity);

    std::cout << kOutputBanner;
    if (!reference_entries.ok()) {
      std::cout << gutil::StableStatusToString(reference_entries.status())
                << "\n";
    } else if (reference_entries->empty()) {
      std::cout << "<empty>\n\n";
    } else {
      // Sorted for golden file stability
      absl::btree_set<ConcreteTableReference> reference_entries_sorted(
          reference_entries->begin(), reference_entries->end());
      std::cout << "-- ReferenceEntries --\n"
                << absl::StrJoin(reference_entries_sorted, "") << "\n";
    }
  }
  return absl::OkStatus();
}

absl::Status PossibleIncomingConcreteTableReferencesTest() {
  for (const auto& test_case :
       PossibleIncomingConcreteTableReferencesTestCases()) {
    std::cout << TestHeader(
                     absl::StrCat("PossibleIncomingConcreteTableReferences: ",
                                  test_case.description))
              << "\n";

    std::cout << kInputBanner << "-- PD table entry --\n";
    std::cout << gutil::PrintTextProto(test_case.entity) << "\n";
    std::cout << "-- ReferenceInfo --\n";
    std::cout << gutil::PrintTextProto(test_case.reference_info) << "\n";

    ASSIGN_OR_RETURN(
        const p4::v1::Entity pi_entity,
        PdTableEntryToPiEntity(GetTestIrP4Info(), test_case.entity));

    absl::StatusOr<absl::flat_hash_set<ConcreteTableReference>>
        reference_entries = PossibleIncomingConcreteTableReferences(
            test_case.reference_info, pi_entity);

    std::cout << kOutputBanner;
    if (!reference_entries.ok()) {
      std::cout << gutil::StableStatusToString(reference_entries.status())
                << "\n";
    } else if (reference_entries->empty()) {
      std::cout << "<empty>\n\n";
    } else {
      // Sorted for golden file stability
      absl::btree_set<ConcreteTableReference> reference_entries_sorted(
          reference_entries->begin(), reference_entries->end());
      std::cout << "-- ReferenceEntries --\n"
                << absl::StrJoin(reference_entries_sorted, "") << "\n";
    }
  }
  return absl::OkStatus();
}

struct UnsatisfiedReferencesTestCase {
  std::string description;
  // PD representation of PI entity used to generate outgoing/possible-incoming
  // table references. Valid entities must meet the following requirements:
  // - Entity must be valid for main.p4 program.
  pdpi::TableEntries entities;
};

std::vector<UnsatisfiedReferencesTestCase> UnsatisfiedReferencesTestCases() {
  return {
      UnsatisfiedReferencesTestCase{
          .description = "Unsatisfied reference",
          .entities = gutil::ParseProtoOrDie<pdpi::TableEntries>(R"pb(
            entries {
              refers_to_multicast_by_action_table_entry {
                match { val: "dragon" }
                action {
                  refers_to_multicast_action { multicast_group_id: "0x0037" }
                }
                controller_metadata: "Has unsatisfied reference"
              }
            }
          )pb")},
      UnsatisfiedReferencesTestCase{
          .description = "Satisfied and unsatisfied references",
          .entities = gutil::ParseProtoOrDie<pdpi::TableEntries>(R"pb(
            entries {
              refers_to_multicast_by_action_table_entry {
                match { val: "dragon" }
                action {
                  refers_to_multicast_action { multicast_group_id: "0x0037" }
                }
                controller_metadata: "References satisfied"
              }
            }
            entries {
              multicast_group_table_entry {
                match { multicast_group_id: "0x0037" }
                action {
                  replicate {
                    replicas { port: "some_port" instance: "0x0031" }
                  }
                }
                metadata: "Has unsatisfied reference"
              }
            }
          )pb")},
      UnsatisfiedReferencesTestCase{
          .description = "Satisfied references",
          .entities = gutil::ParseProtoOrDie<pdpi::TableEntries>(R"pb(
            entries {
              refers_to_multicast_by_action_table_entry {
                match { val: "dragon" }
                action {
                  refers_to_multicast_action { multicast_group_id: "0x0037" }
                }
                controller_metadata: "References satisfied"
              }

            }
            entries {
              multicast_group_table_entry {
                match { multicast_group_id: "0x0037" }
                action {
                  replicate {
                    replicas { port: "some_port" instance: "0x0031" }
                  }
                }
                metadata: "References satisfied"
              }
            }
            entries {
              referenced_by_multicast_replica_table_entry {
                match { port: "some_port" instance: "0x0031" }
                action { do_thing_4 {} }
                controller_metadata: "Has no references"
              }
            }
          )pb")},
  };
}

absl::Status UnsatisfiedReferencesTest() {
  for (const auto& test_case : UnsatisfiedReferencesTestCases()) {
    std::cout << TestHeader(absl::StrCat("UnsatisfiedReferences: ",
                                         test_case.description))
              << "\n";

    std::cout << kInputBanner << "-- PD table entries --\n";
    std::cout << gutil::PrintTextProto(test_case.entities) << "\n";

    ASSIGN_OR_RETURN(
        const std::vector<p4::v1::Entity> pi_entities,
        PdTableEntriesToPiEntities(GetTestIrP4Info(), test_case.entities));

    ASSIGN_OR_RETURN(
        const std::vector<EntityWithUnsatisfiedReferences>
            entity_with_unsatisfied_references,
        UnsatisfiedOutgoingReferences(pi_entities, GetTestIrP4Info()));

    std::cout << kOutputBanner;
    if (entity_with_unsatisfied_references.empty()) {
      std::cout << "<empty>\n\n";
    } else {
      for (const auto& entity_with_unsatisfied_references :
           entity_with_unsatisfied_references) {
        std::cout
            << "-- Entity with Unsatisfied References --\n"
            << gutil::PrintTextProto(entity_with_unsatisfied_references.entity)
            << "-- Unsatisfied References--\n"
            << absl::StrJoin(
                   entity_with_unsatisfied_references.unsatisfied_references,
                   "\n")
            << "\n";
      }
    }
  }
  return absl::OkStatus();
}

void main(int argc, char** argv) {
  if (absl::Status test = OutgoingConcreteTableReferencesTest(); !test.ok()) {
    std::cout << "OutgoingConcreteTableReferencesTest failed.\n" << test;
  }

  if (absl::Status test = PossibleIncomingConcreteTableReferencesTest();
      !test.ok()) {
    std::cout << "PossibleIncomingConcreteTableReferencesTest failed.\n"
              << test;
  }

  if (absl::Status test = UnsatisfiedReferencesTest(); !test.ok()) {
    std::cout << "UnsatisfiedReferencesTest failed.\n" << test;
  }
}

}  // namespace
}  // namespace pdpi

int main(int argc, char** argv) { pdpi::main(argc, argv); }
