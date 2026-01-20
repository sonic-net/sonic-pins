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
#include "p4rt_app/p4runtime/resource_utilization.h"

#include <cstdint>
#include <optional>
#include <ostream>
#include <string>
#include <utility>

#include "absl/container/flat_hash_map.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "google/protobuf/text_format.h"
#include "gtest/gtest.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/entity_keys.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4rt_app/p4runtime/entity_update.h"
#include "p4rt_app/utils/ir_builder.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace p4rt_app {
namespace sonic {

// Pretty print function to help clarify failed expectations.
void PrintTo(const ActionProfileResources& resource, std::ostream* os) {
  *os << "name:" << resource.name << " actions:" << resource.number_of_actions
      << " total_weight:" << resource.total_weight
      << " max_weight:" << resource.max_weight;
}

// Pretty print function to help clarify failed expectations.
void PrintTo(const TableResources& resource, std::ostream* os) {
  *os << "name:" << resource.name;
  if (resource.action_profile.has_value()) {
    *os << " action_profile { ";
    PrintTo(*resource.action_profile, os);
    *os << " } ";
  }
}

}  // namespace sonic

namespace {

using ::gutil::IsOk;
using ::gutil::StatusIs;
using ::testing::Eq;
using ::testing::FieldsAre;
using ::testing::HasSubstr;
using ::testing::Optional;

// This library has 2 methods that should behave the same on both IR and PI
// entries. Therefore, we write most of our tests against both formats.
struct MatchingIrAndPiTableEntry {
  pdpi::IrTableEntry ir_table_entry;
  p4::v1::TableEntry pi_table_entry;
};

absl::StatusOr<MatchingIrAndPiTableEntry> TranslateIrString(
    const pdpi::IrP4Info& ir_p4info, const std::string& table_entry) {
  MatchingIrAndPiTableEntry result;
  if (!google::protobuf::TextFormat::ParseFromString(table_entry,
                                                     &result.ir_table_entry)) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Could not translate string into IR entry.";
  }
  ASSIGN_OR_RETURN(result.pi_table_entry,
                   pdpi::IrTableEntryToPi(ir_p4info, result.ir_table_entry));
  return result;
}

// Resource utilization tests focus on counting resources in PI and IR table
// entries.
class ResourceUtilizationTest : public testing::Test {
 public:
  pdpi::IrP4Info& GetIrP4Info() { return ir_p4info_; }

 protected:
  pdpi::IrP4Info ir_p4info_ =
      sai::GetIrP4Info(sai::Instantiation::kMiddleblock);
  std::string wcmp_table_name_ = "wcmp_group_table";
  std::string wcmp_selector_name_ = "wcmp_group_selector";
};

TEST_F(ResourceUtilizationTest, IgnoresTableEntriesWithoutActionProfiles) {
  ASSERT_OK_AND_ASSIGN(MatchingIrAndPiTableEntry table_entries,
                       TranslateIrString(ir_p4info_,
                                         R"pb(
                                           table_name: "vrf_table"
                                           matches {
                                             name: "vrf_id"
                                             exact { str: "vrf-157" }
                                           }
                                           action { name: "no_action" }
                                         )pb"));

  ASSERT_OK_AND_ASSIGN(TableResources ir_resources,
                       GetResourceUsageForIrTableEntry(
                           ir_p4info_, table_entries.ir_table_entry));
  ASSERT_OK_AND_ASSIGN(TableResources pi_resources,
                       GetResourceUsageForPiTableEntry(
                           ir_p4info_, table_entries.pi_table_entry));

  EXPECT_FALSE(ir_resources.action_profile.has_value());
  EXPECT_FALSE(pi_resources.action_profile.has_value());
}

TEST_F(ResourceUtilizationTest, CountsWcmpActionsAndWeights) {
  ASSERT_OK_AND_ASSIGN(MatchingIrAndPiTableEntry table_entries,
                       TranslateIrString(ir_p4info_,
                                         R"pb(
                                           table_name: "wcmp_group_table"
                                           matches {
                                             name: "wcmp_group_id"
                                             exact { str: "group-1" }
                                           }
                                           action_set {
                                             actions {
                                               action {
                                                 name: "set_nexthop_id"
                                                 params {
                                                   name: "nexthop_id"
                                                   value { str: "nexthop-1" }
                                                 }
                                               }
                                               weight: 1
                                             }
                                             actions {
                                               action {
                                                 name: "set_nexthop_id"
                                                 params {
                                                   name: "nexthop_id"
                                                   value { str: "nexthop-2" }
                                                 }
                                               }
                                               weight: 2
                                             }
                                           })pb"));

  ASSERT_OK_AND_ASSIGN(TableResources ir_resources,
                       GetResourceUsageForIrTableEntry(
                           ir_p4info_, table_entries.ir_table_entry));
  ASSERT_OK_AND_ASSIGN(TableResources pi_resources,
                       GetResourceUsageForPiTableEntry(
                           ir_p4info_, table_entries.pi_table_entry));

  EXPECT_THAT(ir_resources.action_profile,
              Optional(FieldsAre(wcmp_selector_name_, /*number_of_actions=*/2,
                                 /*total_weight=*/3, /*max_weight=*/2)));
  EXPECT_THAT(pi_resources.action_profile,
              Optional(FieldsAre(wcmp_selector_name_, /*number_of_actions=*/2,
                                 /*total_weight=*/3, /*max_weight=*/2)));
}

TEST_F(ResourceUtilizationTest, WcmpReturnsNotFoundIfTableEntryDoesNotExist) {
  ASSERT_OK_AND_ASSIGN(MatchingIrAndPiTableEntry table_entries,
                       TranslateIrString(ir_p4info_,
                                         R"pb(
                                           table_name: "wcmp_group_table"
                                           matches {
                                             name: "wcmp_group_id"
                                             exact { str: "group-1" }
                                           }
                                           action_set {
                                             actions {
                                               action {
                                                 name: "set_nexthop_id"
                                                 params {
                                                   name: "nexthop_id"
                                                   value { str: "nexthop-1" }
                                                 }
                                               }
                                               weight: 1
                                             }
                                           })pb"));

  // Tweak the table name (for IR) and ID (for PI) so that they will fail.
  table_entries.ir_table_entry.set_table_name("bad_table_name");
  table_entries.pi_table_entry.set_table_id(0);

  EXPECT_THAT(
      GetResourceUsageForIrTableEntry(ir_p4info_, table_entries.ir_table_entry),
      StatusIs(absl::StatusCode::kNotFound, HasSubstr("bad_table_name")));
  EXPECT_THAT(
      GetResourceUsageForPiTableEntry(ir_p4info_, table_entries.pi_table_entry),
      StatusIs(absl::StatusCode::kNotFound,
               HasSubstr("table definition for ID: 0")));
}

TEST_F(ResourceUtilizationTest,
       WcmpReturnsNotFoundIfActionSelectorDoesNotExist) {
  ASSERT_OK_AND_ASSIGN(MatchingIrAndPiTableEntry table_entries,
                       TranslateIrString(ir_p4info_,
                                         R"pb(
                                           table_name: "wcmp_group_table"
                                           matches {
                                             name: "wcmp_group_id"
                                             exact { str: "group-1" }
                                           }
                                           action_set {
                                             actions {
                                               action {
                                                 name: "set_nexthop_id"
                                                 params {
                                                   name: "nexthop_id"
                                                   value { str: "nexthop-1" }
                                                 }
                                               }
                                               weight: 1
                                             }
                                           })pb"));

  // Tweak the IrP4Info such that the action selector for the wcmp_group_table
  // is invalid.
  pdpi::IrTableDefinition* table_def_from_name = gutil::FindOrNull(
      *ir_p4info_.mutable_tables_by_name(), "wcmp_group_table");
  ASSERT_NE(table_def_from_name, nullptr);
  table_def_from_name->set_action_profile_id(0);

  pdpi::IrTableDefinition* table_def_from_id = gutil::FindOrNull(
      *ir_p4info_.mutable_tables_by_id(), table_def_from_name->preamble().id());
  ASSERT_NE(table_def_from_id, nullptr);
  table_def_from_id->set_action_profile_id(0);

  EXPECT_THAT(
      GetResourceUsageForIrTableEntry(ir_p4info_, table_entries.ir_table_entry),
      StatusIs(absl::StatusCode::kNotFound,
               HasSubstr("action profile definition for ID: 0")));
  EXPECT_THAT(
      GetResourceUsageForPiTableEntry(ir_p4info_, table_entries.pi_table_entry),
      StatusIs(absl::StatusCode::kNotFound,
               HasSubstr("action profile definition for ID: 0")));
}

absl::StatusOr<EntityUpdate> GetUpdate(const pdpi::IrP4Info& ir_p4info,
                                       p4::v1::Update::Type update_type,
                                       const std::string& ir_entity) {
  EntityUpdate update;
  if (!google::protobuf::TextFormat::ParseFromString(ir_entity,
                                                     &update.entry)) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Could not translate string into IR entity.";
  }
  ASSIGN_OR_RETURN(update.pi_entity,
                   pdpi::IrEntityToPi(ir_p4info, update.entry));
  ASSIGN_OR_RETURN(update.entity_key,
                   pdpi::EntityKey::MakeEntityKey(update.pi_entity));
  update.update_type = update_type;
  return update;
}

class GetTableResourceChangeTest : public ResourceUtilizationTest {
 public:
 protected:
  GetTableResourceChangeTest() : ResourceUtilizationTest() {
    for (const auto& [action_profile_name, action_profile_def] :
         ir_p4info_.action_profiles_by_name()) {
      capacity_by_action_profile_name_[action_profile_name] =
          GetActionProfileResourceCapacity(action_profile_def);
    }
  }

  absl::flat_hash_map<pdpi::EntityKey, p4::v1::Entity> entity_cache_;
  absl::flat_hash_map<std::string, ActionProfileResourceCapacity>
      capacity_by_action_profile_name_;
  absl::flat_hash_map<std::string, int64_t> resources_in_current_batch_;
};

TEST_F(GetTableResourceChangeTest, CanGetInsertResources) {
  ASSERT_OK_AND_ASSIGN(EntityUpdate update,
                       GetUpdate(ir_p4info_, p4::v1::Update::INSERT,
                                 R"pb(
                                   table_entry {
                                     table_name: "wcmp_group_table"
                                     matches {
                                       name: "wcmp_group_id"
                                       exact { str: "group-1" }
                                     }
                                     action_set {
                                       actions {
                                         action {
                                           name: "set_nexthop_id"
                                           params {
                                             name: "nexthop_id"
                                             value { str: "nexthop-1" }
                                           }
                                         }
                                         weight: 1
                                       }
                                       actions {
                                         action {
                                           name: "set_nexthop_id"
                                           params {
                                             name: "nexthop_id"
                                             value { str: "nexthop-2" }
                                           }
                                         }
                                         weight: 2
                                       }
                                     }
                                   })pb"));

  ASSERT_OK_AND_ASSIGN(
      TableResources resources,
      VerifyCapacityAndGetTableResourceChange(ir_p4info_, update, entity_cache_,
                                              capacity_by_action_profile_name_,
                                              resources_in_current_batch_));

  EXPECT_THAT(resources.name, wcmp_table_name_);
  EXPECT_THAT(resources.action_profile,
              Optional(FieldsAre(wcmp_selector_name_, /*number_of_actions=*/2,
                                 /*total_weight=*/3, /*max_weight=*/2)));
}

TEST_F(GetTableResourceChangeTest, CanGetModifyResources) {
  ASSERT_OK_AND_ASSIGN(EntityUpdate update,
                       GetUpdate(ir_p4info_, p4::v1::Update::MODIFY,
                                 R"pb(
                                   table_entry {
                                     table_name: "wcmp_group_table"
                                     matches {
                                       name: "wcmp_group_id"
                                       exact { str: "group-1" }
                                     }
                                     action_set {
                                       actions {
                                         action {
                                           name: "set_nexthop_id"
                                           params {
                                             name: "nexthop_id"
                                             value { str: "nexthop-1" }
                                           }
                                         }
                                         weight: 1
                                       }
                                       actions {
                                         action {
                                           name: "set_nexthop_id"
                                           params {
                                             name: "nexthop_id"
                                             value { str: "nexthop-2" }
                                           }
                                         }
                                         weight: 1
                                       }
                                     }
                                   })pb"));

  // The "old" entry that we will be modifying should have 1 action with a
  // weight of 3.
  auto [cache_entry, table_entry_cache_success] =
      entity_cache_.insert({update.entity_key, update.pi_entity});
  ASSERT_TRUE(table_entry_cache_success);
  cache_entry->second.mutable_table_entry()
      ->mutable_action()
      ->mutable_action_profile_action_set()
      ->mutable_action_profile_actions(0)
      ->set_weight(3);
  cache_entry->second.mutable_table_entry()
      ->mutable_action()
      ->mutable_action_profile_action_set()
      ->mutable_action_profile_actions()
      ->RemoveLast();

  ASSERT_OK_AND_ASSIGN(
      TableResources resources,
      VerifyCapacityAndGetTableResourceChange(ir_p4info_, update, entity_cache_,
                                              capacity_by_action_profile_name_,
                                              resources_in_current_batch_));

  // This modify is changing from 1 action and a weight of 3 to 2 actions with a
  // total weight of 2. So we gain 1 group, and lose 1 weight.
  EXPECT_THAT(resources.name, wcmp_table_name_);
  EXPECT_THAT(resources.action_profile,
              Optional(FieldsAre(wcmp_selector_name_, /*number_of_actions=*/1,
                                 /*total_weight=*/-1, /*max_weight=*/1)));
}

TEST_F(GetTableResourceChangeTest, CanGetDeleteResources) {
  ASSERT_OK_AND_ASSIGN(EntityUpdate update,
                       GetUpdate(ir_p4info_, p4::v1::Update::DELETE,
                                 R"pb(
                                   table_entry {
                                     table_name: "wcmp_group_table"
                                     matches {
                                       name: "wcmp_group_id"
                                       exact { str: "group-1" }
                                     }
                                     action_set {
                                       actions {
                                         action {
                                           name: "set_nexthop_id"
                                           params {
                                             name: "nexthop_id"
                                             value { str: "nexthop-1" }
                                           }
                                         }
                                         weight: 4
                                       }
                                       actions {
                                         action {
                                           name: "set_nexthop_id"
                                           params {
                                             name: "nexthop_id"
                                             value { str: "nexthop-2" }
                                           }
                                         }
                                         weight: 3
                                       }
                                     }
                                   })pb"));

  // Insert the entry into the cache so we can delete it.
  auto [cache_entry, table_entry_cache_success] =
      entity_cache_.insert({update.entity_key, update.pi_entity});
  ASSERT_TRUE(table_entry_cache_success);

  ASSERT_OK_AND_ASSIGN(
      TableResources resources,
      VerifyCapacityAndGetTableResourceChange(ir_p4info_, update, entity_cache_,
                                              capacity_by_action_profile_name_,
                                              resources_in_current_batch_));

  EXPECT_THAT(resources.name, wcmp_table_name_);
  EXPECT_THAT(resources.action_profile,
              Optional(FieldsAre(wcmp_selector_name_, /*number_of_actions=*/-2,
                                 /*total_weight=*/-7, /*max_weight=*/0)));
}

TEST_F(GetTableResourceChangeTest, InvalidTableNameFails) {
  ASSERT_OK_AND_ASSIGN(EntityUpdate update,
                       GetUpdate(ir_p4info_, p4::v1::Update::INSERT,
                                 R"pb(
                                   table_entry {
                                     table_name: "wcmp_group_table"
                                     matches {
                                       name: "wcmp_group_id"
                                       exact { str: "group-1" }
                                     }
                                     action_set {
                                       actions {
                                         action {
                                           name: "set_nexthop_id"
                                           params {
                                             name: "nexthop_id"
                                             value { str: "nexthop-1" }
                                           }
                                         }
                                         weight: 1
                                       }
                                     }
                                   })pb"));

  update.entry.mutable_table_entry()->set_table_name("bad_table_name");

  EXPECT_THAT(
      VerifyCapacityAndGetTableResourceChange(ir_p4info_, update, entity_cache_,
                                              capacity_by_action_profile_name_,
                                              resources_in_current_batch_),
      StatusIs(absl::StatusCode::kInvalidArgument,
               HasSubstr("Could not get table resources")));
}

TEST_F(GetTableResourceChangeTest, InvalidCacheEntryFails) {
  ASSERT_OK_AND_ASSIGN(EntityUpdate update,
                       GetUpdate(ir_p4info_, p4::v1::Update::DELETE,
                                 R"pb(
                                   table_entry {
                                     table_name: "wcmp_group_table"
                                     matches {
                                       name: "wcmp_group_id"
                                       exact { str: "group-1" }
                                     }
                                     action_set {
                                       actions {
                                         action {
                                           name: "set_nexthop_id"
                                           params {
                                             name: "nexthop_id"
                                             value { str: "nexthop-1" }
                                           }
                                         }
                                         weight: 1
                                       }
                                     }
                                   })pb"));

  // Invalidate the cached table entry.
  auto [cache_entry, table_entry_cache_success] =
      entity_cache_.insert({update.entity_key, update.pi_entity});
  ASSERT_TRUE(table_entry_cache_success);
  cache_entry->second.mutable_table_entry()->set_table_id(0);

  EXPECT_THAT(
      VerifyCapacityAndGetTableResourceChange(ir_p4info_, update, entity_cache_,
                                              capacity_by_action_profile_name_,
                                              resources_in_current_batch_),
      StatusIs(absl::StatusCode::kNotFound,
               HasSubstr("Could not get resources for cached table entry")));
}

TEST_F(GetTableResourceChangeTest, NoExistingResourceCapacityFails) {
  ASSERT_OK_AND_ASSIGN(EntityUpdate update,
                       GetUpdate(ir_p4info_, p4::v1::Update::INSERT,
                                 R"pb(
                                   table_entry {
                                     table_name: "wcmp_group_table"
                                     matches {
                                       name: "wcmp_group_id"
                                       exact { str: "group-1" }
                                     }
                                     action_set {
                                       actions {
                                         action {
                                           name: "set_nexthop_id"
                                           params {
                                             name: "nexthop_id"
                                             value { str: "nexthop-1" }
                                           }
                                         }
                                         weight: 1
                                       }
                                     }
                                   })pb"));

  capacity_by_action_profile_name_.clear();

  EXPECT_THAT(
      VerifyCapacityAndGetTableResourceChange(ir_p4info_, update, entity_cache_,
                                              capacity_by_action_profile_name_,
                                              resources_in_current_batch_),
      StatusIs(absl::StatusCode::kNotFound,
               HasSubstr("Could not get the current capacity data for")));
}

TEST_F(GetTableResourceChangeTest, RejectsRequestsWithTooManyActions) {
  ASSERT_OK_AND_ASSIGN(EntityUpdate update,
                       GetUpdate(ir_p4info_, p4::v1::Update::INSERT,
                                 R"pb(
                                   table_entry {
                                     table_name: "wcmp_group_table"
                                     matches {
                                       name: "wcmp_group_id"
                                       exact { str: "group-1" }
                                     }
                                     action_set {
                                       actions {
                                         action {
                                           name: "set_nexthop_id"
                                           params {
                                             name: "nexthop_id"
                                             value { str: "nexthop-1" }
                                           }
                                         }
                                         weight: 1
                                       }
                                       actions {
                                         action {
                                           name: "set_nexthop_id"
                                           params {
                                             name: "nexthop_id"
                                             value { str: "nexthop-2" }
                                           }
                                         }
                                         weight: 1
                                       }
                                       actions {
                                         action {
                                           name: "set_nexthop_id"
                                           params {
                                             name: "nexthop_id"
                                             value { str: "nexthop-3" }
                                           }
                                         }
                                         weight: 1
                                       }
                                     }
                                   })pb"));

  // Set the max group size to 2.
  for (auto& [name, capacity] : capacity_by_action_profile_name_) {
    capacity.action_profile.set_max_group_size(2);
  }

  EXPECT_THAT(
      VerifyCapacityAndGetTableResourceChange(ir_p4info_, update, entity_cache_,
                                              capacity_by_action_profile_name_,
                                              resources_in_current_batch_),
      StatusIs(absl::StatusCode::kInvalidArgument,
               HasSubstr("max allowed is 2, but got 3")));
}

TEST_F(GetTableResourceChangeTest, PacketReplicationEntriesIgnored) {
  ASSERT_OK_AND_ASSIGN(
      EntityUpdate update,
      GetUpdate(ir_p4info_, p4::v1::Update::INSERT,
                R"pb(
                  packet_replication_engine_entry {
                    multicast_group_entry {
                      multicast_group_id: 1
                      replicas { port: "Ethernet0" instance: 1 }
                      replicas { port: "Ethernet0" instance: 2 }
                    }
                  })pb"));

  ASSERT_OK_AND_ASSIGN(
      TableResources resources,
      VerifyCapacityAndGetTableResourceChange(ir_p4info_, update, entity_cache_,
                                              capacity_by_action_profile_name_,
                                              resources_in_current_batch_));

  EXPECT_EQ(resources.name, "");
  EXPECT_EQ(resources.action_profile, std::nullopt);
}

TEST(VerifyCapacityAndGetTableResourceChangeTest,
     ValidWeightIsAcceptedInSumOfWeights) {
  constexpr int kSize = 12000;
  constexpr int kMaxGroupSize = 512;
  constexpr int kActionProfileId = 3;
  constexpr absl::string_view kActionProfileName = "wcmp_selector_profile";
  const IrActionDefinitionBuilder no_action_builder =
      IrActionDefinitionBuilder().name("NoAction");

  const pdpi::IrP4Info ir_p4info =
      IrP4InfoBuilder()
          .table(IrTableDefinitionBuilder()
                     .name("wcmp_group_table")
                     .match_field(R"pb(
                                    id: 1
                                    name: "wcmp_group_id"
                                    match_type: EXACT
                                  )pb",
                                  pdpi::Format::STRING)
                     .entry_action(no_action_builder)
                     .size(100))
          .action(no_action_builder)
          .action_profile(IrActionProfileDefinitionBuilder()
                              .id(kActionProfileId)
                              .name(kActionProfileName)
                              .max_sum_of_weights(kSize, kMaxGroupSize)
                              .table_ids({1}))();

  ASSERT_OK_AND_ASSIGN(EntityUpdate update,
                       GetUpdate(ir_p4info, p4::v1::Update::INSERT,
                                 R"pb(
                                   table_entry {
                                     table_name: "wcmp_group_table"
                                     matches {
                                       name: "wcmp_group_id"
                                       exact { str: "group-1" }
                                     }
                                     action_set {
                                       actions {
                                         action { name: "NoAction" }
                                         weight: 5
                                       }
                                     }
                                   })pb"));

  absl::flat_hash_map<std::string, ActionProfileResourceCapacity>
      capacity_by_action_profile_name = {
          {std::string(kActionProfileName),
           GetActionProfileResourceCapacity(
               ir_p4info.action_profiles_by_id().at(kActionProfileId))},
      };
  absl::flat_hash_map<std::string, int64_t> current_batch_resources;

  EXPECT_THAT(VerifyCapacityAndGetTableResourceChange(
                  ir_p4info, update, /*entity_cache=*/{},
                  capacity_by_action_profile_name, current_batch_resources),
              IsOk());
}

TEST(VerifyCapacityAndGetTableResourceChangeTest,
     VeryHighWeightIsAcceptedInSumOfMembers) {
  constexpr int kSize = 12000;
  constexpr int kMaxGroupSize = 512;
  // Greater than size.
  constexpr int kMaxMemberWeight = 60000;
  constexpr int kActionProfileId = 3;
  constexpr absl::string_view kActionProfileName = "wcmp_selector_profile";
  const IrActionDefinitionBuilder no_action_builder =
      IrActionDefinitionBuilder().name("NoAction");

  const pdpi::IrP4Info ir_p4info =
      IrP4InfoBuilder()
          .table(IrTableDefinitionBuilder()
                     .name("wcmp_group_table")
                     .match_field(R"pb(
                                    id: 1
                                    name: "wcmp_group_id"
                                    match_type: EXACT
                                  )pb",
                                  pdpi::Format::STRING)
                     .entry_action(no_action_builder)
                     .size(100))
          .action(no_action_builder)
          .action_profile(
              IrActionProfileDefinitionBuilder()
                  .id(kActionProfileId)
                  .name(kActionProfileName)
                  .max_sum_of_members(kSize, kMaxGroupSize, kMaxMemberWeight)
                  .table_ids({1}))();

  ASSERT_OK_AND_ASSIGN(EntityUpdate update,
                       GetUpdate(ir_p4info, p4::v1::Update::INSERT,
                                 R"pb(
                                   table_entry {
                                     table_name: "wcmp_group_table"
                                     matches {
                                       name: "wcmp_group_id"
                                       exact { str: "group-1" }
                                     }
                                     action_set {
                                       actions {
                                         action { name: "NoAction" }
                                         # More than the size.
                                         weight: 30000
                                       }
                                       actions {
                                         action { name: "NoAction" }
                                         # More than the size again.
                                         weight: 35000
                                       }
                                     }
                                   })pb"));

  absl::flat_hash_map<std::string, ActionProfileResourceCapacity>
      capacity_by_action_profile_name = {
          {std::string(kActionProfileName),
           GetActionProfileResourceCapacity(
               ir_p4info.action_profiles_by_id().at(kActionProfileId))},
      };
  absl::flat_hash_map<std::string, int64_t> current_batch_resources;

  EXPECT_THAT(VerifyCapacityAndGetTableResourceChange(
                  ir_p4info, update, /*entity_cache=*/{},
                  capacity_by_action_profile_name, current_batch_resources),
              IsOk());
}

TEST(VerifyCapacityAndGetTableResourceChangeTest,
     RejectsTooMuchWeightInSumOfWeights) {
  constexpr int kSize = 10;
  constexpr int kMaxGroupSize = 512;
  constexpr int kActionProfileId = 3;
  constexpr absl::string_view kActionProfileName = "wcmp_selector_profile";
  const IrActionDefinitionBuilder no_action_builder =
      IrActionDefinitionBuilder().name("NoAction");

  const pdpi::IrP4Info ir_p4info =
      IrP4InfoBuilder()
          .table(IrTableDefinitionBuilder()
                     .name("wcmp_group_table")
                     .match_field(R"pb(
                                    id: 1
                                    name: "wcmp_group_id"
                                    match_type: EXACT
                                  )pb",
                                  pdpi::Format::STRING)
                     .entry_action(no_action_builder)
                     .size(100))
          .action(no_action_builder)
          .action_profile(IrActionProfileDefinitionBuilder()
                              .id(kActionProfileId)
                              .name(kActionProfileName)
                              .max_sum_of_weights(kSize, kMaxGroupSize)
                              .table_ids({1}))();

  ASSERT_OK_AND_ASSIGN(EntityUpdate update,
                       GetUpdate(ir_p4info, p4::v1::Update::INSERT,
                                 R"pb(
                                   table_entry {
                                     table_name: "wcmp_group_table"
                                     matches {
                                       name: "wcmp_group_id"
                                       exact { str: "group-1" }
                                     }
                                     action_set {
                                       actions {
                                         action { name: "NoAction" }
                                         # More than the size.
                                         weight: 100
                                       }
                                     }
                                   })pb"));

  absl::flat_hash_map<std::string, ActionProfileResourceCapacity>
      capacity_by_action_profile_name = {
          {std::string(kActionProfileName),
           GetActionProfileResourceCapacity(
               ir_p4info.action_profiles_by_id().at(kActionProfileId))},
      };
  absl::flat_hash_map<std::string, int64_t> current_batch_resources;

  EXPECT_THAT(VerifyCapacityAndGetTableResourceChange(
                  ir_p4info, update, /*entity_cache=*/{},
                  capacity_by_action_profile_name, current_batch_resources),
              StatusIs(absl::StatusCode::kResourceExhausted));
}

TEST(VerifyCapacityAndGetTableResourceChangeTest,
     RejectsTooMuchWeightInASingleRequestSumOfWeights) {
  constexpr int kSize = 12000;
  constexpr int kMaxGroupSize = 512;
  constexpr int kActionProfileId = 3;
  constexpr absl::string_view kActionProfileName = "wcmp_selector_profile";
  const IrActionDefinitionBuilder no_action_builder =
      IrActionDefinitionBuilder().name("NoAction");

  const pdpi::IrP4Info ir_p4info =
      IrP4InfoBuilder()
          .table(IrTableDefinitionBuilder()
                     .name("wcmp_group_table")
                     .match_field(R"pb(
                                    id: 1
                                    name: "wcmp_group_id"
                                    match_type: EXACT
                                  )pb",
                                  pdpi::Format::STRING)
                     .entry_action(no_action_builder)
                     .size(100))
          .action(no_action_builder)
          .action_profile(IrActionProfileDefinitionBuilder()
                              .id(kActionProfileId)
                              .name(kActionProfileName)
                              .max_sum_of_weights(kSize, kMaxGroupSize)
                              .table_ids({1}))();

  ASSERT_OK_AND_ASSIGN(EntityUpdate update,
                       GetUpdate(ir_p4info, p4::v1::Update::INSERT,
                                 R"pb(
                                   table_entry {
                                     table_name: "wcmp_group_table"
                                     matches {
                                       name: "wcmp_group_id"
                                       exact { str: "group-1" }
                                     }
                                     action_set {
                                       actions {
                                         action { name: "NoAction" }
                                         weight: 301
                                       }
                                       actions {
                                         action { name: "NoAction" }
                                         weight: 302
                                       }
                                     }
                                   })pb"));

  absl::flat_hash_map<std::string, ActionProfileResourceCapacity>
      capacity_by_action_profile_name = {
          {std::string(kActionProfileName),
           GetActionProfileResourceCapacity(
               ir_p4info.action_profiles_by_id().at(kActionProfileId))},
      };
  absl::flat_hash_map<std::string, int64_t> current_batch_resources;

  EXPECT_THAT(VerifyCapacityAndGetTableResourceChange(
                  ir_p4info, update, /*entity_cache=*/{},
                  capacity_by_action_profile_name, current_batch_resources),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(VerifyCapacityAndGetTableResourceChangeTest,
     RejectsTooManyMembersInSumOfMembers) {
  constexpr int kSize = 3;
  constexpr int kMaxGroupSize = 512;
  constexpr int kMaxMemberWeight = 4096;
  constexpr int kActionProfileId = 3;
  constexpr absl::string_view kActionProfileName = "wcmp_selector_profile";
  const IrActionDefinitionBuilder no_action_builder =
      IrActionDefinitionBuilder().name("NoAction");

  const pdpi::IrP4Info ir_p4info =
      IrP4InfoBuilder()
          .table(IrTableDefinitionBuilder()
                     .name("wcmp_group_table")
                     .match_field(R"pb(
                                    id: 1
                                    name: "wcmp_group_id"
                                    match_type: EXACT
                                  )pb",
                                  pdpi::Format::STRING)
                     .entry_action(no_action_builder)
                     .size(100))
          .action(no_action_builder)
          .action_profile(
              IrActionProfileDefinitionBuilder()
                  .id(kActionProfileId)
                  .name(kActionProfileName)
                  .max_sum_of_members(kSize, kMaxGroupSize, kMaxMemberWeight)
                  .table_ids({1}))();

  ASSERT_OK_AND_ASSIGN(EntityUpdate update,
                       GetUpdate(ir_p4info, p4::v1::Update::INSERT,
                                 R"pb(
                                   table_entry {
                                     table_name: "wcmp_group_table"
                                     matches {
                                       name: "wcmp_group_id"
                                       exact { str: "group-1" }
                                     }
                                     action_set {
                                       actions {
                                         action { name: "NoAction" }
                                         weight: 500
                                       }
                                       actions {
                                         action { name: "NoAction" }
                                         weight: 501
                                       }
                                       actions {
                                         action { name: "NoAction" }
                                         weight: 502
                                       }
                                       actions {
                                         action { name: "NoAction" }
                                         weight: 503
                                       }
                                     }
                                   })pb"));

  absl::flat_hash_map<std::string, ActionProfileResourceCapacity>
      capacity_by_action_profile_name = {
          {std::string(kActionProfileName),
           GetActionProfileResourceCapacity(
               ir_p4info.action_profiles_by_id().at(kActionProfileId))},
      };
  absl::flat_hash_map<std::string, int64_t> current_batch_resources;

  EXPECT_THAT(VerifyCapacityAndGetTableResourceChange(
                  ir_p4info, update, /*entity_cache=*/{},
                  capacity_by_action_profile_name, current_batch_resources),
              StatusIs(absl::StatusCode::kResourceExhausted));
}

TEST(VerifyCapacityAndGetTableResourceChangeTest,
     RejectsTooBigMemberInSumOfMembers) {
  constexpr int kSize = 12000;
  constexpr int kMaxGroupSize = 512;
  constexpr int kMaxMemberWeight = 4096;
  constexpr int kActionProfileId = 3;
  constexpr absl::string_view kActionProfileName = "wcmp_selector_profile";
  const IrActionDefinitionBuilder no_action_builder =
      IrActionDefinitionBuilder().name("NoAction");

  const pdpi::IrP4Info ir_p4info =
      IrP4InfoBuilder()
          .table(IrTableDefinitionBuilder()
                     .name("wcmp_group_table")
                     .match_field(R"pb(
                                    id: 1
                                    name: "wcmp_group_id"
                                    match_type: EXACT
                                  )pb",
                                  pdpi::Format::STRING)
                     .entry_action(no_action_builder)
                     .size(100))
          .action(no_action_builder)
          .action_profile(
              IrActionProfileDefinitionBuilder()
                  .id(kActionProfileId)
                  .name(kActionProfileName)
                  .max_sum_of_members(kSize, kMaxGroupSize, kMaxMemberWeight)
                  .table_ids({1}))();

  ASSERT_OK_AND_ASSIGN(EntityUpdate update,
                       GetUpdate(ir_p4info, p4::v1::Update::INSERT,
                                 R"pb(
                                   table_entry {
                                     table_name: "wcmp_group_table"
                                     matches {
                                       name: "wcmp_group_id"
                                       exact { str: "group-1" }
                                     }
                                     action_set {
                                       actions {
                                         action { name: "NoAction" }
                                         # More than kMaxMemberWeight.
                                         weight: 10000
                                       }
                                     }
                                   })pb"));

  absl::flat_hash_map<std::string, ActionProfileResourceCapacity>
      capacity_by_action_profile_name = {
          {std::string(kActionProfileName),
           GetActionProfileResourceCapacity(
               ir_p4info.action_profiles_by_id().at(kActionProfileId))},
      };
  absl::flat_hash_map<std::string, int64_t> current_batch_resources;

  EXPECT_THAT(VerifyCapacityAndGetTableResourceChange(
                  ir_p4info, update, /*entity_cache=*/{},
                  capacity_by_action_profile_name, current_batch_resources),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(VerifyCapacityAndGetTableResourceChangeTest,
     ConsidersOtherRequestsIntheBatchInSumOfWeights) {
  constexpr int kSize = 12000;
  constexpr int kMaxGroupSize = 512;
  constexpr int kActionProfileId = 3;
  constexpr absl::string_view kActionProfileName = "wcmp_selector_profile";
  const IrActionDefinitionBuilder no_action_builder =
      IrActionDefinitionBuilder().name("NoAction");

  const pdpi::IrP4Info ir_p4info =
      IrP4InfoBuilder()
          .table(IrTableDefinitionBuilder()
                     .name("wcmp_group_table")
                     .match_field(R"pb(
                                    id: 1
                                    name: "wcmp_group_id"
                                    match_type: EXACT
                                  )pb",
                                  pdpi::Format::STRING)
                     .entry_action(no_action_builder)
                     .size(100))
          .action(no_action_builder)
          .action_profile(IrActionProfileDefinitionBuilder()
                              .id(kActionProfileId)
                              .name(kActionProfileName)
                              .max_sum_of_weights(kSize, kMaxGroupSize)
                              .table_ids({1}))();

  ASSERT_OK_AND_ASSIGN(EntityUpdate update,
                       GetUpdate(ir_p4info, p4::v1::Update::INSERT,
                                 R"pb(
                                   table_entry {
                                     table_name: "wcmp_group_table"
                                     matches {
                                       name: "wcmp_group_id"
                                       exact { str: "group-1" }
                                     }
                                     action_set {
                                       actions {
                                         action { name: "NoAction" }
                                         weight: 1
                                       }
                                     }
                                   })pb"));

  // Set the utilization for everything to full.
  ActionProfileResourceCapacity capacity = GetActionProfileResourceCapacity(
      ir_p4info.action_profiles_by_id().at(kActionProfileId));
  capacity.current_total_weight = capacity.action_profile.size();
  capacity.current_total_members = capacity.action_profile.size();

  absl::flat_hash_map<std::string, ActionProfileResourceCapacity>
      capacity_by_action_profile_name = {
          {std::string(kActionProfileName), std::move(capacity)},
      };
  absl::flat_hash_map<std::string, int64_t> current_batch_resources;

  EXPECT_THAT(VerifyCapacityAndGetTableResourceChange(
                  ir_p4info, update, /*entity_cache=*/{},
                  capacity_by_action_profile_name, current_batch_resources),
              StatusIs(absl::StatusCode::kResourceExhausted,
                       HasSubstr("not enough resources to fit in")));
}

TEST(VerifyCapacityAndGetTableResourceChangeTest,
     ConsidersOtherRequestsIntheBatchInSumOfMembers) {
  constexpr int kSize = 12000;
  constexpr int kMaxGroupSize = 512;
  constexpr int kMaxMemberWeight = 4096;
  constexpr int kActionProfileId = 3;
  constexpr absl::string_view kActionProfileName = "wcmp_selector_profile";
  const IrActionDefinitionBuilder no_action_builder =
      IrActionDefinitionBuilder().name("NoAction");

  const pdpi::IrP4Info ir_p4info =
      IrP4InfoBuilder()
          .table(IrTableDefinitionBuilder()
                     .name("wcmp_group_table")
                     .match_field(R"pb(
                                    id: 1
                                    name: "wcmp_group_id"
                                    match_type: EXACT
                                  )pb",
                                  pdpi::Format::STRING)
                     .entry_action(no_action_builder)
                     .size(100))
          .action(no_action_builder)
          .action_profile(
              IrActionProfileDefinitionBuilder()
                  .id(kActionProfileId)
                  .name(kActionProfileName)
                  .max_sum_of_members(kSize, kMaxGroupSize, kMaxMemberWeight)
                  .table_ids({1}))();

  ASSERT_OK_AND_ASSIGN(EntityUpdate update,
                       GetUpdate(ir_p4info, p4::v1::Update::INSERT,
                                 R"pb(
                                   table_entry {
                                     table_name: "wcmp_group_table"
                                     matches {
                                       name: "wcmp_group_id"
                                       exact { str: "group-1" }
                                     }
                                     action_set {
                                       actions {
                                         action { name: "NoAction" }
                                         weight: 1
                                       }
                                     }
                                   })pb"));

  // Set the utilization for everything to full.
  ActionProfileResourceCapacity capacity = GetActionProfileResourceCapacity(
      ir_p4info.action_profiles_by_id().at(kActionProfileId));
  capacity.current_total_weight = capacity.action_profile.size();
  capacity.current_total_members = capacity.action_profile.size();

  absl::flat_hash_map<std::string, ActionProfileResourceCapacity>
      capacity_by_action_profile_name = {
          {std::string(kActionProfileName), std::move(capacity)},
      };
  absl::flat_hash_map<std::string, int64_t> current_batch_resources;

  EXPECT_THAT(VerifyCapacityAndGetTableResourceChange(
                  ir_p4info, update, /*entity_cache=*/{},
                  capacity_by_action_profile_name, current_batch_resources),
              StatusIs(absl::StatusCode::kResourceExhausted,
                       HasSubstr("not enough resources to fit in")));
}

TEST(ActionProfileResourceCapacityTest, UsesSumOfXTests) {
  constexpr int kSize = 1;
  constexpr int kMaxGroupSize = 1;
  constexpr int kMaxMemberWeight = 1;
  {
    ActionProfileResourceCapacity capacity_without_specified_semantics =
        GetActionProfileResourceCapacity(
            IrActionProfileDefinitionBuilder()
                .name("wcmp_selector_profile_without_size_selector_semantics")
                .wcmp_selector_size(kSize, kMaxGroupSize)());
    EXPECT_TRUE(UsesSumOfWeights(capacity_without_specified_semantics));
    EXPECT_FALSE(UsesSumOfMembers(capacity_without_specified_semantics));
  }

  {
    ActionProfileResourceCapacity capacity_with_explicit_sum_of_weights =
        GetActionProfileResourceCapacity(
            IrActionProfileDefinitionBuilder()
                .name("wcmp_selector_profile_with_sum_of_weights")
                .max_sum_of_weights(kSize, kMaxGroupSize)());
    EXPECT_TRUE(UsesSumOfWeights(capacity_with_explicit_sum_of_weights));
    EXPECT_FALSE(UsesSumOfMembers(capacity_with_explicit_sum_of_weights));
  }
  {
    ActionProfileResourceCapacity capacity_with_explicit_sum_of_members =
        GetActionProfileResourceCapacity(
            IrActionProfileDefinitionBuilder()
                .name("wcmp_selector_profile_with_sum_of_members")
                .max_sum_of_members(kSize, kMaxGroupSize, kMaxMemberWeight)());
    EXPECT_FALSE(UsesSumOfWeights(capacity_with_explicit_sum_of_members));
    EXPECT_TRUE(UsesSumOfMembers(capacity_with_explicit_sum_of_members));
  }
}

TEST(ActionProfileResourceCapacityTest, GetMaxXTests) {
  constexpr int kSize = 200;
  constexpr int kMaxGroupSize = 150;
  constexpr int kMaxMemberWeight = 100;
  {
    ActionProfileResourceCapacity capacity_without_specified_semantics =
        GetActionProfileResourceCapacity(
            IrActionProfileDefinitionBuilder()
                .name("wcmp_selector_profile_without_size_selector_semantics")
                .wcmp_selector_size(kSize, kMaxGroupSize)());
    // Only relevant when Sum Of Weights semantics are used (like here).
    EXPECT_THAT(GetMaxWeightForAllGroups(capacity_without_specified_semantics),
                Optional(kSize));
    EXPECT_THAT(GetMaxWeightPerGroup(capacity_without_specified_semantics),
                Optional(kMaxGroupSize));
    // Only relevant when Sum Of Members semantics are used (not here).
    EXPECT_THAT(GetMaxMembersForAllGroups(capacity_without_specified_semantics),
                Eq(std::nullopt));
    EXPECT_THAT(GetMaxMembersPerGroup(capacity_without_specified_semantics),
                Eq(std::nullopt));
    EXPECT_THAT(GetMaxWeightPerMember(capacity_without_specified_semantics),
                Eq(std::nullopt));
  }

  {
    ActionProfileResourceCapacity capacity_with_explicit_sum_of_weights =
        GetActionProfileResourceCapacity(
            IrActionProfileDefinitionBuilder()
                .name("wcmp_selector_profile_with_sum_of_weights")
                .max_sum_of_weights(kSize, kMaxGroupSize)());
    // Only relevant when Sum Of Weights semantics are used (like here).
    EXPECT_THAT(GetMaxWeightForAllGroups(capacity_with_explicit_sum_of_weights),
                Optional(kSize));
    EXPECT_THAT(GetMaxWeightPerGroup(capacity_with_explicit_sum_of_weights),
                Optional(kMaxGroupSize));
    // Only relevant when Sum Of Members semantics are used (not here).
    EXPECT_THAT(
        GetMaxMembersForAllGroups(capacity_with_explicit_sum_of_weights),
        Eq(std::nullopt));
    EXPECT_THAT(GetMaxMembersPerGroup(capacity_with_explicit_sum_of_weights),
                Eq(std::nullopt));
    EXPECT_THAT(GetMaxWeightPerMember(capacity_with_explicit_sum_of_weights),
                Eq(std::nullopt));
  }
  {
    ActionProfileResourceCapacity capacity_with_explicit_sum_of_members =
        GetActionProfileResourceCapacity(
            IrActionProfileDefinitionBuilder()
                .name("wcmp_selector_profile_with_sum_of_members")
                .max_sum_of_members(kSize, kMaxGroupSize, kMaxMemberWeight)());
    // Only relevant when Sum Of Weights semantics are used (not here).
    EXPECT_THAT(GetMaxWeightForAllGroups(capacity_with_explicit_sum_of_members),
                Eq(std::nullopt));
    EXPECT_THAT(GetMaxWeightPerGroup(capacity_with_explicit_sum_of_members),
                Eq(std::nullopt));
    // Only relevant when Sum Of Members semantics are used (like here).
    EXPECT_THAT(
        GetMaxMembersForAllGroups(capacity_with_explicit_sum_of_members),
        Optional(kSize));
    EXPECT_THAT(GetMaxMembersPerGroup(capacity_with_explicit_sum_of_members),
                Optional(kMaxGroupSize));
    EXPECT_THAT(GetMaxWeightPerMember(capacity_with_explicit_sum_of_members),
                Optional(kMaxMemberWeight));
  }
}

}  // namespace
}  // namespace p4rt_app
