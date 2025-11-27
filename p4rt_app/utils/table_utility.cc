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
#include "p4rt_app/utils/table_utility.h"

#include <algorithm>
#include <string>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "google/protobuf/map.h"
#include "gutil/gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/utils/annotation_parser.h"
#include "swss/schema.h"

namespace p4rt_app {
namespace table {

// This is what orch agent understands as fixed tables
std::vector<std::string> FixedTables {
  APP_P4RT_ROUTER_INTERFACE_TABLE_NAME,
  APP_P4RT_NEIGHBOR_TABLE_NAME,
  APP_P4RT_NEXTHOP_TABLE_NAME,
  APP_P4RT_WCMP_GROUP_TABLE_NAME,
  APP_P4RT_IPV4_TABLE_NAME,
  APP_P4RT_IPV6_TABLE_NAME,
  APP_P4RT_MIRROR_SESSION_TABLE_NAME,
  APP_P4RT_L3_ADMIT_TABLE_NAME,
  APP_P4RT_TUNNEL_TABLE_NAME
};

std::string TypeName(Type type) {
  switch (type) {
    case Type::kAcl:
      return "ACL";
    case Type::kFixed:
      return "FIXED";
    case Type::kExt:
      return "EXT";
    case Type::kAclDefinition:
      return APP_P4RT_ACL_TABLE_DEFINITION_NAME;
    case Type::kTblsDefinitionSet:
      return APP_P4RT_TABLES_DEFINITION_TABLE_NAME;
  }
  // TODO: return status failure.
}

absl::StatusOr<Type> TypeParse(absl::string_view type_name) {
  if (type_name == "ACL") return Type::kAcl;
  if (type_name == "FIXED") return Type::kFixed;
  if (type_name == "EXT") return Type::kExt;
  if (type_name == APP_P4RT_ACL_TABLE_DEFINITION_NAME) {
          return Type::kAclDefinition;
  }
  if (type_name == APP_P4RT_TABLES_DEFINITION_TABLE_NAME) {
          return Type::kTblsDefinitionSet;
  }
  return gutil::InvalidArgumentErrorBuilder()
         << "\"" << type_name << "\" does not name a valid table::Type.";
}

}  // namespace table

table::Type conditional_kExt(const pdpi::IrTableDefinition& ir_table)
{
    if (ir_table.preamble().id() > 0x03000000)
    {
        return table::Type::kExt;
    }
    return table::Type::kFixed;
}

absl::StatusOr<table::Type> GetTableType(
    const pdpi::IrTableDefinition& ir_table) {
  std::string table_name =
              absl::Substitute("$0_$1", "FIXED", ir_table.preamble().alias());
  absl::AsciiStrToUpper(&table_name);
  auto result =
      pdpi::GetAnnotationBody("sai_acl", ir_table.preamble().annotations());

  switch (result.status().code()) {
    case absl::StatusCode::kOk:
      return table::Type::kAcl;
    case absl::StatusCode::kNotFound:
      if (std::find(p4rt_app::table::FixedTables.begin(),
                    p4rt_app::table::FixedTables.end(),
                    table_name) != p4rt_app::table::FixedTables.end()) {
        return table::Type::kFixed;
      }

      // Return kExt table-type conditionally, until extension tables
      //     validation is in place. Once that is in place,
      //     return kExt table-type unconditionally
      return conditional_kExt(ir_table);
    default:
      return gutil::InvalidArgumentErrorBuilder()
             << "Failed to determine table type: " << result.status();
  }
}

namespace {
// Estimate the bitwidth of a table's match fields.
//
// NOTE: Not all match fields in P4 will have a bitwidth (e.g. in_port), and
// this logic will treat those fields as having a bitwidth of 0. So this is
// not a perfect solution, but since most fields will have a bitwidth we
// consider it "good enough".
int EstimateBitwidth(const pdpi::IrTableDefinition& table) {
  int bitwidth = 0;
  for (const auto& [field_name, field_def] : table.match_fields_by_name()) {
    bitwidth += field_def.match_field().bitwidth();
  }
  return bitwidth;
}
}  // namespace

void OrderTablesBySize(std::vector<const pdpi::IrTableDefinition*>& tables) {
  std::sort(tables.begin(), tables.end(),
            [](const pdpi::IrTableDefinition* const& lhs,
               const pdpi::IrTableDefinition* const& rhs) {
              int lhs_bitwidth = EstimateBitwidth(*lhs);
              int rhs_bitwidth = EstimateBitwidth(*rhs);
              return lhs_bitwidth != rhs_bitwidth
                         ? lhs_bitwidth > rhs_bitwidth
                         : lhs->preamble().alias() > rhs->preamble().alias();
            });
}

std::vector<const pdpi::IrTableDefinition*> OrderTablesBySize(
    const google::protobuf::Map<std::string, pdpi::IrTableDefinition>&
        tables_by_name) {
  std::vector<const pdpi::IrTableDefinition*> tables;
  tables.reserve(tables_by_name.size());
  for (const auto& [_, table] : tables_by_name) {
    tables.push_back(&table);
  }
  OrderTablesBySize(tables);
  return tables;
}

absl::StatusOr<std::string> DuplicateTable(pdpi::IrP4Info& ir_p4info,
                                           absl::string_view table_name) {
  auto lookup = ir_p4info.tables_by_name().find(table_name);
  if (lookup == ir_p4info.tables_by_name().end()) {
    return gutil::NotFoundErrorBuilder()
           << "Cannot duplicate table '" << table_name
           << "': Table not found in IrP4Info.";
  }
  int largest_table_id = 0;
  for (const auto& [id, _] : ir_p4info.tables_by_id()) {
    if (id > largest_table_id) largest_table_id = id;
  }
  std::string dup_table_name = absl::StrCat(table_name, "_duplicate_");
  int dup_table_id = largest_table_id + 1;

  pdpi::IrTableDefinition dup_table_def = lookup->second;
  int table_id = dup_table_def.preamble().id();

  dup_table_def.mutable_preamble()->set_alias(dup_table_name);
  absl::StrAppend(dup_table_def.mutable_preamble()->mutable_name(),
                  "_duplicate_");
  dup_table_def.mutable_preamble()->set_id(dup_table_id);

  ir_p4info.mutable_tables_by_name()->insert(
      std::make_pair(dup_table_name, dup_table_def));
  ir_p4info.mutable_tables_by_id()->insert(
      std::make_pair(dup_table_id, std::move(dup_table_def)));

  // Update the action profile references.
  for (auto& [_, action_profile_def] :
       *ir_p4info.mutable_action_profiles_by_name()) {
    auto& action_profile = *action_profile_def.mutable_action_profile();
    for (int id : action_profile.table_ids()) {
      if (id == table_id) {
        action_profile.add_table_ids(dup_table_id);
        ir_p4info.mutable_action_profiles_by_id()
            ->at(action_profile.preamble().id())
            .mutable_action_profile()
            ->add_table_ids(dup_table_id);
        break;
      }
    }
  }

  return dup_table_name;
}

}  // namespace p4rt_app
