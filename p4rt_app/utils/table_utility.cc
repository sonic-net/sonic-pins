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
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "google/protobuf/map.h"
#include "gutil/gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_infra/p4_pdpi/annotation_parser.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
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

std::vector<pdpi::IrTableDefinition> OrderTablesBySize(
    const google::protobuf::Map<std::string, pdpi::IrTableDefinition>&
        tables_by_name) {
  // Store the table definition, and any interesting fields for determining the
  // order.
  struct OrderingFields {
    pdpi::IrTableDefinition table_def;
    std::string table_name;
    int bitwidth;
  };

  // Collect all the table definitions and sum the bitwidths of all the match
  // fields.
  //
  // NOTE: Not all match fields in P4 will have a bitwidth (e.g. in_port), and
  // this logic will treat those fields as having a bitwidth of 0. So this is
  // not a perfect solution, but since most fields will have a bitwidth we
  // consider it "good enough".
  std::vector<OrderingFields> acl_tables;
  acl_tables.reserve(tables_by_name.size());
  for (const auto& [table_name, table_def] : tables_by_name) {
    int bitwidth = 0;
    for (const auto& [field_name, field_def] :
         table_def.match_fields_by_name()) {
      bitwidth += field_def.match_field().bitwidth();
    }
    acl_tables.push_back(OrderingFields{
        .table_def = table_def,
        .table_name = table_name,
        .bitwidth = bitwidth,
    });
  }

  // Sort in descending bitwidth order.
  std::sort(acl_tables.begin(), acl_tables.end(),
            [](const OrderingFields& lhs, const OrderingFields& rhs) {
              if (lhs.bitwidth != rhs.bitwidth) {
                return lhs.bitwidth > rhs.bitwidth;
              }
              return lhs.table_name > rhs.table_name;
            });

  std::vector<pdpi::IrTableDefinition> result;
  result.reserve(acl_tables.size());
  for (const auto& table : acl_tables) {
    result.push_back(std::move(table.table_def));
  }
  return result;
}

}  // namespace p4rt_app
