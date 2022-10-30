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

#include "absl/status/status.h"
#include "gutil/status.h"
#include "absl/strings/substitute.h"
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
  if (type_name == APP_P4RT_ACL_TABLE_DEFINITION_NAME) return Type::kAclDefinition;
  if (type_name == APP_P4RT_TABLES_DEFINITION_TABLE_NAME) return Type::kTblsDefinitionSet;
  return gutil::InvalidArgumentErrorBuilder()
         << "\"" << type_name << "\" does not name a valid table::Type.";
}

}  // namespace table

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
      return table::Type::kExt;
    default:
      return gutil::InvalidArgumentErrorBuilder()
             << "Failed to determine table type: " << result.status();
  }
}

}  // namespace p4rt_app
