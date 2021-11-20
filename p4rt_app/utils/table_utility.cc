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
#include "p4_pdpi/utils/annotation_parser.h"
#include "swss/schema.h"

namespace p4rt_app {
namespace table {

std::string TypeName(Type type) {
  switch (type) {
    case Type::kAcl:
      return "ACL";
    case Type::kFixed:
      return "FIXED";
    case Type::kDefinition:
      return APP_P4RT_ACL_TABLE_DEFINITION_NAME;
  }
  // TODO: return status failure.
}

absl::StatusOr<Type> TypeParse(absl::string_view type_name) {
  if (type_name == "ACL") return Type::kAcl;
  if (type_name == "FIXED") return Type::kFixed;
  if (type_name == APP_P4RT_ACL_TABLE_DEFINITION_NAME) return Type::kDefinition;
  return gutil::InvalidArgumentErrorBuilder()
         << "\"" << type_name << "\" does not name a valid table::Type.";
}

}  // namespace table

absl::StatusOr<table::Type> GetTableType(
    const pdpi::IrTableDefinition& ir_table) {
  auto result =
      pdpi::GetAnnotationBody("sai_acl", ir_table.preamble().annotations());
  switch (result.status().code()) {
    case absl::StatusCode::kOk:
      return table::Type::kAcl;
    case absl::StatusCode::kNotFound:
      return table::Type::kFixed;
    default:
      return gutil::InvalidArgumentErrorBuilder()
             << "Failed to determine table type: " << result.status();
  }
}

}  // namespace p4rt_app
