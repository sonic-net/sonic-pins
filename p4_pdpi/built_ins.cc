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

#include "p4_pdpi/built_ins.h"

#include <string>

#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "gutil/status.h"
#include "p4_pdpi/ir.pb.h"

namespace pdpi {

namespace {
// General string constants.
constexpr absl::string_view kBuiltInPrefix = "builtin::";

// Multicast group table-related string constants.
constexpr absl::string_view kMulticastGroupTableString =
    "multicast_group_table";
constexpr absl::string_view kMulticastGroupIdString = "multicast_group_id";
constexpr absl::string_view kReplicaString = "replica";
constexpr absl::string_view kReplicaPortString = "replica.port";
constexpr absl::string_view kReplicaInstanceString = "replica.instance";

// Clone session table-related string constants.
constexpr absl::string_view kCloneSessionTableString = "clone_session_table";

}  // namespace

std::string GetMulticastGroupTableName() {
  return absl::StrCat(kBuiltInPrefix, kMulticastGroupTableString);
}

std::string GetReplicaActionName() {
  return absl::StrCat(kBuiltInPrefix, kReplicaString);
}

std::string GetCloneSessionTableName() {
  return absl::StrCat(kBuiltInPrefix, kCloneSessionTableString);
}

bool IsBuiltInTable(absl::string_view table_name) {
  return StringToIrBuiltInTable(table_name).ok();
}

bool IsBuiltInAction(absl::string_view action_name) {
  return StringToIrBuiltInAction(action_name).ok();
}

bool BuiltInTableHasMatchField(IrBuiltInTable table,
                               IrBuiltInMatchField field) {
  switch (table) {
    case BUILT_IN_TABLE_MULTICAST_GROUP_TABLE: {
      return field == BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID;
    }
    default: {
      return false;
    }
  }
}

bool BuiltInTableHasAction(IrBuiltInTable table, IrBuiltInAction action) {
  switch (table) {
    case BUILT_IN_TABLE_MULTICAST_GROUP_TABLE: {
      return action == BUILT_IN_ACTION_REPLICA;
    }
    default: {
      return false;
    }
  }
}

bool BuiltInActionHasParameter(IrBuiltInAction action,
                               IrBuiltInParameter parameter) {
  switch (action) {
    case BUILT_IN_TABLE_MULTICAST_GROUP_TABLE: {
      return parameter == BUILT_IN_PARAMETER_REPLICA_PORT ||
             parameter == BUILT_IN_PARAMETER_REPLICA_INSTANCE;
    }
    default: {
      return false;
    }
  }
}

absl::StatusOr<IrBuiltInAction> GetBuiltInActionFromBuiltInParameter(
    IrBuiltInParameter parameter) {
  switch (parameter) {
    case BUILT_IN_PARAMETER_REPLICA_PORT: {
      return BUILT_IN_ACTION_REPLICA;
    }
    case BUILT_IN_PARAMETER_REPLICA_INSTANCE: {
      return BUILT_IN_ACTION_REPLICA;
    }
    default: {
      return gutil::InvalidArgumentErrorBuilder()
             << "Unknown built-in parameter: "
             << IrBuiltInParameter_Name(parameter);
    }
  }
}

absl::StatusOr<std::string> IrBuiltInTableToString(IrBuiltInTable table) {
  switch (table) {
    case pdpi::BUILT_IN_TABLE_MULTICAST_GROUP_TABLE:
      return GetMulticastGroupTableName();
    case pdpi::BUILT_IN_TABLE_CLONE_SESSION_TABLE:
      return GetCloneSessionTableName();
    default: {
      return gutil::InvalidArgumentErrorBuilder()
             << "Unknown built-in table: " << IrBuiltInTable_Name(table);
    }
  }
}

absl::StatusOr<std::string> IrBuiltInMatchFieldToString(
    IrBuiltInMatchField field) {
  switch (field) {
    case BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID: {
      return std::string(kMulticastGroupIdString);
    }
    default: {
      return gutil::InvalidArgumentErrorBuilder()
             << "Unknown built-in match field: "
             << IrBuiltInMatchField_Name(field);
    }
  }
}

absl::StatusOr<std::string> IrBuiltInActionToString(IrBuiltInAction action) {
  switch (action) {
    case BUILT_IN_ACTION_REPLICA: {
      return absl::StrCat(kBuiltInPrefix, kReplicaString);
    }
    default: {
      return gutil::InvalidArgumentErrorBuilder()
             << "Unknown built-in action: " << IrBuiltInAction_Name(action);
    }
  }
}

absl::StatusOr<std::string> IrBuiltInParameterToString(
    IrBuiltInParameter parameter) {
  switch (parameter) {
    case BUILT_IN_PARAMETER_REPLICA_PORT: {
      return std::string(kReplicaPortString);
    }
    case BUILT_IN_PARAMETER_REPLICA_INSTANCE: {
      return std::string(kReplicaInstanceString);
    }
    default: {
      return gutil::InvalidArgumentErrorBuilder()
             << "Unknown built-in parameter: "
             << IrBuiltInParameter_Name(parameter);
    }
  }
}

absl::StatusOr<IrBuiltInTable> StringToIrBuiltInTable(absl::string_view table) {
  if (table == GetMulticastGroupTableName()) {
    return pdpi::BUILT_IN_TABLE_MULTICAST_GROUP_TABLE;
  }
  if (table == GetCloneSessionTableName()) {
    return pdpi::BUILT_IN_TABLE_CLONE_SESSION_TABLE;
  }
  return gutil::InvalidArgumentErrorBuilder()
         << "'" << table << "' is not a built-in table.";
}

absl::StatusOr<IrBuiltInMatchField> StringToIrBuiltInMatchField(
    absl::string_view field) {
  if (field == kMulticastGroupIdString) {
    return BUILT_IN_MATCH_FIELD_MULTICAST_GROUP_ID;
  }
  return gutil::InvalidArgumentErrorBuilder()
         << "'" << field << "' is not a built-in match field.";
}

absl::StatusOr<IrBuiltInAction> StringToIrBuiltInAction(
    absl::string_view action) {
  if (action == absl::StrCat(kBuiltInPrefix, kReplicaString)) {
    return BUILT_IN_ACTION_REPLICA;
  }
  return gutil::InvalidArgumentErrorBuilder()
         << "'" << action << "' is not a built-in action.";
}

absl::StatusOr<IrBuiltInParameter> StringToIrBuiltInParameter(
    absl::string_view parameter) {
  if (parameter == kReplicaPortString) {
    return BUILT_IN_PARAMETER_REPLICA_PORT;
  }
  if (parameter == kReplicaInstanceString) {
    return BUILT_IN_PARAMETER_REPLICA_INSTANCE;
  }
  return gutil::InvalidArgumentErrorBuilder()
         << "'" << parameter << "' is not a built-in paramter.";
}

}  // namespace pdpi
