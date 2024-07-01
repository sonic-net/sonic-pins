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
constexpr absl::string_view kBuiltInPrefix = "builtin::";
constexpr absl::string_view kMulticastGroupTableString =
    "multicast_group_table";
constexpr absl::string_view kMulticastGroupIdString = "multicast_group_id";
constexpr absl::string_view kMulticastReplicaPortString = "replica.port";
constexpr absl::string_view kMulticastReplicaInstanceString =
    "replica.instance";
}  // namespace

bool BuiltInTableHasField(IrBuiltInTable table, IrBuiltInField field) {
  switch (table) {
    case BUILT_IN_TABLE_MULTICAST_GROUP_TABLE: {
      return field == BUILT_IN_FIELD_MULTICAST_GROUP_ID ||
             field == BUILT_IN_FIELD_REPLICA_PORT ||
             field == BUILT_IN_FIELD_REPLICA_INSTANCE;
    }
    default: {
      return false;
    }
  }
}

bool IsBuiltInTable(absl::string_view table_name) {
  return StringToIrBuiltInTable(table_name).ok();
}

absl::StatusOr<std::string> IrBuiltInTableToString(IrBuiltInTable table) {
  switch (table) {
    case pdpi::BUILT_IN_TABLE_MULTICAST_GROUP_TABLE: {
      return absl::StrCat(kBuiltInPrefix, kMulticastGroupTableString);
    }
    default: {
      return gutil::InvalidArgumentErrorBuilder() << "Unknown built-in table.";
    }
  }
}

absl::StatusOr<IrBuiltInTable> StringToIrBuiltInTable(absl::string_view table) {
  if (table == absl::StrCat(kBuiltInPrefix, kMulticastGroupTableString)) {
    return pdpi::BUILT_IN_TABLE_MULTICAST_GROUP_TABLE;
  }
  return gutil::InvalidArgumentErrorBuilder()
         << "'" << table << "' is not a built-in table.";
}

absl::StatusOr<std::string> IrBuiltInFieldToString(IrBuiltInField field) {
  switch (field) {
    case BUILT_IN_FIELD_MULTICAST_GROUP_ID: {
      return std::string(kMulticastGroupIdString);
    }
    case BUILT_IN_FIELD_REPLICA_PORT: {
      return std::string(kMulticastReplicaPortString);
    }
    case BUILT_IN_FIELD_REPLICA_INSTANCE: {
      return std::string(kMulticastReplicaInstanceString);
    }
    default: {
      return gutil::InvalidArgumentErrorBuilder() << "Unknown built-in field.";
    }
  }
}

absl::StatusOr<IrBuiltInField> StringToIrBuiltInField(absl::string_view field) {
  if (field == kMulticastGroupIdString) {
    return BUILT_IN_FIELD_MULTICAST_GROUP_ID;
  }
  if (field == kMulticastReplicaPortString) {
    return BUILT_IN_FIELD_REPLICA_PORT;
  }
  if (field == kMulticastReplicaInstanceString) {
    return BUILT_IN_FIELD_REPLICA_INSTANCE;
  }
  return gutil::InvalidArgumentErrorBuilder()
         << "'" << field << "' is not a built-in field.";
}

}  // namespace pdpi
