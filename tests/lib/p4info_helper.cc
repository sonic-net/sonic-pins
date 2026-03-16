// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
#include "tests/lib/p4info_helper.h"

#include <memory>
#include <string>

#include "absl/status/statusor.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/status.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_runtime/p4_runtime_session.h"
#include "thinkit/switch.h"

namespace pins {

bool TableHasMatchField(const pdpi::IrP4Info& ir_p4info,
                        const std::string& table_name,
                        const std::string& field_name) {
  // Verify that the table exists.
  const pdpi::IrTableDefinition* table_def =
      gutil::FindOrNull(ir_p4info.tables_by_name(), table_name);
  if (table_def == nullptr) {
    VLOG(1) << "P4Info does not contain table: " << table_name;
    return false;
  }

  // Verify that the table definition has the required match field.
  const pdpi::IrMatchFieldDefinition* match_field_def =
      gutil::FindOrNull(table_def->match_fields_by_name(), field_name);
  if (match_field_def == nullptr) {
    VLOG(1) << "P4Info table '" << table_name
            << "' does not contain match field: " << field_name;
    return false;
  }

  return true;
}

absl::StatusOr<p4::config::v1::P4Info> GetP4InfoFromSUT(thinkit::Switch& sut) {
  ASSIGN_OR_RETURN(std::unique_ptr<p4_runtime::P4RuntimeSession> session,
                   p4_runtime::P4RuntimeSession::Create(sut));
  ASSIGN_OR_RETURN(p4::v1::GetForwardingPipelineConfigResponse response,
                   p4_runtime::GetForwardingPipelineConfig(session.get()));
  return response.config().p4info();
}

}  // namespace pins
