/*
 * Copyright 2020 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#ifndef PINS_P4RT_APP_SONIC_APP_DB_TO_PDPI_IR_TRANSLATOR_H_
#define PINS_P4RT_APP_SONIC_APP_DB_TO_PDPI_IR_TRANSLATOR_H_

#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "swss/rediscommand.h"

namespace p4rt_app {
namespace sonic {

// Given a PDPI IrTableEntry will generate the SONiC AppDb key for a P4RT table.
absl::StatusOr<std::string>
IrTableEntryToAppDbKey(const pdpi::IrTableEntry &entry);

// Given a PDPI IrTableEntry will generate the SONiC AppDb field values for a
// P4RT table.
absl::StatusOr<std::vector<swss::FieldValueTuple>>
IrTableEntryToAppDbValues(const pdpi::IrTableEntry &entry);

// Given the SONiC AppDb key, and field values will generate a PDPI
// IrTableEntry.
absl::StatusOr<pdpi::IrTableEntry> AppDbKeyAndValuesToIrTableEntry(
    const pdpi::IrP4Info &ir_p4_info, absl::string_view app_db_key,
    const std::vector<std::pair<std::string, std::string>> &app_db_values);

// Given a PDPI IrMulticastGroupEntry, generate the SONiC AppDb key for
// packet replication in the P4RT table.
std::string
IrMulticastGroupEntryToAppDbKey(const pdpi::IrMulticastGroupEntry &entry);

} // namespace sonic
} // namespace p4rt_app

#endif // PINS_P4RT_APP_SONIC_APP_DB_TO_PDPI_IR_TRANSLATOR_H_
