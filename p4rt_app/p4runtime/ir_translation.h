// Copyright 2021 Google LLC
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
#ifndef GOOGLE_P4RT_APP_P4RUNTIME_IR_TRANSLATION_H_
#define GOOGLE_P4RT_APP_P4RUNTIME_IR_TRANSLATION_H_

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "boost/bimap.hpp"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"

namespace p4rt_app {

enum class TranslationDirection { kForController, kForOrchAgent };

struct TranslateTableEntryOptions {
  const TranslationDirection& direction;
  const pdpi::IrP4Info& ir_p4_info;
  bool translate_port_ids = false;

  // boost::bimap<SONiC port name, controller ID>;
  const boost::bimap<std::string, std::string>& port_map;
};

// Translates only a port string value.
absl::StatusOr<std::string> TranslatePort(
    TranslationDirection direction,
    const boost::bimap<std::string, std::string>& port_map,
    const std::string& port_key);

// Translates all the port fields, and VRF ID in a PDPI IrTableEntry. The
// library assumes all port names, and VRF IDs are encodded as strings. If not
// it will return an InvalidArgument error.
absl::Status TranslateTableEntry(const TranslateTableEntryOptions& options,
                                 pdpi::IrTableEntry& entry);

// Updates the IrP4Info so that the contents can be consumed by the OrchAgent.
// For example:
//  * OA expects UDF formats to be HEX_STRINGS
void TranslateIrP4InfoForOrchAgent(pdpi::IrP4Info& p4_info);

// TODO: Remove this when P4Info uses 64-bit IPv6 ACL match fields.
// Shifts left by 64 bits the IPv6 address of all ternary IPv6 match fields.
// If the IPv6 address is larger than 64 bits, does nothing.
void Convert64BitIpv6AclMatchFieldsTo128Bit(pdpi::IrTableEntry& ir_table_entry);

// Translates a PI table entry from the controller into an IR format with fields
// values consumable by the OA.
absl::StatusOr<pdpi::IrTableEntry> TranslatePiTableEntryForOrchAgent(
    const p4::v1::TableEntry& pi_table_entry, const pdpi::IrP4Info& ir_p4_info,
    bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    bool translate_key_only);

// Updates a IR table entry from the controller to an IR format with fields
// values consumable by the OA.
absl::Status UpdateIrTableEntryForOrchAgent(
    pdpi::IrTableEntry& ir_table_entry, const pdpi::IrP4Info& ir_p4_info,
    bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map);

}  // namespace p4rt_app

#endif  // GOOGLE_P4RT_APP_P4RUNTIME_IR_TRANSLATION_H_
