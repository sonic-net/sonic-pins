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
#ifndef PINS_P4RT_APP_P4RUNTIME_IR_TRANSLATION_H_
#define PINS_P4RT_APP_P4RUNTIME_IR_TRANSLATION_H_

#include "absl/status/status.h"
#include "boost/bimap.hpp"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4rt_app/p4runtime/queue_translator.h"

namespace p4rt_app {

enum class TranslationDirection { kForController, kForOrchAgent };

struct TranslateTableEntryOptions {
  const TranslationDirection &direction;
  const pdpi::IrP4Info &ir_p4_info;
  bool translate_port_ids = false;

  // boost::bimap<SONiC port name, controller ID>;
  const boost::bimap<std::string, std::string> &port_map;
  const QueueTranslator& cpu_queue_translator;
  const QueueTranslator& front_panel_queue_translator;
};

// Translates only a port string value.
absl::StatusOr<std::string>
TranslatePort(TranslationDirection direction,
              const boost::bimap<std::string, std::string> &port_map,
              const std::string &port_key);

// Translates all the port fields, and VRF ID in a PDPI IrTableEntry. The
// library assumes all port names, and VRF IDs are encodded as strings. If not
// it will return an InvalidArgument error.
absl::Status TranslateTableEntry(const TranslateTableEntryOptions &options,
                                 pdpi::IrTableEntry &entry);

// Translates all the port fields in a PDPI IrPacketReplicationEngineEntry.
absl::Status
TranslatePacketReplicationEntry(const TranslateTableEntryOptions &options,
                                pdpi::IrPacketReplicationEngineEntry &entry);

// Updates the IrP4Info so that the contents can be consumed by the OrchAgent.
// For example:
//  * OA expects UDF formats to be HEX_STRINGS
void TranslateIrP4InfoForOrchAgent(pdpi::IrP4Info &p4_info);

// TODO: Remove this when P4Info uses 64-bit IPv6 ACL match fields.
// Shifts left by 64 bits the IPv6 address of all ternary IPv6 match fields.
// If the IPv6 address is larger than 64 bits, does nothing.
void Convert64BitIpv6AclMatchFieldsTo128Bit(pdpi::IrTableEntry &ir_table_entry);

// Translates a PI entity from the controller into an IR format with field
// values consumable by the OA.
absl::StatusOr<pdpi::IrEntity> TranslatePiEntityForOrchAgent(
    const p4::v1::Entity &pi_entity, const pdpi::IrP4Info &ir_p4_info,
    bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    const QueueTranslator& cpu_queue_translator,
    const QueueTranslator& front_panel_queue_translator,
    bool translate_key_only);

// Translates a PI table entry from the controller into an IR format with field
// values consumable by the OA.
absl::StatusOr<pdpi::IrTableEntry> TranslatePiTableEntryForOrchAgent(
    const p4::v1::TableEntry &pi_table_entry, const pdpi::IrP4Info &ir_p4_info,
    bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    const QueueTranslator& cpu_queue_translator,
    const QueueTranslator& front_panel_queue_translator,
    bool translate_key_only);

// Translates a PI packet replication engine entry from the controller into an
// IR format with field values consumable by the OA.
absl::StatusOr<pdpi::IrPacketReplicationEngineEntry>
TranslatePiPacketReplicationEngineEntryForOrchAgent(
    const p4::v1::PacketReplicationEngineEntry& pi_packet_replication_entry,
    const pdpi::IrP4Info& ir_p4_info, bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    const QueueTranslator& cpu_queue_translator,
    const QueueTranslator& front_panel_queue_translator,
    bool translate_key_only);

// Updates an IR entity from the controller to an IR format with field values
// consumable by the OA.
absl::Status UpdateIrEntityForOrchAgent(
    pdpi::IrEntity &ir_entity, const pdpi::IrP4Info &ir_p4_info,
    bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    const QueueTranslator& cpu_queue_translator,
    const QueueTranslator& front_panel_queue_translator);

// Updates a IR table entry from the controller to an IR format with field
// values consumable by the OA.
absl::Status UpdateIrTableEntryForOrchAgent(
    pdpi::IrTableEntry &ir_table_entry, const pdpi::IrP4Info &ir_p4_info,
    bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    const QueueTranslator& cpu_queue_translator,
    const QueueTranslator& front_panel_queue_translator);

// Updates a IR packet replication engine entry from the controller to an IR
// format with field values consumable by the OA.
absl::Status UpdateIrPacketReplicationEngineEntryForOrchAgent(
    pdpi::IrPacketReplicationEngineEntry& ir_packet_replication_entry,
    const pdpi::IrP4Info& ir_p4_info, bool translate_port_ids,
    const boost::bimap<std::string, std::string>& port_translation_map,
    const QueueTranslator& cpu_queue_translator,
    const QueueTranslator& front_panel_queue_translator);

} // namespace p4rt_app

#endif // PINS_P4RT_APP_P4RUNTIME_IR_TRANSLATION_H_
