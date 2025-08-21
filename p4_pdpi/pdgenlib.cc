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

#include "p4_pdpi/pdgenlib.h"

#include <stdint.h>

#include <algorithm>
#include <string>
#include <vector>

#include "absl/container/flat_hash_set.h"
#include "absl/status/statusor.h"
#include "absl/strings/ascii.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_replace.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/strip.h"
#include "absl/strings/substitute.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/internal/ordered_map.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/pd.h"

using ::absl::StatusOr;
using ::gutil::InvalidArgumentErrorBuilder;
using ::p4::config::v1::MatchField;

namespace pdpi {

namespace {

std::string GetUnsupportedWarning(absl::string_view unsupported_entity) {
  return absl::StrCat("// CAUTION: This ", unsupported_entity,
                      " is not (yet) supported.\n");
}

// Returns a P4 object ID without the object tag.
uint32_t IdWithoutTag(uint32_t id) { return id & 0xffffff; }

// Returns a header comment.
std::string HeaderComment(const std::string& title) {
  std::string prefix = "// -- ";
  constexpr int kLineWidth = 80;
  std::string postfix(kLineWidth - prefix.size() - title.size() - 1, '-');
  return absl::StrCat("\n", prefix, title, " ", postfix, "\n");
}

// Returns a comment explaining the format of a match field or parameter, e.g.
// "Format::HEX_STRING / 10 bits".
std::string GetFormatComment(Format format, int32_t bitwidth) {
  std::string bitwidth_str = "";
  if (format == Format::HEX_STRING) {
    bitwidth_str = absl::StrCat(" / ", bitwidth, " bits");
  } else if (format == Format::IPV6) {
    bitwidth_str =
        absl::StrCat(" / ", bitwidth == 128 ? "" : "upper ", bitwidth, " bits");
  }
  return absl::StrCat("Format::", Format_Name(format), bitwidth_str);
}

// Returns the proto field for a match.
StatusOr<std::string> GetMatchFieldDeclaration(
    const IrMatchFieldDefinition& match) {
  std::string type;
  std::string match_kind;
  switch (match.match_field().match_type()) {
    case MatchField::TERNARY:
      type = "Ternary";
      match_kind = "ternary";
      break;
    case MatchField::EXACT:
      type = "string";
      match_kind = "exact";
      break;
    case MatchField::OPTIONAL:
      type = "Optional";
      match_kind = "optional";
      break;
    case MatchField::LPM:
      type = "Lpm";
      match_kind = "lpm";
      break;
    default:
      return InvalidArgumentErrorBuilder()
             << "Invalid match kind: " << match.DebugString();
  }

  ASSIGN_OR_RETURN(
      const std::string field_name,
      P4NameToProtobufFieldName(match.match_field().name(), kP4MatchField));

  std::string result;
  if (match.is_unsupported()) {
    absl::StrAppend(&result, GetUnsupportedWarning("match field"), "    ");
  }
  absl::StrAppend(
      &result, type, " ", field_name, " = ", match.match_field().id(), "; // ",
      match_kind, " match / ",
      GetFormatComment(match.format(), match.match_field().bitwidth()));
  return result;
}

// Returns the nested Match message for a given table.
StatusOr<std::string> GetTableMatchMessage(const IrTableDefinition& table) {
  std::string result = "";

  absl::StrAppend(&result, "  message Match {\n");
  std::vector<IrMatchFieldDefinition> match_fields;
  for (const auto& [id, match] : Ordered(table.match_fields_by_id())) {
    match_fields.push_back(match);
  }
  std::sort(match_fields.begin(), match_fields.end(),
            [](const IrMatchFieldDefinition& a,
               const IrMatchFieldDefinition& b) -> bool {
              return a.match_field().id() < b.match_field().id();
            });
  for (const auto& match : match_fields) {
    for (const auto& reference : match.references()) {
      absl::StrAppend(&result, "    // Refers to '", reference.table(), ".",
                      reference.match_field(), "'.\n");
    }
    ASSIGN_OR_RETURN(const auto& match_pd, GetMatchFieldDeclaration(match));
    absl::StrAppend(&result, "    ", match_pd, "\n");
  }
  absl::StrAppend(&result, "  }\n");

  return result;
}

// Returns the nested Action message for a given table.
StatusOr<std::string> GetTableActionMessage(const IrTableDefinition& table) {
  std::string result;

  absl::StrAppend(&result, "  message Action {\n");
  std::vector<IrActionReference> entry_actions;
  for (const auto& action : table.entry_actions()) {
    entry_actions.push_back(action);
  }
  std::sort(entry_actions.begin(), entry_actions.end(),
            [](const IrActionReference& a, const IrActionReference& b) -> bool {
              return a.action().preamble().id() < b.action().preamble().id();
            });
  if (entry_actions.size() > 1) {
    absl::StrAppend(&result, "  oneof action {\n");
  }
  absl::flat_hash_set<uint32_t> proto_ids;
  for (const auto& action : entry_actions) {
    const auto& name = action.action().preamble().alias();
    RETURN_IF_ERROR(gutil::InsertIfUnique(
        proto_ids, action.proto_id(),
        absl::StrCat("Proto IDs for entry actions must be unique, but table ",
                     name, " has duplicate ID ", action.proto_id())));
    ASSIGN_OR_RETURN(const std::string action_message_name,
                     P4NameToProtobufMessageName(name, kP4Action));
    ASSIGN_OR_RETURN(const std::string action_field_name,
                     P4NameToProtobufFieldName(name, kP4Action));
    if (action.action().is_unsupported()) {
      absl::StrAppend(&result, "    ", GetUnsupportedWarning("action"));
    }
    absl::StrAppend(&result, "    ", action_message_name, " ",
                    action_field_name, " = ", action.proto_id(), ";\n");
  }
  if (entry_actions.size() > 1) {
    absl::StrAppend(&result, "  }\n");
  }
  absl::StrAppend(&result, "  }\n");

  // If necessary, add WcmpAction message
  if (table.uses_oneshot()) {
    absl::StrAppend(&result, "  message WcmpAction {\n");
    absl::StrAppend(&result, "    Action action = 1;\n");
    absl::StrAppend(&result, "    int32 weight = 2;\n");
    absl::StrAppend(&result, "    string watch_port = 3;  // Format::STRING\n");
    absl::StrAppend(&result, "  }\n");
  }
  return result;
}

// Returns the contents of the @entry_restriction on the given table (if any).
absl::optional<std::string> GetConstraint(const IrTableDefinition& table) {
  std::string prefix = "@entry_restriction(\"";
  for (const auto& annotation : table.preamble().annotations()) {
    if (absl::StartsWith(annotation, prefix)) {
      return std::string(
          absl::StripSuffix(absl::StripPrefix(annotation, prefix), "\")"));
    }
  }
  return absl::nullopt;
}

// Returns the message for a given table.
StatusOr<std::string> GetTableMessage(const IrTableDefinition& table) {
  std::string result;

  if (table.is_unsupported()) {
    absl::StrAppend(&result, GetUnsupportedWarning("table"));
  }

  const absl::optional<std::string> constraint = GetConstraint(table);
  if (constraint.has_value()) {
    absl::StrAppend(&result, "// Table entry restrictions:");
    for (const auto& full_line : absl::StrSplit(constraint.value(), '\n')) {
      const auto& line = absl::StripAsciiWhitespace(full_line);
      if (line.empty()) continue;
      if (absl::StartsWith(line, "//")) {
        absl::StrAppend(&result, "\n// ",
                        absl::StrReplaceAll(line, {{"//", "##"}}));
      } else {
        absl::StrAppend(&result, "\n//   ", line);
      }
    }
    absl::StrAppend(&result, "\n");
  }
  const std::string& name = table.preamble().alias();
  ASSIGN_OR_RETURN(const std::string message_name,
                   P4NameToProtobufMessageName(name, kP4Table));
  absl::StrAppend(&result, "message ", message_name, " {\n");

  // Match message.
  ASSIGN_OR_RETURN(const auto& match_message, GetTableMatchMessage(table));
  absl::StrAppend(&result, match_message);
  absl::StrAppend(&result, "  Match match = 1;\n");

  // Action message.
  ASSIGN_OR_RETURN(const auto& action_message, GetTableActionMessage(table));
  absl::StrAppend(&result, action_message);
  if (table.uses_oneshot()) {
    absl::StrAppend(&result, "  repeated WcmpAction wcmp_actions = 2;\n");
  } else {
    absl::StrAppend(&result, "  Action action = 2;\n");
  }

  // Priority (if applicable).
  bool has_priority = false;
  for (const auto& [id, match] : Ordered(table.match_fields_by_id())) {
    const auto& kind = match.match_field().match_type();
    if (kind == MatchField::TERNARY || kind == MatchField::OPTIONAL ||
        kind == MatchField::RANGE) {
      has_priority = true;
    }
  }
  if (has_priority) {
    absl::StrAppend(&result, "  int32 priority = 3;\n");
  }

  // Meter (if applicable).
  if (table.has_meter()) {
    switch (table.meter().unit()) {
      case p4::config::v1::MeterSpec::BYTES:
        absl::StrAppend(&result, "  BytesMeterConfig meter_config = 4;\n");
        break;
      case p4::config::v1::MeterSpec::PACKETS:
        absl::StrAppend(&result, "  PacketsMeterConfig meter_config = 5;\n");
        break;
      default:
        return InvalidArgumentErrorBuilder()
               << "Unsupported meter: " << table.meter().DebugString();
    }
  }

  // Counter (if applicable).
  if (table.has_counter()) {
    switch (table.counter().unit()) {
      case p4::config::v1::CounterSpec::BYTES:
        absl::StrAppend(&result, "  BytesCounterData counter_data = 6;\n");
        break;
      case p4::config::v1::CounterSpec::PACKETS:
        absl::StrAppend(&result, "  PacketsCounterData counter_data = 6;\n");
        break;
      case p4::config::v1::CounterSpec::BOTH:
        absl::StrAppend(&result,
                        "  BytesAndPacketsCounterData counter_data = 6;\n");
        break;
      default:
        return InvalidArgumentErrorBuilder()
               << "Unsupported counter: " << table.counter().DebugString();
    }
  }

  // Meter counters (if applicable), we re-use the counter unit defintion
  // for meter counters as well.
  if (table.has_meter() && table.has_counter()) {
    switch (table.counter().unit()) {
      case p4::config::v1::CounterSpec::BYTES:
        absl::StrAppend(&result,
                        "  MeterBytesCounterData meter_counter_data = 9;\n");
        break;
      case p4::config::v1::CounterSpec::PACKETS:
        absl::StrAppend(&result,
                        "  MeterPacketsCounterData meter_counter_data = 9;\n");
        break;
      case p4::config::v1::CounterSpec::BOTH:
        absl::StrAppend(
            &result,
            "  MeterBytesAndPacketsCounterData meter_counter_data = 9;\n");
        break;
      default:
        return InvalidArgumentErrorBuilder() << "Unsupported meter counter: "
                                             << table.counter().DebugString();
    }
  }

  absl::StrAppend(&result, "  bytes controller_metadata = 8;\n");

  absl::StrAppend(&result, "}");
  return result;
}

// Returns the message for the given action.
StatusOr<std::string> GetActionMessage(const IrActionDefinition& action) {
  std::string result = "";

  if (action.is_unsupported()) {
    absl::StrAppend(&result, GetUnsupportedWarning("action"));
  }

  const std::string& name = action.preamble().alias();
  ASSIGN_OR_RETURN(const std::string message_name,
                   P4NameToProtobufMessageName(name, kP4Action));
  absl::StrAppend(&result, "message ", message_name, " {\n");

  // Sort parameters by ID
  std::vector<IrActionDefinition::IrActionParamDefinition> params;
  for (const auto& [id, param] : Ordered(action.params_by_id())) {
    params.push_back(param);
  }
  std::sort(params.begin(), params.end(),
            [](const IrActionDefinition::IrActionParamDefinition& a,
               const IrActionDefinition::IrActionParamDefinition& b) -> bool {
              return a.param().id() < b.param().id();
            });

  // Field for every param.
  for (const auto& param : params) {
    ASSIGN_OR_RETURN(
        const std::string param_name,
        P4NameToProtobufFieldName(param.param().name(), kP4Parameter));
    for (const auto& reference : param.references()) {
      absl::StrAppend(&result, "  // Refers to '", reference.table(), ".",
                      reference.match_field(), "'.\n");
    }
    absl::StrAppend(
        &result, "  string ", param_name, " = ", param.param().id(), "; // ",
        GetFormatComment(param.format(), param.param().bitwidth()), "\n");
  }

  absl::StrAppend(&result, "}");
  return result;
}

StatusOr<std::string> GetPacketIoMessage(const IrP4Info& info) {
  std::string result = "";

  // Packet-in
  absl::StrAppend(&result, "message PacketIn {\n");
  absl::StrAppend(&result, "  bytes payload = 1;\n\n");
  absl::StrAppend(&result, "  message Metadata {\n");
  for (const auto& [name, meta] : Ordered(info.packet_in_metadata_by_name())) {
    // Skip PI-only padding.
    if (meta.is_padding()) continue;
    ASSIGN_OR_RETURN(
        const std::string meta_name,
        P4NameToProtobufFieldName(meta.metadata().name(), kP4MetaField));
    absl::StrAppend(
        &result, "    string ", meta_name, " = ", meta.metadata().id(), "; // ",
        GetFormatComment(meta.format(), meta.metadata().bitwidth()), "\n");
  }
  absl::StrAppend(&result, "  }\n");
  absl::StrAppend(&result, "  Metadata metadata = 2;\n");
  absl::StrAppend(&result, "}\n");

  // Packet-out
  absl::StrAppend(&result, "message PacketOut {\n");
  absl::StrAppend(&result, "  bytes payload = 1;\n\n");
  absl::StrAppend(&result, "  message Metadata {\n");
  for (const auto& [name, meta] : Ordered(info.packet_out_metadata_by_name())) {
    // Skip PI-only padding.
    if (meta.is_padding()) continue;
    ASSIGN_OR_RETURN(
        const std::string meta_name,
        P4NameToProtobufFieldName(meta.metadata().name(), kP4MetaField));
    absl::StrAppend(
        &result, "    string ", meta_name, " = ", meta.metadata().id(), "; // ",
        GetFormatComment(meta.format(), meta.metadata().bitwidth()), "\n");
  }
  absl::StrAppend(&result, "  }\n");
  absl::StrAppend(&result, "  Metadata metadata = 2;\n");
  absl::StrAppend(&result, "}");

  return result;
}

bool IsActionUnused(const IrActionDefinition& action,
                    const std::vector<IrTableDefinition>& tables) {
  for (const auto& table : tables) {
    for (const auto& used_action : table.entry_actions()) {
      if (used_action.action().preamble().id() == action.preamble().id())
        return false;
    }
  }
  return true;
}

}  // namespace

StatusOr<std::string> IrP4InfoToPdProto(const IrP4Info& info,
                                        const PdGenOptions& options) {
  std::string result = "";

  // Header comment.
  absl::StrAppend(&result, R"(
// P4 PD proto

// NOTE: This file is automatically created from the P4 program using the pdgen
//       library in p4_pdpi. DO NOT modify it manually.

syntax = "proto3";
package )" + options.package + R"(;

import "p4/v1/p4runtime.proto";
import "google/rpc/code.proto";
import "google/rpc/status.proto";

// PDPI uses the following formats for different kinds of values:
// - Format::IPV4 for IPv4 addresses (32 bits), e.g., "10.0.0.1".
// - Format::IPV6 for IPv6 addresses (128 bits) formatted according to RFC 5952.
//   E.g. "2001:db8::1".
// - Format::MAC for MAC addresses (48 bits), e.g., "01:02:03:04:aa".
// - Format::STRING for entities that the controller refers to by string, e.g.,
//   ports.
// - Format::HEX_STRING for anything else, i.e. bitstrings of arbitrary length.
//   E.g., "0x01ab".

)");

  // General definitions.
  absl::StrAppend(&result, HeaderComment("General definitions"));
  absl::StrAppend(&result, R"(
// Ternary match. The value and mask are formatted according to the Format of the match field.
message Ternary {
  string value = 1;
  string mask = 2;
}

// LPM match. The value is formatted according to the Format of the match field.
message Lpm {
  string value = 1;
  int32 prefix_length = 2;
}

// Optional match. The value is formatted according to the Format of the match field.
message Optional {
  string value = 1;
}
)");

  // Filter by role and sort by ID.
  std::vector<IrTableDefinition> tables;
  for (const auto& [id, table] : Ordered(info.tables_by_id())) {
    if (absl::c_find(options.roles, table.role()) != options.roles.end()) {
      tables.push_back(table);
    }
  }
  std::sort(tables.begin(), tables.end(),
            [](const IrTableDefinition& a, const IrTableDefinition& b) {
              return a.preamble().id() < b.preamble().id();
            });
  if (tables.empty()) {
    return InvalidArgumentErrorBuilder() << "No tables, cannot generate PD";
  }

  // Sort actions by ID.
  std::vector<IrActionDefinition> actions;
  for (const auto& [id, action] : Ordered(info.actions_by_id())) {
    actions.push_back(action);
  }
  std::sort(actions.begin(), actions.end(),
            [](const IrActionDefinition& a, const IrActionDefinition& b) {
              return a.preamble().id() < b.preamble().id();
            });
  if (actions.empty()) {
    return InvalidArgumentErrorBuilder() << "No actions, cannot generate PD";
  }

  // Table messages.
  absl::StrAppend(&result, HeaderComment("Tables"), "\n");
  for (const auto& table : tables) {
    ASSIGN_OR_RETURN(const auto& table_pd, GetTableMessage(table));
    absl::StrAppend(&result, table_pd, "\n\n");
  }

  if (options.multicast_table_field_number.has_value()) {
    absl::StrAppend(&result, R"(
// Corresponds to `MulticastGroupEntry` in p4runtime.proto. This table is part
// of the v1model architecture and is not explicitly present in the P4 program.
message MulticastGroupTableEntry {
  message Match {
    string multicast_group_id = 1;  // exact match / Format::HEX_STRING / 16 bits
  }
  message Action {
    ReplicateAction replicate = 1;
  }
  Match match = 1;
  Action action = 2;
  bytes metadata = 3;
}

)");
  }

  // Action messages.
  absl::StrAppend(&result, HeaderComment("Actions"), "\n");
  for (const auto& action : actions) {
    if (IsActionUnused(action, tables)) continue;
    ASSIGN_OR_RETURN(const auto& action_pd, GetActionMessage(action));
    absl::StrAppend(&result, action_pd, "\n\n");
  }
  if (options.multicast_table_field_number.has_value()) {
    absl::StrAppend(&result, R"(
// This action is unique to `MulticastGroupTableEntry` and is not explicitly
// present in the P4 program.
message ReplicateAction {
  // All `Replica`s and `BackupReplica`s must have unique (port, instance)-pairs
  // within the scope of the `ReplicateAction` that contains them.
  repeated Replica replicas = 1;
  // Corresponds to `Replica` in p4runtime.proto.
  message Replica {
    // Refers to 'multicast_router_interface_table.multicast_replica_port'.
    string port = 1;      // Format::STRING
    // Refers to 'multicast_router_interface_table.multicast_replica_instance'.
    string instance = 2;  // Format::HEX_STRING / 16 bits
    repeated BackupReplica backup_replicas = 3;
  }
  // Corresponds to `BackupReplica` in p4runtime.proto.
  message BackupReplica {
    // Refers to 'multicast_router_interface_table.multicast_replica_port'.
    string port = 1;      // Format::STRING
    // Refers to 'multicast_router_interface_table.multicast_replica_instance'.
    string instance = 2;  // Format::HEX_STRING / 16 bits
  }
}

)");
  }

  // Overall TableEntry message.
  absl::StrAppend(&result, HeaderComment("All tables"), "\n");
  absl::StrAppend(&result, "message TableEntry {\n");
  absl::StrAppend(&result, "  oneof entry {\n");
  for (const auto& table : tables) {
    if (table.is_unsupported()) {
      absl::StrAppend(&result, "    ", GetUnsupportedWarning("table"));
    }
    const auto& name = table.preamble().alias();
    ASSIGN_OR_RETURN(const std::string table_message_name,
                     P4NameToProtobufMessageName(name, kP4Table));
    ASSIGN_OR_RETURN(const std::string table_field_name,
                     P4NameToProtobufFieldName(name, kP4Table));
    absl::StrAppend(&result, "    ", table_message_name, " ", table_field_name,
                    " = ", IdWithoutTag(table.preamble().id()), ";\n");
  }
  if (options.multicast_table_field_number.has_value()) {
    absl::StrAppend(
        &result,
        absl::Substitute(
            "    MulticastGroupTableEntry multicast_group_table_entry = $0;\n",
            *options.multicast_table_field_number));
  }
  absl::StrAppend(&result, "  }\n");
  absl::StrAppend(&result, "}\n\n");

  // TableEntries message (vector of TableEntry).
  absl::StrAppend(&result, "message TableEntries {\n");
  absl::StrAppend(&result, "  repeated TableEntry entries = 1;\n");
  absl::StrAppend(&result, "}\n\n");

  // PacketIo message.
  absl::StrAppend(&result, HeaderComment("Packet-IO"), "\n");
  ASSIGN_OR_RETURN(const auto& packetio_pd, GetPacketIoMessage(info));
  absl::StrAppend(&result, packetio_pd, "\n\n");

  // Meter messages.
  absl::StrAppend(&result, HeaderComment("Meter configs"));
  absl::StrAppend(&result, R"(
message BytesMeterConfig {
  // Committed/peak information rate (bytes per sec).
  int64 bytes_per_second = 1;
  // Committed/peak burst size.
  int64 burst_bytes = 2;
}

message PacketsMeterConfig {
  // Committed/peak information rate (packets per sec).
  int64 packets_per_second = 1;
  // Committed/peak burst size.
  int64 burst_packets = 2;
}
)");

  // Counter messages.
  absl::StrAppend(&result, HeaderComment("Counter data"));
  absl::StrAppend(&result, R"(
message BytesCounterData {
  // Number of bytes.
  int64 byte_count = 1;
}

message PacketsCounterData {
  // Number of packets.
  int64 packet_count = 1;
}

message BytesAndPacketsCounterData {
  // Number of bytes.
  int64 byte_count = 1;
  // Number of packets.
  int64 packet_count = 2;
}
)");

  // Meter Counter messages.
  absl::StrAppend(&result, HeaderComment("Meter counter data"));
  absl::StrAppend(&result, R"(
message MeterBytesCounterData {
  // Number of bytes per color.
  BytesCounterData green = 1;
  BytesCounterData yellow = 2;
  BytesCounterData red = 3;
}

message MeterPacketsCounterData {
  // Number of packets per color.
  PacketsCounterData green = 1;
  PacketsCounterData yellow = 2;
  PacketsCounterData red = 3;
}

message MeterBytesAndPacketsCounterData {
  // Number of bytes and packets per color.
  BytesAndPacketsCounterData green = 1;
  BytesAndPacketsCounterData yellow = 2;
  BytesAndPacketsCounterData red = 3;
}
)");

  // RPC messages.
  absl::StrAppend(&result, HeaderComment("RPC messages"));
  absl::StrAppend(&result, R"(
// Describes an update in a Write RPC request.
message Update {
  // Required.
  p4.v1.Update.Type type = 1;
  // Required.
  TableEntry table_entry = 2;
}

// Describes a Write RPC request.
message WriteRequest {
  // Required.
  uint64 device_id = 1;
  // Required.
  p4.v1.Uint128 election_id = 2;
  // Required.
  repeated Update updates = 3;
}

// Describes the status of a single update in a Write RPC.
message UpdateStatus {
  // Required.
  google.rpc.Code code = 1;
  // Required for non-OK status.
  string message = 2;
}

// Describes the result of a Write RPC.
message WriteRpcStatus {
  oneof status {
    google.rpc.Status rpc_wide_error = 1;
    WriteResponse rpc_response = 2;
  }
}

// Describes a Write RPC response.
message WriteResponse {
  // Same order as `updates` in `WriteRequest`.
  repeated UpdateStatus statuses = 1;
}

// Read requests.
message ReadRequest {
  // Required.
  uint64 device_id = 1;
  // Indicates if counter data should be read.
  bool read_counter_data = 2;
  // Indicates if meter configs should be read.
  bool read_meter_configs = 3;
}

// A read request response.
message ReadResponse {
  // The table entries read by the switch.
  repeated TableEntry table_entries = 1;
}

// A stream message request
message StreamMessageRequest {
  oneof update {
    p4.v1.MasterArbitrationUpdate arbitration = 1;
    PacketOut packet = 2;
  }
}

// A stream error message
message StreamError {
  google.rpc.Status status = 1;
  PacketOut packet_out = 2;
}

// A stream message response
message StreamMessageResponse {
  oneof update {
    p4.v1.MasterArbitrationUpdate arbitration = 1;
    PacketIn packet = 2;
    // Used by the server to asynchronously report errors which occur when
    // processing StreamMessageRequest messages.
    StreamError error = 3;
  }
}
)");

  return result;
}

}  // namespace pdpi
