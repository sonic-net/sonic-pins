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

#include "p4_pdpi/pd.h"

#include <stdint.h>

#include <algorithm>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "absl/strings/strip.h"
#include "google/protobuf/descriptor.h"
#include "google/protobuf/map.h"
#include "google/protobuf/message.h"
#include "google/rpc/code.pb.h"
#include "google/rpc/status.pb.h"
#include "gutil/collections.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/internal/ordered_map.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/utils/ir.h"

namespace pdpi {

using ::google::protobuf::FieldDescriptor;
using ::gutil::InvalidArgumentErrorBuilder;
using ::p4::config::v1::MatchField;

namespace {

constexpr char kPdProtoAndP4InfoOutOfSync[] =
    "The PD proto and P4Info file are out of sync";

constexpr absl::string_view kTableMessageSuffix = "Entry";
constexpr absl::string_view kActionMessageSuffix = "Action";
constexpr absl::string_view kTableFieldSuffix = "_entry";

constexpr absl::string_view ProtoMessageSuffix(P4EntityKind entity_kind) {
  switch (entity_kind) {
    case kP4Table:
      return kTableMessageSuffix;
    case kP4Action:
      return kActionMessageSuffix;
    default:
      return absl::string_view();
  }
}

constexpr absl::string_view ProtoFieldSuffix(P4EntityKind entity_kind) {
  switch (entity_kind) {
    case kP4Table:
      return kTableFieldSuffix;
    case kP4Action:  // Intentionally no suffix.
    default:
      return absl::string_view();
  }
}

std::string SnakeCaseToPascalCase(absl::string_view input) {
  std::string output;
  for (unsigned i = 0; i < input.size(); i += 1) {
    if (input[i] == '_') {
      i += 1;
      if (i < input.size()) {
        absl::StrAppend(&output, std::string(1, std::toupper(input[i])));
      }
    } else if (i == 0) {
      absl::StrAppend(&output, std::string(1, std::toupper(input[i])));
    } else {
      absl::StrAppend(&output, std::string(1, input[i]));
    }
  }
  return output;
}

absl::StatusOr<std::string> ProtobufFieldNameToP4Name(
    absl::string_view proto_field_name, P4EntityKind entity_kind) {
  // TODO: validate the name is in snake case.
  if (absl::ConsumeSuffix(&proto_field_name, ProtoFieldSuffix(entity_kind))) {
    return std::string(proto_field_name);
  }
  return gutil::InvalidArgumentErrorBuilder()
         << "expected field name '" << proto_field_name << "' to end in suffix "
         << ProtoFieldSuffix(entity_kind);
}

absl::StatusOr<const google::protobuf::FieldDescriptor *> GetFieldDescriptor(
    const google::protobuf::Message &parent_message,
    const std::string &fieldname) {
  auto *parent_descriptor = parent_message.GetDescriptor();
  auto *field_descriptor = parent_descriptor->FindFieldByName(fieldname);
  if (field_descriptor == nullptr) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Field " << fieldname << " missing in "
           << parent_message.GetTypeName();
  }
  return field_descriptor;
}

absl::StatusOr<google::protobuf::Message *> GetMutableMessage(
    google::protobuf::Message *parent_message, const std::string &fieldname) {
  ASSIGN_OR_RETURN(auto *field_descriptor,
                   GetFieldDescriptor(*parent_message, fieldname));
  if (field_descriptor == nullptr) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Field " << fieldname << " missing in "
           << parent_message->GetTypeName() << ". "
           << kPdProtoAndP4InfoOutOfSync;
  }

  return parent_message->GetReflection()->MutableMessage(parent_message,
                                                         field_descriptor);
}

absl::StatusOr<const google::protobuf::Message *> GetMessageField(
    const google::protobuf::Message &parent_message,
    const std::string &fieldname) {
  ASSIGN_OR_RETURN(auto *field_descriptor,
                   GetFieldDescriptor(parent_message, fieldname));
  if (field_descriptor == nullptr) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Field " << fieldname << " missing in "
           << parent_message.GetTypeName() << ". "
           << kPdProtoAndP4InfoOutOfSync;
  }

  return &parent_message.GetReflection()->GetMessage(parent_message,
                                                     field_descriptor);
}

absl::StatusOr<bool> HasField(const google::protobuf::Message &parent_message,
                              const std::string &fieldname) {
  ASSIGN_OR_RETURN(auto *field_descriptor,
                   GetFieldDescriptor(parent_message, fieldname));
  if (field_descriptor == nullptr) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Field " << fieldname << " missing in "
           << parent_message.GetTypeName() << ". "
           << kPdProtoAndP4InfoOutOfSync;
  }

  return parent_message.GetReflection()->HasField(parent_message,
                                                  field_descriptor);
}

// Looks up repeated field of the given name in the given message using
// reflection, and returns non-null pointer to the element of the given index.
absl::StatusOr<const google::protobuf::Message *> GetRepeatedFieldMessage(
    const google::protobuf::Message &parent_message,
    const std::string &fieldname, int index) {
  ASSIGN_OR_RETURN(auto *field_descriptor,
                   GetFieldDescriptor(parent_message, fieldname));
  if (field_descriptor == nullptr) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Field " << fieldname << " missing in "
           << parent_message.GetTypeName() << ". "
           << kPdProtoAndP4InfoOutOfSync;
  }
  if (!field_descriptor->is_repeated()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "field '" << fieldname << "' in '" << parent_message.GetTypeName()
           << "' is not a repeated field";
  }
  int repeated_field_length = parent_message.GetReflection()->FieldSize(
      parent_message, field_descriptor);
  if (index >= repeated_field_length) {
    return gutil::OutOfRangeErrorBuilder()
           << "Index out of repeated field's bound. field's length: "
           << repeated_field_length << "index: " << index;
  }
  return &parent_message.GetReflection()->GetRepeatedMessage(
      parent_message, field_descriptor, index);
}

// Looks up repeated field of the given name in the given message using
// reflection, and returns vector of non-null pointers to the repeated field
// elements.
absl::StatusOr<std::vector<const google::protobuf::Message *>>
GetRepeatedFieldMessages(const google::protobuf::Message &parent_message,
                         const std::string &fieldname) {
  ASSIGN_OR_RETURN(auto *field_descriptor,
                   GetFieldDescriptor(parent_message, fieldname));
  if (field_descriptor == nullptr) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Field " << fieldname << " missing in "
           << parent_message.GetTypeName() << ". "
           << kPdProtoAndP4InfoOutOfSync;
  }
  if (!field_descriptor->is_repeated()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "field '" << fieldname << "' in '" << parent_message.GetTypeName()
           << "' is not a repeated field";
  }

  int size = parent_message.GetReflection()->FieldSize(parent_message,
                                                       field_descriptor);
  std::vector<const google::protobuf::Message *> result;
  result.reserve(size);
  for (int i = 0; i < size; ++i) {
    result.push_back(&parent_message.GetReflection()->GetRepeatedMessage(
        parent_message, field_descriptor, i));
  }
  return result;
}

absl::StatusOr<google::protobuf::Message *> AddRepeatedMutableMessage(
    google::protobuf::Message *parent_message, const std::string &fieldname) {
  ASSIGN_OR_RETURN(auto *field_descriptor,
                   GetFieldDescriptor(*parent_message, fieldname));
  if (field_descriptor == nullptr) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Field " << fieldname << " missing in "
           << parent_message->GetTypeName() << ". "
           << kPdProtoAndP4InfoOutOfSync;
  }
  return parent_message->GetReflection()->AddMessage(parent_message,
                                                     field_descriptor);
}

absl::Status ValidateFieldDescriptorType(const FieldDescriptor *descriptor,
                                         FieldDescriptor::Type expected_type) {
  if (expected_type != descriptor->type()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Expected field \"" << descriptor->name() << "\" to be of type \""
           << FieldDescriptor::TypeName(expected_type) << "\", but got \""
           << FieldDescriptor::TypeName(descriptor->type()) << "\" instead";
  }
  return absl::OkStatus();
}

absl::StatusOr<bool> GetBoolField(const google::protobuf::Message &message,
                                  const std::string &fieldname) {
  ASSIGN_OR_RETURN(auto *field_descriptor,
                   GetFieldDescriptor(message, fieldname));
  RETURN_IF_ERROR(ValidateFieldDescriptorType(field_descriptor,
                                              FieldDescriptor::TYPE_BOOL));
  return message.GetReflection()->GetBool(message, field_descriptor);
}

absl::StatusOr<int32_t> GetInt32Field(const google::protobuf::Message &message,
                                      const std::string &fieldname) {
  ASSIGN_OR_RETURN(auto *field_descriptor,
                   GetFieldDescriptor(message, fieldname));
  RETURN_IF_ERROR(ValidateFieldDescriptorType(field_descriptor,
                                              FieldDescriptor::TYPE_INT32));
  return message.GetReflection()->GetInt32(message, field_descriptor);
}

absl::StatusOr<int64_t> GetInt64Field(const google::protobuf::Message &message,
                                      const std::string &fieldname) {
  ASSIGN_OR_RETURN(auto *field_descriptor,
                   GetFieldDescriptor(message, fieldname));
  RETURN_IF_ERROR(ValidateFieldDescriptorType(field_descriptor,
                                              FieldDescriptor::TYPE_INT64));
  return message.GetReflection()->GetInt64(message, field_descriptor);
}

absl::StatusOr<uint64_t> GetUint64Field(
    const google::protobuf::Message &message, const std::string &fieldname) {
  ASSIGN_OR_RETURN(auto *field_descriptor,
                   GetFieldDescriptor(message, fieldname));
  RETURN_IF_ERROR(ValidateFieldDescriptorType(field_descriptor,
                                              FieldDescriptor::TYPE_UINT64));
  return message.GetReflection()->GetUInt64(message, field_descriptor);
}

absl::StatusOr<std::string> GetStringField(
    const google::protobuf::Message &message, const std::string &fieldname) {
  ASSIGN_OR_RETURN(auto *field_descriptor,
                   GetFieldDescriptor(message, fieldname));
  RETURN_IF_ERROR(ValidateFieldDescriptorType(field_descriptor,
                                              FieldDescriptor::TYPE_STRING));
  return message.GetReflection()->GetString(message, field_descriptor);
}

absl::StatusOr<std::string> GetBytesField(
    const google::protobuf::Message &message, const std::string &fieldname) {
  ASSIGN_OR_RETURN(auto *field_descriptor,
                   GetFieldDescriptor(message, fieldname));
  RETURN_IF_ERROR(ValidateFieldDescriptorType(field_descriptor,
                                              FieldDescriptor::TYPE_BYTES));
  return message.GetReflection()->GetString(message, field_descriptor);
}

absl::Status SetBoolField(google::protobuf::Message *message,
                          const std::string &fieldname, bool value) {
  ASSIGN_OR_RETURN(auto *field_descriptor,
                   GetFieldDescriptor(*message, fieldname));
  RETURN_IF_ERROR(ValidateFieldDescriptorType(field_descriptor,
                                              FieldDescriptor::TYPE_BOOL));
  message->GetReflection()->SetBool(message, field_descriptor, value);
  return absl::OkStatus();
}

absl::Status SetInt32Field(google::protobuf::Message *message,
                           const std::string &fieldname, int32_t value) {
  ASSIGN_OR_RETURN(auto *field_descriptor,
                   GetFieldDescriptor(*message, fieldname));
  RETURN_IF_ERROR(ValidateFieldDescriptorType(field_descriptor,
                                              FieldDescriptor::TYPE_INT32));
  message->GetReflection()->SetInt32(message, field_descriptor, value);
  return absl::OkStatus();
}

absl::Status SetInt64Field(google::protobuf::Message *message,
                           const std::string &fieldname, int64_t value) {
  ASSIGN_OR_RETURN(auto *field_descriptor,
                   GetFieldDescriptor(*message, fieldname));
  RETURN_IF_ERROR(ValidateFieldDescriptorType(field_descriptor,
                                              FieldDescriptor::TYPE_INT64));
  message->GetReflection()->SetInt64(message, field_descriptor, value);
  return absl::OkStatus();
}

absl::Status SetUint64Field(google::protobuf::Message *message,
                            const std::string &fieldname, uint64_t value) {
  ASSIGN_OR_RETURN(auto *field_descriptor,
                   GetFieldDescriptor(*message, fieldname));
  RETURN_IF_ERROR(ValidateFieldDescriptorType(field_descriptor,
                                              FieldDescriptor::TYPE_UINT64));
  message->GetReflection()->SetUInt64(message, field_descriptor, value);
  return absl::OkStatus();
}

absl::Status SetStringField(google::protobuf::Message *message,
                            const std::string &fieldname, std::string value) {
  ASSIGN_OR_RETURN(auto *field_descriptor,
                   GetFieldDescriptor(*message, fieldname));
  RETURN_IF_ERROR(ValidateFieldDescriptorType(field_descriptor,
                                              FieldDescriptor::TYPE_STRING));
  message->GetReflection()->SetString(message, field_descriptor, value);
  return absl::OkStatus();
}

absl::Status SetBytesField(google::protobuf::Message *message,
                           const std::string &fieldname, std::string value) {
  ASSIGN_OR_RETURN(auto *field_descriptor,
                   GetFieldDescriptor(*message, fieldname));
  RETURN_IF_ERROR(ValidateFieldDescriptorType(field_descriptor,
                                              FieldDescriptor::TYPE_BYTES));
  message->GetReflection()->SetString(message, field_descriptor, value);
  return absl::OkStatus();
}

absl::Status ClearField(google::protobuf::Message *message,
                        const std::string &fieldname) {
  ASSIGN_OR_RETURN(auto *field_descriptor,
                   GetFieldDescriptor(*message, fieldname));
  message->GetReflection()->ClearField(message, field_descriptor);
  return absl::OkStatus();
}

std::vector<std::string> GetAllFieldNames(
    const google::protobuf::Message &message) {
  std::vector<const FieldDescriptor *> fields;
  message.GetReflection()->ListFields(message, &fields);
  std::vector<std::string> field_names;
  field_names.reserve(fields.size());
  for (const auto *field : fields) {
    field_names.push_back(field->name());
  }
  return field_names;
}

absl::Status AddIrMeterCounterDataToPdEntry(
    const IrTableEntry &ir, const IrTableDefinition &ir_table_info,
    google::protobuf::Message &pd_table) {
  if (!ir_table_info.has_counter()) {
    return absl::InvalidArgumentError(
        absl::StrCat(kNewBullet,
                     "Table has no counter support but IR table entry has "
                     "a meter counter."));
  }

  const auto &pd_meter_counter_data =
      GetMutableMessage(&pd_table, "meter_counter_data");
  if (!pd_meter_counter_data.ok()) {
    return absl::InvalidArgumentError(
        absl::StrCat(kNewBullet, pd_meter_counter_data.status().message()));
  }

  std::vector<std::string> invalid_reasons;
  absl::flat_hash_map<std::string, const p4::v1::CounterData>
      ir_meter_colors_to_color_counter_data = {
          {"green", ir.meter_counter_data().green()},
          {"yellow", ir.meter_counter_data().yellow()},
          {"red", ir.meter_counter_data().red()},
      };
  for (const auto &[color, ir_color_counter_data] :
       ir_meter_colors_to_color_counter_data) {
    const absl::StatusOr<google::protobuf::Message *> &pd_color_counter_data =
        GetMutableMessage(*pd_meter_counter_data, color);
    if (!pd_color_counter_data.ok()) {
      invalid_reasons.push_back(absl::StrCat(
          kNewBullet, color, pd_color_counter_data.status().message()));
      continue;
    }
    // Use the same unit as counter data for meter counter data.
    switch (ir_table_info.counter().unit()) {
      case p4::config::v1::CounterSpec_Unit_BYTES: {
        absl::Status byte_count_status =
            SetInt64Field(*pd_color_counter_data, "byte_count",
                          ir_color_counter_data.byte_count());
        if (!byte_count_status.ok()) {
          invalid_reasons.push_back(
              absl::StrCat(kNewBullet, color, byte_count_status.message()));
        }
        break;
      }
      case p4::config::v1::CounterSpec_Unit_PACKETS: {
        absl::Status packet_count_status =
            SetInt64Field(*pd_color_counter_data, "packet_count",
                          ir_color_counter_data.packet_count());
        if (!packet_count_status.ok()) {
          invalid_reasons.push_back(
              absl::StrCat(kNewBullet, color, packet_count_status.message()));
        }
        break;
      }
      case p4::config::v1::CounterSpec_Unit_BOTH: {
        absl::Status byte_count_status =
            SetInt64Field(*pd_color_counter_data, "byte_count",
                          ir_color_counter_data.byte_count());
        if (!byte_count_status.ok()) {
          invalid_reasons.push_back(
              absl::StrCat(kNewBullet, color, byte_count_status.message()));
        }
        const auto &packet_count_status =
            SetInt64Field(*pd_color_counter_data, "packet_count",
                          ir_color_counter_data.packet_count());
        if (!packet_count_status.ok()) {
          invalid_reasons.push_back(
              absl::StrCat(kNewBullet, color, packet_count_status.message()));
        }
        break;
      }
      default:
        invalid_reasons.push_back(absl::StrCat(
            kNewBullet,
            "Invalid meter counter unit: ", ir_table_info.counter().unit()));
    }
  }

  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(absl::StrJoin(invalid_reasons, "\n  "));
  }
  return absl::OkStatus();
}

absl::Status AddPdMeterCounterDataToIrEntry(
    const google::protobuf::Message &pd_table,
    const IrTableDefinition &ir_table_info, IrTableEntry &ir) {
  // First check if "meter_counter_data" field exists and then get the
  // field value.
  std::vector<std::string> invalid_reasons;
  const absl::StatusOr<bool> &pd_has_meter_counter_data =
      HasField(pd_table, "meter_counter_data");
  if (!pd_has_meter_counter_data.ok()) {
    invalid_reasons.push_back(
        absl::StrCat(kNewBullet, pd_has_meter_counter_data.status().message()));
  } else if (*pd_has_meter_counter_data) {
    const absl::StatusOr<const google::protobuf::Message *> &
        pd_meter_counter_data = GetMessageField(pd_table, "meter_counter_data");
    if (!pd_meter_counter_data.ok()) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet, pd_meter_counter_data.status().message()));
    } else {
      absl::btree_map<std::string, p4::v1::CounterData *>
          colors_to_ir_meter_color_counter_data = {
              {"green", ir.mutable_meter_counter_data()->mutable_green()},
              {"yellow", ir.mutable_meter_counter_data()->mutable_yellow()},
              {"red", ir.mutable_meter_counter_data()->mutable_red()},
          };
      for (const auto &[color, ir_meter_color_counter_data] :
           colors_to_ir_meter_color_counter_data) {
        const auto &color_counter_data =
            GetMessageField(**pd_meter_counter_data, color);
        if (!color_counter_data.ok()) {
          invalid_reasons.push_back(
              absl::StrCat(kNewBullet, color_counter_data.status().message()));
          continue;
        }
        switch (ir_table_info.counter().unit()) {
          case p4::config::v1::CounterSpec_Unit_BYTES: {
            const absl::StatusOr<int64_t> &pd_byte_counter =
                GetInt64Field(**color_counter_data, "byte_count");
            if (!pd_byte_counter.ok()) {
              invalid_reasons.push_back(
                  absl::StrCat(kNewBullet, pd_byte_counter.status().message()));
            } else {
              ir_meter_color_counter_data->set_byte_count(*pd_byte_counter);
            }
            break;
          }
          case p4::config::v1::CounterSpec_Unit_PACKETS: {
            const absl::StatusOr<int64_t> &pd_packet_counter =
                GetInt64Field(**color_counter_data, "packet_count");
            if (!pd_packet_counter.ok()) {
              invalid_reasons.push_back(absl::StrCat(
                  kNewBullet, pd_packet_counter.status().message()));
            } else {
              ir_meter_color_counter_data->set_packet_count(*pd_packet_counter);
            }
            break;
          }
          case p4::config::v1::CounterSpec_Unit_BOTH: {
            const absl::StatusOr<int64_t> &pd_byte_counter =
                GetInt64Field(**color_counter_data, "byte_count");
            if (!pd_byte_counter.ok()) {
              invalid_reasons.push_back(
                  absl::StrCat(kNewBullet, pd_byte_counter.status().message()));
            } else {
              ir_meter_color_counter_data->set_byte_count(*pd_byte_counter);
            }
            const absl::StatusOr<int64_t> &pd_packet_counter =
                GetInt64Field(**color_counter_data, "packet_count");
            if (!pd_packet_counter.ok()) {
              invalid_reasons.push_back(absl::StrCat(
                  kNewBullet, pd_packet_counter.status().message()));
            } else {
              ir_meter_color_counter_data->set_packet_count(*pd_packet_counter);
            }
            break;
          }
          default:
            invalid_reasons.push_back(absl::StrCat(
                kNewBullet,
                "Invalid counter unit: ", ir_table_info.meter().unit()));
        }
      }
    }
  }
  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(absl::StrJoin(invalid_reasons, "\n  "));
  }
  return absl::OkStatus();
}

}  // namespace

absl::StatusOr<std::string> P4NameToProtobufMessageName(
    absl::string_view p4_name, P4EntityKind entity_kind) {
  // TODO: validate the name is in snake case.
  const absl::string_view suffix = ProtoMessageSuffix(entity_kind);
  // Append suffix, unless it is redundant.
  return absl::StrCat(absl::StripSuffix(SnakeCaseToPascalCase(p4_name), suffix),
                      suffix);
}

absl::StatusOr<std::string> P4NameToProtobufFieldName(
    absl::string_view p4_name, P4EntityKind entity_kind) {
  // TODO: validate the name is in snake case.
  return absl::StrCat(p4_name, ProtoFieldSuffix(entity_kind));
}

absl::Status PiTableEntryToPd(const IrP4Info &info,
                              const p4::v1::TableEntry &pi,
                              google::protobuf::Message *pd,
                              bool key_only /*=false*/) {
  ASSIGN_OR_RETURN(const auto ir_entry, PiTableEntryToIr(info, pi, key_only));
  return IrTableEntryToPd(info, ir_entry, pd, key_only);
}

absl::Status PiTableEntriesToPd(const IrP4Info &info,
                                const absl::Span<const p4::v1::TableEntry> &pi,
                                google::protobuf::Message *pd, bool key_only) {
  for (auto const &pi_entry : pi) {
    ASSIGN_OR_RETURN(google::protobuf::Message * pd_entry,
                     AddRepeatedMutableMessage(pd, "entries"));
    RETURN_IF_ERROR(PiTableEntryToPd(info, pi_entry, pd_entry, key_only));
  }
  return absl::OkStatus();
}

absl::Status PiPacketInToPd(const IrP4Info &info,
                            const p4::v1::PacketIn &pi_packet,
                            google::protobuf::Message *pd_packet) {
  ASSIGN_OR_RETURN(const auto ir, PiPacketInToIr(info, pi_packet));
  return IrPacketInToPd(info, ir, pd_packet);
}

absl::Status PiPacketOutToPd(const IrP4Info &info,
                             const p4::v1::PacketOut &pi_packet,
                             google::protobuf::Message *pd_packet) {
  ASSIGN_OR_RETURN(const auto ir, PiPacketOutToIr(info, pi_packet));
  return IrPacketOutToPd(info, ir, pd_packet);
}

absl::Status PiReadRequestToPd(const IrP4Info &info,
                               const p4::v1::ReadRequest &pi,
                               google::protobuf::Message *pd) {
  ASSIGN_OR_RETURN(const auto ir_entry, PiReadRequestToIr(info, pi));
  return IrReadRequestToPd(info, ir_entry, pd);
}

absl::Status PiReadResponseToPd(const IrP4Info &info,
                                const p4::v1::ReadResponse &pi,
                                google::protobuf::Message *pd) {
  ASSIGN_OR_RETURN(const auto ir_entry, PiReadResponseToIr(info, pi));
  return IrReadResponseToPd(info, ir_entry, pd);
}

absl::Status PiUpdateToPd(const IrP4Info &info, const p4::v1::Update &pi,
                          google::protobuf::Message *pd) {
  ASSIGN_OR_RETURN(const auto ir_entry, PiUpdateToIr(info, pi));
  return IrUpdateToPd(info, ir_entry, pd);
}

absl::Status PiWriteRequestToPd(const IrP4Info &info,
                                const p4::v1::WriteRequest &pi,
                                google::protobuf::Message *pd) {
  ASSIGN_OR_RETURN(const auto ir_entry, PiWriteRequestToIr(info, pi));
  return IrWriteRequestToPd(info, ir_entry, pd);
}

absl::Status PiStreamMessageRequestToPd(const IrP4Info &info,
                                        const p4::v1::StreamMessageRequest &pi,
                                        google::protobuf::Message *pd) {
  ASSIGN_OR_RETURN(const auto ir, PiStreamMessageRequestToIr(info, pi));
  return IrStreamMessageRequestToPd(info, ir, pd);
}

absl::Status PiStreamMessageResponseToPd(
    const IrP4Info &info, const p4::v1::StreamMessageResponse &pi,
    google::protobuf::Message *pd) {
  ASSIGN_OR_RETURN(const auto ir, PiStreamMessageResponseToIr(info, pi));
  return IrStreamMessageResponseToPd(info, ir, pd);
}

absl::StatusOr<p4::v1::TableEntry> PdTableEntryToPi(
    const IrP4Info &info, const google::protobuf::Message &pd, bool key_only) {
  ASSIGN_OR_RETURN(const auto ir_entry, PdTableEntryToIr(info, pd, key_only));
  return IrTableEntryToPi(info, ir_entry, key_only);
}

absl::StatusOr<std::vector<p4::v1::TableEntry>> PdTableEntriesToPi(
    const IrP4Info &info, const google::protobuf::Message &pd, bool key_only) {
  ASSIGN_OR_RETURN(std::vector<const google::protobuf::Message *> pd_entries,
                   GetRepeatedFieldMessages(pd, "entries"));
  std::vector<p4::v1::TableEntry> pi_entries;
  pi_entries.reserve(pd_entries.size());
  for (auto *pd_entry : pd_entries) {
    ASSIGN_OR_RETURN(pi_entries.emplace_back(),
                     PdTableEntryToPi(info, *pd_entry));
  }
  return pi_entries;
}

absl::StatusOr<p4::v1::PacketIn> PdPacketInToPi(
    const IrP4Info &info, const google::protobuf::Message &packet) {
  ASSIGN_OR_RETURN(const auto ir, PdPacketInToIr(info, packet));
  return IrPacketInToPi(info, ir);
}

absl::StatusOr<p4::v1::PacketOut> PdPacketOutToPi(
    const IrP4Info &info, const google::protobuf::Message &packet) {
  ASSIGN_OR_RETURN(const auto ir, PdPacketOutToIr(info, packet));
  return IrPacketOutToPi(info, ir);
}

absl::StatusOr<p4::v1::ReadRequest> PdReadRequestToPi(
    const IrP4Info &info, const google::protobuf::Message &pd) {
  ASSIGN_OR_RETURN(const auto ir_entry, PdReadRequestToIr(info, pd));
  return IrReadRequestToPi(info, ir_entry);
}

absl::StatusOr<p4::v1::ReadResponse> PdReadResponseToPi(
    const IrP4Info &info, const google::protobuf::Message &pd) {
  ASSIGN_OR_RETURN(const auto ir_entry, PdReadResponseToIr(info, pd));
  return IrReadResponseToPi(info, ir_entry);
}

absl::StatusOr<p4::v1::Update> PdUpdateToPi(
    const IrP4Info &info, const google::protobuf::Message &pd) {
  ASSIGN_OR_RETURN(const auto ir_entry, PdUpdateToIr(info, pd));
  return IrUpdateToPi(info, ir_entry);
}

absl::StatusOr<p4::v1::WriteRequest> PdWriteRequestToPi(
    const IrP4Info &info, const google::protobuf::Message &pd) {
  ASSIGN_OR_RETURN(const auto ir_entry, PdWriteRequestToIr(info, pd));
  return IrWriteRequestToPi(info, ir_entry);
}

absl::StatusOr<p4::v1::StreamMessageRequest> PdStreamMessageRequestToPi(
    const IrP4Info &info,
    const google::protobuf::Message &stream_message_request) {
  ASSIGN_OR_RETURN(const auto ir,
                   PdStreamMessageRequestToIr(info, stream_message_request));
  return IrStreamMessageRequestToPi(info, ir);
}

absl::StatusOr<p4::v1::StreamMessageResponse> PdStreamMessageResponseToPi(
    const IrP4Info &info,
    const google::protobuf::Message &stream_message_response) {
  ASSIGN_OR_RETURN(const auto ir,
                   PdStreamMessageResponseToIr(info, stream_message_response));
  return IrStreamMessageResponseToPi(info, ir);
}

absl::Status GrpcStatusToPd(const grpc::Status &status,
                            int number_of_updates_in_write_request,
                            google::protobuf::Message *pd) {
  ASSIGN_OR_RETURN(
      const auto ir_write_rpc_status,
      GrpcStatusToIrWriteRpcStatus(status, number_of_updates_in_write_request));
  return IrWriteRpcStatusToPd(ir_write_rpc_status, pd);
}

absl::StatusOr<grpc::Status> PdWriteRpcStatusToGrpcStatus(
    const google::protobuf::Message &pd) {
  ASSIGN_OR_RETURN(const auto ir_write_rpc_status,
                   pdpi::PdWriteRpcStatusToIr(pd));
  return IrWriteRpcStatusToGrpcStatus(ir_write_rpc_status);
}

// Converts all IR matches to their PD form and stores them in the match field
// of the PD table entry.
static absl::Status IrMatchEntryToPd(const IrTableDefinition &ir_table_info,
                                     const IrTableEntry &ir_table_entry,
                                     google::protobuf::Message *pd_match) {
  std::vector<std::string> invalid_reasons;
  for (const auto &ir_match : ir_table_entry.matches()) {
    std::vector<std::string> invalid_match_reasons;
    const auto &status_or_ir_match_info = gutil::FindPtrOrStatus(
        ir_table_info.match_fields_by_name(), ir_match.name());
    if (!status_or_ir_match_info.ok()) {
      invalid_match_reasons.push_back(absl::StrCat(
          kNewBullet, "P4Info for table does not contain match with name '",
          ir_match.name(), "'."));
      continue;
    }
    const auto *ir_match_info = *status_or_ir_match_info;
    if (IsElementUnused((ir_match_info->match_field().annotations()))) {
      invalid_match_reasons.push_back(
          absl::StrCat(kNewBullet, "Match field has @unused annotation."));
    }

    switch (ir_match_info->match_field().match_type()) {
      case MatchField::EXACT: {
        const absl::StatusOr<std::string> &pd_value =
            IrValueToFormattedString(ir_match.exact(), ir_match_info->format());
        if (!pd_value.ok()) {
          invalid_match_reasons.push_back(
              absl::StrCat(kNewBullet, pd_value.status().message()));
          break;
        }
        const auto &status =
            SetStringField(pd_match, ir_match.name(), *pd_value);
        if (!status.ok()) {
          invalid_match_reasons.push_back(
              absl::StrCat(kNewBullet, status.message()));
          break;
        }
        break;
      }
      case MatchField::LPM: {
        const absl::StatusOr<google::protobuf::Message *> &pd_lpm =
            GetMutableMessage(pd_match, ir_match.name());
        if (!pd_lpm.ok()) {
          invalid_match_reasons.push_back(
              absl::StrCat(kNewBullet, pd_lpm.status().message()));
          break;
        }
        const absl::StatusOr<std::string> &pd_value = IrValueToFormattedString(
            ir_match.lpm().value(), ir_match_info->format());
        if (!pd_value.ok()) {
          invalid_match_reasons.push_back(
              absl::StrCat(kNewBullet, pd_value.status().message()));
          break;
        }
        const auto &value_status = SetStringField(*pd_lpm, "value", *pd_value);
        if (!value_status.ok()) {
          invalid_match_reasons.push_back(
              absl::StrCat(kNewBullet, value_status.message()));
          break;
        }
        const auto &prefix_length_status = SetInt32Field(
            *pd_lpm, "prefix_length", ir_match.lpm().prefix_length());
        if (!prefix_length_status.ok()) {
          invalid_match_reasons.push_back(
              absl::StrCat(kNewBullet, prefix_length_status.message()));
          break;
        }
        break;
      }
      case MatchField::TERNARY: {
        const absl::StatusOr<google::protobuf::Message *> &pd_ternary =
            GetMutableMessage(pd_match, ir_match.name());
        if (!pd_ternary.ok()) {
          invalid_match_reasons.push_back(
              absl::StrCat(kNewBullet, pd_ternary.status().message()));
          break;
        }
        const absl::StatusOr<std::string> &pd_value = IrValueToFormattedString(
            ir_match.ternary().value(), ir_match_info->format());
        if (!pd_value.ok()) {
          invalid_match_reasons.push_back(
              absl::StrCat(kNewBullet, pd_value.status().message()));
          break;
        }
        const auto &value_status =
            SetStringField(*pd_ternary, "value", *pd_value);
        if (!value_status.ok()) {
          invalid_match_reasons.push_back(
              absl::StrCat(kNewBullet, value_status.message()));
          break;
        }
        const absl::StatusOr<std::string> &pd_mask = IrValueToFormattedString(
            ir_match.ternary().mask(), ir_match_info->format());
        if (!pd_mask.ok()) {
          invalid_match_reasons.push_back(
              absl::StrCat(kNewBullet, pd_mask.status().message()));
          break;
        }
        const auto &mask_status = SetStringField(*pd_ternary, "mask", *pd_mask);
        if (!mask_status.ok()) {
          invalid_match_reasons.push_back(
              absl::StrCat(kNewBullet, mask_status.message()));
          break;
        }
        break;
      }
      case MatchField::OPTIONAL: {
        const absl::StatusOr<google::protobuf::Message *> &pd_optional =
            GetMutableMessage(pd_match, ir_match.name());
        if (!pd_optional.ok()) {
          invalid_match_reasons.push_back(
              absl::StrCat(kNewBullet, pd_optional.status().message()));
          break;
        }
        const absl::StatusOr<std::string> &pd_value = IrValueToFormattedString(
            ir_match.optional().value(), ir_match_info->format());
        if (!pd_value.ok()) {
          invalid_match_reasons.push_back(
              absl::StrCat(kNewBullet, pd_value.status().message()));
          break;
        }
        const auto &value_status =
            SetStringField(*pd_optional, "value", *pd_value);
        if (!value_status.ok()) {
          invalid_match_reasons.push_back(
              absl::StrCat(kNewBullet, value_status.message()));
          break;
        }
        break;
      }
      default:
        invalid_match_reasons.push_back(
            absl::StrCat(kNewBullet, "Unsupported match type '",
                         MatchField_MatchType_Name(
                             ir_match_info->match_field().match_type()),
                         "'."));
    }
    if (!invalid_match_reasons.empty()) {
      invalid_reasons.push_back(
          GenerateFormattedError(MatchFieldName(ir_match.name()),
                                 absl::StrJoin(invalid_match_reasons, "\n")));
    }
  }
  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(absl::StrJoin(invalid_reasons, "\n"));
  }
  return absl::OkStatus();
}

// Converts an IR action invocation to its PD form and stores it in the parent
// message.
static absl::Status IrActionInvocationToPd(
    const IrP4Info &ir_p4info, const IrActionInvocation &ir_action,
    google::protobuf::Message *parent_message) {
  absl::string_view action_name = ir_action.name();
  const auto &status_or_ir_action_info = gutil::FindPtrOrStatus(
      ir_p4info.actions_by_name(), std::string(action_name));
  if (!status_or_ir_action_info.ok()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        ActionName(action_name),
        absl::StrCat(kNewBullet, "It does not exist in the P4Info.")));
  }
  const auto *ir_action_info = *status_or_ir_action_info;
  const auto &pd_action_name =
      P4NameToProtobufFieldName(ir_action.name(), kP4Action);
  if (!pd_action_name.ok()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        ActionName(action_name),
        absl::StrCat(kNewBullet, pd_action_name.status().message())));
  }
  const auto &pd_action = GetMutableMessage(parent_message, *pd_action_name);
  if (!pd_action.ok()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        ActionName(action_name),
        absl::StrCat(kNewBullet, pd_action.status().message())));
  }
  std::vector<std::string> invalid_reasons;
  if (IsElementUnused((ir_action_info->preamble().annotations()))) {
    invalid_reasons.push_back(
        absl::StrCat(kNewBullet, "Action has @unused annotation."));
  }

  for (const auto &ir_param : ir_action.params()) {
    const auto &status_or_param_info = gutil::FindPtrOrStatus(
        ir_action_info->params_by_name(), ir_param.name());
    absl::string_view param_name = ir_param.name();
    if (!status_or_param_info.ok()) {
      invalid_reasons.push_back(GenerateReason(
          ParamName(param_name), status_or_param_info.status().message()));
      continue;
    }
    const absl::StatusOr<std::string> &pd_value = IrValueToFormattedString(
        ir_param.value(), (*status_or_param_info)->format());
    if (!pd_value.ok()) {
      invalid_reasons.push_back(
          GenerateReason(ParamName(param_name), pd_value.status().message()));
      continue;
    }
    const auto &value_status =
        SetStringField(*pd_action, ir_param.name(), *pd_value);
    if (!value_status.ok()) {
      invalid_reasons.push_back(
          GenerateReason(ParamName(param_name), value_status.message()));
      continue;
    }
  }
  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        ActionName(action_name), absl::StrJoin(invalid_reasons, "\n")));
  }
  return absl::OkStatus();
}

// Converts an IR action set to its PD form and stores it in the
// PD table entry.
static absl::Status IrActionSetToPd(const IrP4Info &ir_p4info,
                                    const IrTableEntry &ir_table_entry,
                                    google::protobuf::Message *pd_table) {
  const auto &pd_wcmp_action_set_descriptor =
      GetFieldDescriptor(*pd_table, "wcmp_actions");
  if (!pd_wcmp_action_set_descriptor.ok()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        "ActionSet",
        absl::StrCat(kNewBullet,
                     pd_wcmp_action_set_descriptor.status().message())));
  }
  std::vector<std::string> invalid_reasons;
  for (const auto &ir_action_set_invocation :
       ir_table_entry.action_set().actions()) {
    auto *pd_wcmp_action_set = pd_table->GetReflection()->AddMessage(
        pd_table, *pd_wcmp_action_set_descriptor);
    const absl::StatusOr<google::protobuf::Message *> &pd_action_set =
        GetMutableMessage(pd_wcmp_action_set, "action");
    if (!pd_action_set.ok()) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet, pd_action_set.status().message()));
      continue;
    }
    const auto &action_status = IrActionInvocationToPd(
        ir_p4info, ir_action_set_invocation.action(), *pd_action_set);
    if (!action_status.ok()) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet, action_status.message()));
      continue;
    }
    const auto &weight_status = SetInt32Field(
        pd_wcmp_action_set, "weight", ir_action_set_invocation.weight());
    if (!weight_status.ok()) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet, weight_status.message()));
      continue;
    }
    const auto &watch_port_status =
        SetStringField(pd_wcmp_action_set, "watch_port",
                       ir_action_set_invocation.watch_port());
    if (!watch_port_status.ok()) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet, watch_port_status.message()));
      continue;
    }
  }
  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        "ActionSet", absl::StrJoin(invalid_reasons, "\n")));
  }
  return absl::OkStatus();
}

absl::Status IrTableEntryToPd(const IrP4Info &ir_p4info, const IrTableEntry &ir,
                              google::protobuf::Message *pd, bool key_only) {
  const auto &status_or_ir_table_info =
      gutil::FindPtrOrStatus(ir_p4info.tables_by_name(), ir.table_name());
  if (!status_or_ir_table_info.ok()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        TableName(ir.table_name()),
        absl::StrCat(kNewBullet, "It does not exist in the P4Info.",
                     kPdProtoAndP4InfoOutOfSync)));
  }
  const auto *ir_table_info = *status_or_ir_table_info;
  const auto &pd_table_name =
      P4NameToProtobufFieldName(ir.table_name(), kP4Table);
  if (!pd_table_name.ok()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        TableName(ir.table_name()),
        absl::StrCat(kNewBullet, pd_table_name.status().message())));
  }
  const auto &status_or_pd_table = GetMutableMessage(pd, *pd_table_name);
  if (!status_or_pd_table.ok()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        TableName(ir.table_name()),
        absl::StrCat(kNewBullet, status_or_pd_table.status().message())));
  }

  auto *pd_table = *status_or_pd_table;

  std::vector<std::string> invalid_reasons;

  if (IsElementUnused((ir_table_info->preamble().annotations()))) {
    invalid_reasons.push_back(
        absl::StrCat(kNewBullet, "Table entry for table '", ir.table_name(),
                     "' has @unused annotation."));
  }

  const absl::StatusOr<google::protobuf::Message *> &pd_match =
      GetMutableMessage(pd_table, "match");
  if (!pd_match.ok()) {
    invalid_reasons.push_back(
        absl::StrCat(kNewBullet, pd_match.status().message()));
  } else {
    const auto &match_status = IrMatchEntryToPd(*ir_table_info, ir, *pd_match);
    if (!match_status.ok()) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet, match_status.message()));
    }
  }

  if (ir.priority() != 0) {
    const auto &priority_status =
        SetInt32Field(pd_table, "priority", ir.priority());
    if (!priority_status.ok()) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet, priority_status.message()));
    }
  }
  if (!key_only) {
    const auto &metadata_status = SetBytesField(pd_table, "controller_metadata",
                                                ir.controller_metadata());
    if (!metadata_status.ok()) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet, metadata_status.message()));
    }

    if (ir_table_info->uses_oneshot()) {
      const auto &action_set_status = IrActionSetToPd(ir_p4info, ir, pd_table);
      if (!action_set_status.ok()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, action_set_status.message()));
      }
    } else if (ir.has_action()) {
      const absl::StatusOr<google::protobuf::Message *> &pd_action =
          GetMutableMessage(pd_table, "action");
      if (!pd_action.ok()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, pd_action.status().message()));
      } else {
        const auto &action_status =
            IrActionInvocationToPd(ir_p4info, ir.action(), *pd_action);
        if (!action_status.ok()) {
          invalid_reasons.push_back(
              absl::StrCat(kNewBullet, action_status.message()));
        }
      }
    }

    if (ir_table_info->has_meter() && ir.has_meter_config()) {
      const absl::StatusOr<google::protobuf::Message *> &config =
          GetMutableMessage(pd_table, "meter_config");
      if (!config.ok()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, config.status().message()));
      } else {
        const auto &ir_meter_config = ir.meter_config();
        if (ir_meter_config.cir() != ir_meter_config.pir()) {
          invalid_reasons.push_back(absl::StrCat(
              kNewBullet, "CIR and PIR values should be equal. Got CIR as ",
              ir_meter_config.cir(), ", PIR as ", ir_meter_config.pir(), "."));
        }
        if (ir_meter_config.cburst() != ir_meter_config.pburst()) {
          invalid_reasons.push_back(absl::StrCat(
              kNewBullet,
              "CBurst and PBurst values should be equal. Got CBurst as ",
              ir_meter_config.cburst(), ", PBurst as ",
              ir_meter_config.pburst(), "."));
        }
        switch (ir_table_info->meter().unit()) {
          case p4::config::v1::MeterSpec_Unit_BYTES: {
            const auto &bytes_per_second_status = SetInt64Field(
                *config, "bytes_per_second", ir_meter_config.cir());
            if (!bytes_per_second_status.ok()) {
              invalid_reasons.push_back(
                  absl::StrCat(kNewBullet, bytes_per_second_status.message()));
            }
            const auto &burst_bytes_status =
                SetInt64Field(*config, "burst_bytes", ir_meter_config.cburst());
            if (!burst_bytes_status.ok()) {
              invalid_reasons.push_back(
                  absl::StrCat(kNewBullet, burst_bytes_status.message()));
            }
            break;
          }
          case p4::config::v1::MeterSpec_Unit_PACKETS: {
            const auto &packets_per_second_status = SetInt64Field(
                *config, "packets_per_second", ir_meter_config.cir());
            if (!packets_per_second_status.ok()) {
              invalid_reasons.push_back(absl::StrCat(
                  kNewBullet, packets_per_second_status.message()));
            }
            const auto &burst_packets_status = SetInt64Field(
                *config, "burst_packets", ir_meter_config.cburst());
            if (!burst_packets_status.ok()) {
              invalid_reasons.push_back(
                  absl::StrCat(kNewBullet, burst_packets_status.message()));
            }
            break;
          }
          default:
            invalid_reasons.push_back(absl::StrCat(
                kNewBullet,
                "Invalid meter unit: ", ir_table_info->meter().unit()));
        }
      }

      // Take care of meter_counter_data for the 3 colors.
      if (ir.has_meter_counter_data()) {
        absl::Status status =
            AddIrMeterCounterDataToPdEntry(ir, *ir_table_info, *pd_table);
        if (!status.ok()) {
          invalid_reasons.push_back(std::string(status.message()));
        }
      }
    }

    if (ir_table_info->has_counter() && ir.has_counter_data()) {
      const absl::StatusOr<google::protobuf::Message *> &counter_data =
          GetMutableMessage(pd_table, "counter_data");
      if (!counter_data.ok()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, counter_data.status().message()));
      } else {
        switch (ir_table_info->counter().unit()) {
          case p4::config::v1::CounterSpec_Unit_BYTES: {
            const auto &byte_count_status = SetInt64Field(
                *counter_data, "byte_count", ir.counter_data().byte_count());
            if (!byte_count_status.ok()) {
              invalid_reasons.push_back(
                  absl::StrCat(kNewBullet, byte_count_status.message()));
            }
            break;
          }
          case p4::config::v1::CounterSpec_Unit_PACKETS: {
            const auto &packet_count_status =
                SetInt64Field(*counter_data, "packet_count",
                              ir.counter_data().packet_count());
            if (!packet_count_status.ok()) {
              invalid_reasons.push_back(
                  absl::StrCat(kNewBullet, packet_count_status.message()));
            }
            break;
          }
          case p4::config::v1::CounterSpec_Unit_BOTH: {
            const auto &byte_count_status = SetInt64Field(
                *counter_data, "byte_count", ir.counter_data().byte_count());
            if (!byte_count_status.ok()) {
              invalid_reasons.push_back(
                  absl::StrCat(kNewBullet, byte_count_status.message()));
            }
            const auto &packet_count_status =
                SetInt64Field(*counter_data, "packet_count",
                              ir.counter_data().packet_count());
            if (!packet_count_status.ok()) {
              invalid_reasons.push_back(
                  absl::StrCat(kNewBullet, packet_count_status.message()));
            }
            break;
          }
          default:
            invalid_reasons.push_back(absl::StrCat(
                kNewBullet,
                "Invalid counter unit: ", ir_table_info->counter().unit()));
        }
      }
    }
  }

  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        TableName(ir.table_name()), absl::StrJoin(invalid_reasons, "\n")));
  }
  return absl::OkStatus();
}

template <typename T>
absl::Status IrPacketIoToPd(const IrP4Info &info, const std::string &kind,
                            const T &packet,
                            google::protobuf::Message *pd_packet) {
  const std::string &packet_description = absl::StrCat("'", kind, "' message");
  const auto &field_descriptor = GetFieldDescriptor(*pd_packet, "payload");
  if (!field_descriptor.ok()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        packet_description,
        absl::StrCat(kNewBullet, field_descriptor.status().message())));
  }
  const auto &validate_status = ValidateFieldDescriptorType(
      *field_descriptor, FieldDescriptor::TYPE_BYTES);
  if (!validate_status.ok()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        packet_description,
        absl::StrCat(kNewBullet, validate_status.message())));
  }
  pd_packet->GetReflection()->SetString(pd_packet, *field_descriptor,
                                        packet.payload());

  google::protobuf::Map<std::string, IrPacketIoMetadataDefinition>
      metadata_by_name;
  if (kind == "packet-in") {
    metadata_by_name = info.packet_in_metadata_by_name();
  } else if (kind == "packet-out") {
    metadata_by_name = info.packet_out_metadata_by_name();
  } else {
    return absl::InvalidArgumentError(GenerateFormattedError(
        packet_description,
        absl::StrCat(kNewBullet, "Invalid PacketIo type.")));
  }

  std::vector<std::string> invalid_reasons;
  for (const auto &metadata : packet.metadata()) {
    const std::string &name = metadata.name();

    const auto &status_or_metadata_definition =
        gutil::FindPtrOrStatus(metadata_by_name, name);
    if (!status_or_metadata_definition.ok()) {
      invalid_reasons.push_back(absl::StrCat(kNewBullet, "Metadata with name '",
                                             name, "' not defined."));
      continue;
    }
    const absl::StatusOr<std::string> &raw_value = IrValueToFormattedString(
        metadata.value(), (*status_or_metadata_definition)->format());
    if (!raw_value.ok()) {
      invalid_reasons.push_back(
          GenerateReason(MetadataName(name), raw_value.status().message()));
      continue;
    }
    const absl::StatusOr<google::protobuf::Message *> &pd_metadata =
        GetMutableMessage(pd_packet, "metadata");
    if (!pd_metadata.ok()) {
      invalid_reasons.push_back(
          GenerateReason(MetadataName(name), pd_metadata.status().message()));
      continue;
    }
    const absl::Status &value_status =
        SetStringField(*pd_metadata, name, *raw_value);
    if (!value_status.ok()) {
      invalid_reasons.push_back(
          GenerateReason(MetadataName(name), value_status.message()));
      continue;
    }
  }
  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        packet_description, absl::StrJoin(invalid_reasons, "\n")));
  }
  return absl::OkStatus();
}

absl::Status IrPacketInToPd(const IrP4Info &info, const IrPacketIn &packet,
                            google::protobuf::Message *pd_packet) {
  return IrPacketIoToPd<IrPacketIn>(info, "packet-in", packet, pd_packet);
}
absl::Status IrPacketOutToPd(const IrP4Info &info, const IrPacketOut &packet,
                             google::protobuf::Message *pd_packet) {
  return IrPacketIoToPd<IrPacketOut>(info, "packet-out", packet, pd_packet);
}

absl::Status IrReadRequestToPd(const IrP4Info &info, const IrReadRequest &ir,
                               google::protobuf::Message *pd) {
  std::vector<std::string> invalid_reasons;
  if (ir.device_id() == 0) {
    invalid_reasons.push_back(absl::StrCat(kNewBullet, "Device ID missing."));
  }
  const auto &device_id_status =
      SetUint64Field(pd, "device_id", ir.device_id());
  if (!device_id_status.ok()) {
    invalid_reasons.push_back(
        absl::StrCat(kNewBullet, device_id_status.message()));
  }
  if (ir.read_counter_data()) {
    const auto &read_counter_status =
        SetBoolField(pd, "read_counter_data", ir.read_counter_data());
    if (!read_counter_status.ok()) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet, read_counter_status.message()));
    }
  }
  if (ir.read_meter_configs()) {
    const auto &read_meter_status =
        SetBoolField(pd, "read_meter_configs", ir.read_meter_configs());
    if (!read_meter_status.ok()) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet, read_meter_status.message()));
    }
  }
  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        "Read Request", absl::StrJoin(invalid_reasons, "\n")));
  }
  return absl::OkStatus();
}

absl::Status IrReadResponseToPd(const IrP4Info &info, const IrReadResponse &ir,
                                google::protobuf::Message *read_response) {
  std::vector<std::string> invalid_reasons;
  for (const auto &ir_table_entry : ir.table_entries()) {
    const absl::StatusOr<const FieldDescriptor *> &table_entries_descriptor =
        GetFieldDescriptor(*read_response, "table_entries");
    if (!table_entries_descriptor.ok()) {
      invalid_reasons.push_back(
          absl::StrCat(table_entries_descriptor.status().message()));
      continue;
    }
    const auto &table_entry_status =
        IrTableEntryToPd(info, ir_table_entry,
                         read_response->GetReflection()->AddMessage(
                             read_response, *table_entries_descriptor));
    if (!table_entry_status.ok()) {
      invalid_reasons.push_back(std::string(table_entry_status.message()));
      continue;
    }
  }
  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        "Read Response", absl::StrJoin(invalid_reasons, "\n")));
  }
  return absl::OkStatus();
}

absl::Status IrUpdateToPd(const IrP4Info &info, const IrUpdate &ir,
                          google::protobuf::Message *update) {
  ASSIGN_OR_RETURN(const auto *type_descriptor,
                   GetFieldDescriptor(*update, "type"));
  RETURN_IF_ERROR(
      ValidateFieldDescriptorType(type_descriptor, FieldDescriptor::TYPE_ENUM));
  update->GetReflection()->SetEnumValue(update, type_descriptor, ir.type());

  ASSIGN_OR_RETURN(auto *pd_table_entry,
                   GetMutableMessage(update, "table_entry"));
  RETURN_IF_ERROR(IrTableEntryToPd(info, ir.table_entry(), pd_table_entry));
  return absl::OkStatus();
}

absl::Status IrWriteRequestToPd(const IrP4Info &info, const IrWriteRequest &ir,
                                google::protobuf::Message *write_request) {
  RETURN_IF_ERROR(SetUint64Field(write_request, "device_id", ir.device_id()));
  if (ir.election_id().high() > 0 || ir.election_id().low() > 0) {
    ASSIGN_OR_RETURN(auto *election_id,
                     GetMutableMessage(write_request, "election_id"));
    RETURN_IF_ERROR(
        SetUint64Field(election_id, "high", ir.election_id().high()));
    RETURN_IF_ERROR(SetUint64Field(election_id, "low", ir.election_id().low()));
  }

  ASSIGN_OR_RETURN(const auto updates_descriptor,
                   GetFieldDescriptor(*write_request, "updates"));
  std::vector<std::string> invalid_reasons;
  for (int idx = 0; idx < ir.updates_size(); ++idx) {
    const auto &ir_update = ir.updates(idx);
    const auto &update_status =
        IrUpdateToPd(info, ir_update,
                     write_request->GetReflection()->AddMessage(
                         write_request, updates_descriptor));
    if (!update_status.ok()) {
      invalid_reasons.push_back(GenerateFormattedError(
          absl::StrCat("updates[", idx, "]"), update_status.message()));
      continue;
    }
  }
  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        "Write Request", absl::StrJoin(invalid_reasons, "\n")));
  }
  return absl::OkStatus();
}

static absl::Status IrArbitrationToPd(
    const p4::v1::MasterArbitrationUpdate &ir_arbitration,
    google::protobuf::Message *stream_message) {
  ASSIGN_OR_RETURN(auto *arbitration,
                   GetMutableMessage(stream_message, "arbitration"));

  RETURN_IF_ERROR(
      SetUint64Field(arbitration, "device_id", ir_arbitration.device_id()));

  ASSIGN_OR_RETURN(auto *election_id,
                   GetMutableMessage(arbitration, "election_id"));
  RETURN_IF_ERROR(
      SetUint64Field(election_id, "high", ir_arbitration.election_id().high()));
  RETURN_IF_ERROR(
      SetUint64Field(election_id, "low", ir_arbitration.election_id().low()));

  ASSIGN_OR_RETURN(auto *pd_status, GetMutableMessage(arbitration, "status"));
  RETURN_IF_ERROR(
      SetInt32Field(pd_status, "code", ir_arbitration.status().code()));
  RETURN_IF_ERROR(
      SetStringField(pd_status, "message", ir_arbitration.status().message()));
  return absl::OkStatus();
}

absl::Status IrStreamMessageRequestToPd(
    const IrP4Info &info, const IrStreamMessageRequest &ir,
    google::protobuf::Message *stream_message) {
  switch (ir.update_case()) {
    case IrStreamMessageRequest::kArbitration: {
      RETURN_IF_ERROR(IrArbitrationToPd(ir.arbitration(), stream_message));
      break;
    }
    case IrStreamMessageRequest::kPacket: {
      ASSIGN_OR_RETURN(auto *packet_out,
                       GetMutableMessage(stream_message, "packet"));
      RETURN_IF_ERROR(IrPacketOutToPd(info, ir.packet(), packet_out));
      break;
    }
    default:
      return absl::InvalidArgumentError(absl::StrCat(
          "Unsupported update: ",
          ir.GetDescriptor()->FindFieldByNumber(ir.update_case())->name(),
          "."));
  }
  return absl::OkStatus();
}

absl::Status IrStreamMessageResponseToPd(
    const IrP4Info &info, const IrStreamMessageResponse &ir,
    google::protobuf::Message *stream_message) {
  switch (ir.update_case()) {
    case IrStreamMessageResponse::kArbitration: {
      RETURN_IF_ERROR(IrArbitrationToPd(ir.arbitration(), stream_message));
      break;
    }
    case IrStreamMessageResponse::kPacket: {
      ASSIGN_OR_RETURN(auto *packet,
                       GetMutableMessage(stream_message, "packet"));
      RETURN_IF_ERROR(IrPacketInToPd(info, ir.packet(), packet));
      break;
    }
    case IrStreamMessageResponse::kError: {
      IrStreamError ir_error = ir.error();
      ASSIGN_OR_RETURN(auto *error, GetMutableMessage(stream_message, "error"));

      ASSIGN_OR_RETURN(auto *pd_status, GetMutableMessage(error, "status"));
      RETURN_IF_ERROR(
          SetInt32Field(pd_status, "code", ir_error.status().code()));

      RETURN_IF_ERROR(
          SetStringField(pd_status, "message", ir_error.status().message()));

      ASSIGN_OR_RETURN(auto *packet_out,
                       GetMutableMessage(error, "packet_out"));
      RETURN_IF_ERROR(
          IrPacketOutToPd(info, ir.error().packet_out(), packet_out));
      break;
    }
    default:
      return absl::InvalidArgumentError(absl::StrCat(
          "Unsupported update: ",
          ir.GetDescriptor()->FindFieldByNumber(ir.update_case())->name(),
          "."));
  }
  return absl::OkStatus();
}

static absl::Status IrUpdateStatusToPd(
    const IrUpdateStatus &ir_update_status,
    google::protobuf::Message *pd_update_status) {
  RETURN_IF_ERROR(
      SetEnumField(pd_update_status, "code", ir_update_status.code()));
  RETURN_IF_ERROR(
      SetStringField(pd_update_status, "message", ir_update_status.message()));
  return absl::OkStatus();
}

static absl::Status IrWriteResponseToPd(
    const IrWriteResponse &ir_write_response,
    google::protobuf::Message *pd_rpc_response) {
  // Iterates through each ir update status and add message to pd via
  // AddRepeatedMutableMessage
  std::vector<std::string> invalid_reasons;
  for (const IrUpdateStatus &ir_update_status : ir_write_response.statuses()) {
    const auto &pd_update =
        AddRepeatedMutableMessage(pd_rpc_response, "statuses");
    if (!pd_update.ok()) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet, pd_update.status().message()));
      continue;
    }
    const absl::Status &pd_update_status =
        IrUpdateStatusToPd(ir_update_status, *pd_update);
    if (!pd_update_status.ok()) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet, pd_update_status.message()));
      continue;
    }
  }
  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        "Write Response", absl::StrJoin(invalid_reasons, "\n")));
  }
  return absl::OkStatus();
}

absl::Status IrWriteRpcStatusToPd(const IrWriteRpcStatus &ir_write_status,
                                  google::protobuf::Message *pd) {
  switch (ir_write_status.status_case()) {
    case IrWriteRpcStatus::kRpcResponse: {
      ASSIGN_OR_RETURN(auto *pd_rpc_response,
                       GetMutableMessage(pd, "rpc_response"));
      return IrWriteResponseToPd(ir_write_status.rpc_response(),
                                 pd_rpc_response);
    }
    case IrWriteRpcStatus::kRpcWideError: {
      ASSIGN_OR_RETURN(auto *pd_rpc_wide_error,
                       GetMutableMessage(pd, "rpc_wide_error"));
      RETURN_IF_ERROR(SetInt32Field(pd_rpc_wide_error, "code",
                                    ir_write_status.rpc_wide_error().code()));
      RETURN_IF_ERROR(
          SetStringField(pd_rpc_wide_error, "message",
                         ir_write_status.rpc_wide_error().message()));
      break;
    }
    default:
      return absl::UnknownError("Unknown IrWriteRpcStatus case");
  }
  return absl::OkStatus();
}

// Converts all PD matches to their IR form and stores them in the matches
// field of ir_table_entry.
static absl::Status PdMatchEntryToIr(const IrTableDefinition &ir_table_info,
                                     const google::protobuf::Message &pd_match,
                                     IrTableEntry *ir_table_entry) {
  // Verify that there are no matches in PD that are not supported by the
  // P4Info provided. This could happen since if a P4Info that is a superset
  // of P4Infos for different roles is used to generate the PD, but a role
  // specific P4Info is passed in to PDPI.

  std::vector<std::pair<uint64_t, std::string>> matches;
  absl::flat_hash_set<std::string> match_set;
  for (const auto &[id, match_field] : ir_table_info.match_fields_by_id()) {
    matches.push_back({id, match_field.match_field().name()});
    match_set.insert(match_field.match_field().name());
  }

  std::vector<std::string> invalid_reasons;
  for (const auto &field : GetAllFieldNames(pd_match)) {
    if (!match_set.contains(field)) {
      invalid_reasons.push_back(GenerateFormattedError(
          MatchFieldName(field), "Match field does not exist in the P4Info."));
    }
  }
  std::sort(matches.begin(), matches.end());
  for (const auto &[_, pd_match_name] : matches) {
    std::vector<std::string> invalid_match_reasons;
    const auto &status_or_ir_match_info = gutil::FindPtrOrStatus(
        ir_table_info.match_fields_by_name(), pd_match_name);
    if (!status_or_ir_match_info.ok()) {
      return absl::InvalidArgumentError(GenerateFormattedError(
          MatchFieldName(pd_match_name),
          absl::StrCat(kNewBullet, "It does not exist in the P4Info.")));
    }
    const auto *ir_match_info = *status_or_ir_match_info;

    // Skip optional fields that are not present in pd_match. For exact
    // matches, this will automatically assume the default value (i.e. ""),
    // which allows for "" for Format::STRING fields.
    auto has_field = HasField(pd_match, pd_match_name);
    if (has_field.ok() && !*has_field &&
        ir_match_info->match_field().match_type() != MatchField::EXACT) {
      continue;
    }

    if (IsElementUnused(ir_match_info->match_field().annotations())) {
      invalid_match_reasons.push_back(
          absl::StrCat(kNewBullet, "Match field has @unused annotation."));
    }

    auto *ir_match = ir_table_entry->add_matches();
    ir_match->set_name(pd_match_name);
    switch (ir_match_info->match_field().match_type()) {
      case MatchField::EXACT: {
        const absl::StatusOr<std::string> &pd_value =
            GetStringField(pd_match, pd_match_name);
        if (!pd_value.ok()) {
          invalid_match_reasons.push_back(
              absl::StrCat(kNewBullet, pd_value.status().message()));
          break;
        }
        const absl::StatusOr<IrValue> &exact_match =
            FormattedStringToIrValue(*pd_value, ir_match_info->format());
        if (!exact_match.ok()) {
          invalid_match_reasons.push_back(
              absl::StrCat(kNewBullet, exact_match.status().message()));
          break;
        }
        *ir_match->mutable_exact() = *exact_match;
        break;
      }
      case MatchField::LPM: {
        auto *ir_lpm = ir_match->mutable_lpm();
        const auto &pd_lpm = GetMessageField(pd_match, pd_match_name);
        if (!pd_lpm.ok()) {
          invalid_match_reasons.push_back(
              absl::StrCat(kNewBullet, pd_lpm.status().message()));
          break;
        }

        const absl::StatusOr<std::string> &pd_value =
            GetStringField(**pd_lpm, "value");
        if (!pd_value.ok()) {
          invalid_match_reasons.push_back(
              absl::StrCat(kNewBullet, pd_value.status().message()));
          break;
        }
        const absl::StatusOr<IrValue> ir_value =
            FormattedStringToIrValue(*pd_value, ir_match_info->format());
        if (!ir_value.ok()) {
          invalid_match_reasons.push_back(
              absl::StrCat(kNewBullet, ir_value.status().message()));
          break;
        }
        *ir_lpm->mutable_value() = *ir_value;

        const absl::StatusOr<int32_t> &pd_prefix_len =
            GetInt32Field(**pd_lpm, "prefix_length");
        if (!pd_prefix_len.ok()) {
          invalid_match_reasons.push_back(
              absl::StrCat(kNewBullet, pd_prefix_len.status().message()));
          break;
        }
        if (*pd_prefix_len < 0 ||
            *pd_prefix_len > ir_match_info->match_field().bitwidth()) {
          invalid_match_reasons.push_back(
              absl::StrCat(kNewBullet, "Prefix length ", *pd_prefix_len,
                           " is out of bounds."));
          break;
        }
        ir_lpm->set_prefix_length(*pd_prefix_len);
        break;
      }
      case MatchField::TERNARY: {
        auto *ir_ternary = ir_match->mutable_ternary();
        const auto &pd_ternary = GetMessageField(pd_match, pd_match_name);
        if (!pd_ternary.ok()) {
          invalid_match_reasons.push_back(
              absl::StrCat(kNewBullet, pd_ternary.status().message()));
          break;
        }

        const absl::StatusOr<std::string> &pd_value =
            GetStringField(**pd_ternary, "value");
        if (!pd_value.ok()) {
          invalid_match_reasons.push_back(
              absl::StrCat(kNewBullet, pd_value.status().message()));
          break;
        }
        const absl::StatusOr<IrValue> &ir_value =
            FormattedStringToIrValue(*pd_value, ir_match_info->format());
        if (!ir_value.ok()) {
          invalid_match_reasons.push_back(
              absl::StrCat(kNewBullet, ir_value.status().message()));
          break;
        }
        *ir_ternary->mutable_value() = *ir_value;

        const absl::StatusOr<std::string> &pd_mask =
            GetStringField(**pd_ternary, "mask");
        if (!pd_mask.ok()) {
          invalid_match_reasons.push_back(
              absl::StrCat(kNewBullet, pd_mask.status().message()));
          break;
        }
        const absl::StatusOr<IrValue> &ir_mask =
            FormattedStringToIrValue(*pd_mask, ir_match_info->format());
        if (!ir_mask.ok()) {
          invalid_match_reasons.push_back(
              absl::StrCat(kNewBullet, ir_mask.status().message()));
          break;
        }
        *ir_ternary->mutable_mask() = *ir_mask;
        break;
      }
      case MatchField::OPTIONAL: {
        auto *ir_optional = ir_match->mutable_optional();
        const auto &pd_optional = GetMessageField(pd_match, pd_match_name);

        if (!pd_optional.ok()) {
          invalid_match_reasons.push_back(
              absl::StrCat(kNewBullet, pd_optional.status().message()));
          break;
        }

        const absl::StatusOr<std::string> &pd_value =
            GetStringField(**pd_optional, "value");
        if (!pd_value.ok()) {
          invalid_match_reasons.push_back(
              absl::StrCat(kNewBullet, pd_value.status().message()));
          break;
        }
        const absl::StatusOr<IrValue> ir_value =
            FormattedStringToIrValue(*pd_value, ir_match_info->format());
        if (!ir_value.ok()) {
          invalid_match_reasons.push_back(
              absl::StrCat(kNewBullet, ir_value.status().message()));
          break;
        }
        *ir_optional->mutable_value() = *ir_value;
        break;
      }
      default:
        invalid_match_reasons.push_back(
            absl::StrCat(kNewBullet, "Unsupported match type '",
                         MatchField_MatchType_Name(
                             ir_match_info->match_field().match_type()),
                         "'."));
    }
    if (!invalid_match_reasons.empty()) {
      invalid_reasons.push_back(
          GenerateFormattedError(MatchFieldName(pd_match_name),
                                 absl::StrJoin(invalid_match_reasons, "\n")));
    }
  }

  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(absl::StrJoin(invalid_reasons, "\n"));
  }
  return absl::OkStatus();
}

// Converts a PD action invocation to its IR form and returns it.
static absl::StatusOr<IrActionInvocation> PdActionInvocationToIr(
    const IrP4Info &ir_p4info,
    const google::protobuf::Message &pd_action_invocation) {
  const std::vector<std::string> all_fields =
      GetAllFieldNames(pd_action_invocation);
  if (all_fields.size() > 1) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        "Action", absl::StrCat(kNewBullet, "Expected exactly one action.")));
  }
  const std::string &action_name = all_fields[0];
  const auto &status_or_pd_action =
      GetMessageField(pd_action_invocation, action_name);
  if (!status_or_pd_action.ok()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        ActionName(action_name),
        absl::StrCat(kNewBullet, status_or_pd_action.status().message())));
  }
  const auto *pd_action = *status_or_pd_action;

  const auto &status_or_ir_action_info =
      gutil::FindPtrOrStatus(ir_p4info.actions_by_name(), action_name);
  if (!status_or_ir_action_info.ok()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        ActionName(action_name),
        absl::StrCat(kNewBullet, "It does not exist in the P4Info.")));
  }
  IrActionInvocation ir_action;
  ir_action.set_name(action_name);
  std::vector<std::string> invalid_reasons;

  if (IsElementUnused((*status_or_ir_action_info)->preamble().annotations())) {
    invalid_reasons.push_back(
        absl::StrCat(kNewBullet, "Action has @unused annotation."));
  }

  for (const auto &pd_arg_name : GetAllFieldNames(*pd_action)) {
    const auto &status_or_param_info = gutil::FindPtrOrStatus(
        (*status_or_ir_action_info)->params_by_name(), pd_arg_name);
    if (!status_or_param_info.ok()) {
      invalid_reasons.push_back(GenerateReason(
          ParamName(pd_arg_name), status_or_param_info.status().message()));
      continue;
    }
    const absl::StatusOr<std::string> &pd_arg =
        GetStringField(*pd_action, pd_arg_name);
    if (!pd_arg.ok()) {
      invalid_reasons.push_back(
          GenerateReason(ParamName(pd_arg_name), pd_arg.status().message()));
      continue;
    }
    auto *ir_param = ir_action.add_params();
    ir_param->set_name(pd_arg_name);
    const absl::StatusOr<IrValue> &ir_value =
        FormattedStringToIrValue(*pd_arg, (*status_or_param_info)->format());
    if (!ir_value.ok()) {
      invalid_reasons.push_back(
          GenerateReason(ParamName(pd_arg_name), ir_value.status().message()));
      continue;
    }
    *ir_param->mutable_value() = *ir_value;
  }

  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        ActionName(action_name), absl::StrJoin(invalid_reasons, "\n")));
  }
  return ir_action;
}

// Converts a PD action set to its IR form and stores it in the
// ir_table_entry.
static absl::StatusOr<IrActionSetInvocation> PdActionSetToIr(
    const IrP4Info &ir_p4info, const google::protobuf::Message &pd_action_set) {
  IrActionSetInvocation ir_action_set_invocation;
  std::vector<std::string> invalid_reasons;
  {
    const absl::StatusOr<int32_t> &pd_weight =
        GetInt32Field(pd_action_set, "weight");
    if (!pd_weight.ok()) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet, pd_weight.status().message()));
    } else {
      ir_action_set_invocation.set_weight(*pd_weight);
    }
  }
  {
    const absl::StatusOr<std::string> &pd_watch_port =
        GetStringField(pd_action_set, "watch_port");
    if (!pd_watch_port.ok()) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet, pd_watch_port.status().message()));
    } else {
      ir_action_set_invocation.set_watch_port(*pd_watch_port);
    }
  }
  {
    const auto &pd_action = GetMessageField(pd_action_set, "action");
    if (pd_action.ok() && !GetAllFieldNames(**pd_action).empty()) {
      const absl::StatusOr<IrActionInvocation> &ir_action =
          PdActionInvocationToIr(ir_p4info, **pd_action);
      if (!ir_action.ok()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, ir_action.status().message()));
      } else {
        *ir_action_set_invocation.mutable_action() = *ir_action;
      }
    }
  }
  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        "ActionSet", absl::StrJoin(invalid_reasons, "\n")));
  }
  return ir_action_set_invocation;
}

absl::StatusOr<IrTableEntry> PdTableEntryToIr(
    const IrP4Info &ir_p4info, const google::protobuf::Message &pd,
    bool key_only /*=false*/) {
  IrTableEntry ir;
  const auto &pd_table_field_name = gutil::GetOneOfFieldName(pd, "entry");
  if (!pd_table_field_name.ok()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        "Table",
        absl::StrCat(kNewBullet, pd_table_field_name.status().message())));
  }
  const auto &p4_table_name =
      ProtobufFieldNameToP4Name(*pd_table_field_name, kP4Table);
  if (!p4_table_name.ok()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        "Table", absl::StrCat(kNewBullet, p4_table_name.status().message())));
  }
  const auto &status_or_ir_table_info =
      gutil::FindPtrOrStatus(ir_p4info.tables_by_name(), *p4_table_name);
  if (!status_or_ir_table_info.ok()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        TableName(*p4_table_name),
        absl::StrCat(kNewBullet, "It does not exist in the P4Info.",
                     kPdProtoAndP4InfoOutOfSync)));
  }
  const auto *ir_table_info = *status_or_ir_table_info;
  ir.set_table_name(*p4_table_name);

  std::vector<std::string> invalid_reasons;

  if (IsElementUnused(ir_table_info->preamble().annotations())) {
    invalid_reasons.push_back(
        absl::StrCat(kNewBullet, "Table entry for table '", *p4_table_name,
                     "' has @unused annotation."));
  }

  const auto &status_or_pd_table = GetMessageField(pd, *pd_table_field_name);
  if (!status_or_pd_table.ok()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        TableName(*p4_table_name),
        absl::StrCat(kNewBullet, status_or_pd_table.status().message())));
  }
  const auto *pd_table = *status_or_pd_table;

  const auto &pd_match = GetMessageField(*pd_table, "match");
  if (!pd_match.ok()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        TableName(*p4_table_name),
        absl::StrCat(kNewBullet, pd_match.status().message())));
  }
  const auto &match_status = PdMatchEntryToIr(*ir_table_info, **pd_match, &ir);
  if (!match_status.ok()) {
    invalid_reasons.push_back(absl::StrCat(kNewBullet, match_status.message()));
  }

  const auto &status_or_priority = GetInt32Field(*pd_table, "priority");
  if (status_or_priority.ok()) {
    ir.set_priority(status_or_priority.value());
  }
  if (!key_only) {
    const auto &status_or_metadata =
        GetBytesField(*pd_table, "controller_metadata");
    if (status_or_metadata.ok()) {
      ir.set_controller_metadata(status_or_metadata.value());
    }

    if (ir_table_info->uses_oneshot()) {
      const absl::StatusOr<const FieldDescriptor *> &pd_action_set =
          GetFieldDescriptor(*pd_table, "wcmp_actions");
      if (!pd_action_set.ok()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, pd_action_set.status().message()));
      } else {
        auto *action_set = ir.mutable_action_set();
        for (auto i = 0; i < pd_table->GetReflection()->FieldSize(
                                 *pd_table, *pd_action_set);
             ++i) {
          const absl::StatusOr<IrActionSetInvocation> &ir_action_set =
              PdActionSetToIr(ir_p4info,
                              pd_table->GetReflection()->GetRepeatedMessage(
                                  *pd_table, *pd_action_set, i));
          if (!ir_action_set.ok()) {
            invalid_reasons.push_back(
                absl::StrCat(kNewBullet, ir_action_set.status().message()));
            continue;
          }
          *action_set->add_actions() = *ir_action_set;
        }
      }
    } else {
      const auto &status_or_pd_action = GetMessageField(*pd_table, "action");
      if (status_or_pd_action.ok() &&
          !GetAllFieldNames(**status_or_pd_action).empty()) {
        const absl::StatusOr<IrActionInvocation> &ir_action =
            PdActionInvocationToIr(ir_p4info, **status_or_pd_action);
        if (!ir_action.ok()) {
          invalid_reasons.push_back(
              absl::StrCat(kNewBullet, ir_action.status().message()));
        } else {
          *ir.mutable_action() = *ir_action;
        }
      }
    }

    if (ir_table_info->has_meter()) {
      const absl::StatusOr<bool> &pd_has_meter_config =
          HasField(*pd_table, "meter_config");
      if (!pd_has_meter_config.ok()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, pd_has_meter_config.status().message()));
      } else if (*pd_has_meter_config) {
        const auto &config = GetMessageField(*pd_table, "meter_config");
        if (!config.ok()) {
          invalid_reasons.push_back(
              absl::StrCat(kNewBullet, config.status().message()));
        } else {
          absl::StatusOr<int64_t> value;
          absl::StatusOr<int64_t> burst_value;
          switch (ir_table_info->meter().unit()) {
            case p4::config::v1::MeterSpec_Unit_BYTES: {
              value = GetInt64Field(**config, "bytes_per_second");
              burst_value = GetInt64Field(**config, "burst_bytes");
              break;
            }
            case p4::config::v1::MeterSpec_Unit_PACKETS: {
              value = GetInt64Field(**config, "packets_per_second");
              burst_value = GetInt64Field(**config, "burst_packets");
              break;
            }
            default:
              invalid_reasons.push_back(absl::StrCat(
                  kNewBullet,
                  "Invalid meter unit: ", ir_table_info->meter().unit()));
          }
          auto ir_meter_config = ir.mutable_meter_config();
          if (!value.ok()) {
            invalid_reasons.push_back(
                absl::StrCat(kNewBullet, value.status().message()));
          } else if (*value != 0) {
            ir_meter_config->set_cir(*value);
            ir_meter_config->set_pir(*value);
          }
          if (!burst_value.ok()) {
            invalid_reasons.push_back(
                absl::StrCat(kNewBullet, burst_value.status().message()));
          } else if (*burst_value != 0) {
            ir_meter_config->set_cburst(*burst_value);
            ir_meter_config->set_pburst(*burst_value);
          }
        }
      }
    }

    if (ir_table_info->has_counter()) {
      const absl::StatusOr<bool> &pd_has_counter_data =
          HasField(*pd_table, "counter_data");
      if (!pd_has_counter_data.ok()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, pd_has_counter_data.status().message()));
      } else if (*pd_has_counter_data) {
        const auto &counter_data = GetMessageField(*pd_table, "counter_data");
        if (!counter_data.ok()) {
          invalid_reasons.push_back(
              absl::StrCat(kNewBullet, counter_data.status().message()));
        } else {
          switch (ir_table_info->counter().unit()) {
            case p4::config::v1::CounterSpec_Unit_BYTES: {
              const absl::StatusOr<int64_t> &pd_byte_counter =
                  GetInt64Field(**counter_data, "byte_count");
              if (!pd_byte_counter.ok()) {
                invalid_reasons.push_back(absl::StrCat(
                    kNewBullet, pd_byte_counter.status().message()));
              } else if (*pd_byte_counter != 0) {
                ir.mutable_counter_data()->set_byte_count(*pd_byte_counter);
              }
              break;
            }
            case p4::config::v1::CounterSpec_Unit_PACKETS: {
              const absl::StatusOr<int64_t> &pd_packet_counter =
                  GetInt64Field(**counter_data, "packet_count");
              if (!pd_packet_counter.ok()) {
                invalid_reasons.push_back(absl::StrCat(
                    kNewBullet, pd_packet_counter.status().message()));
              } else if (*pd_packet_counter != 0) {
                ir.mutable_counter_data()->set_packet_count(*pd_packet_counter);
              }
              break;
            }
            case p4::config::v1::CounterSpec_Unit_BOTH: {
              const absl::StatusOr<int64_t> &pd_byte_counter =
                  GetInt64Field(**counter_data, "byte_count");
              if (!pd_byte_counter.ok()) {
                invalid_reasons.push_back(absl::StrCat(
                    kNewBullet, pd_byte_counter.status().message()));
              } else if (*pd_byte_counter != 0) {
                ir.mutable_counter_data()->set_byte_count(*pd_byte_counter);
              }
              const absl::StatusOr<int64_t> &pd_packet_counter =
                  GetInt64Field(**counter_data, "packet_count");
              if (!pd_packet_counter.ok()) {
                invalid_reasons.push_back(absl::StrCat(
                    kNewBullet, pd_packet_counter.status().message()));
              } else if (*pd_packet_counter != 0) {
                ir.mutable_counter_data()->set_packet_count(*pd_packet_counter);
              }
              break;
            }
            default:
              invalid_reasons.push_back(absl::StrCat(
                  kNewBullet,
                  "Invalid counter unit: ", ir_table_info->meter().unit()));
          }
        }
      }
    }

    if (ir_table_info->has_meter() && ir_table_info->has_counter()) {
      absl::Status status =
          AddPdMeterCounterDataToIrEntry(*pd_table, *ir_table_info, ir);
      if (!status.ok()) {
        invalid_reasons.push_back(std::string(status.message()));
      }
    }
  }

  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        TableName(*p4_table_name), absl::StrJoin(invalid_reasons, "\n")));
  }
  return ir;
}

// Generic helper that works for both packet-in and packet-out. For both, T is
// one of {IrPacketIn, IrPacketOut}.
template <typename T>
absl::StatusOr<T> PdPacketIoToIr(const IrP4Info &info, const std::string &kind,
                                 const google::protobuf::Message &packet) {
  T result;
  const std::string &packet_description = absl::StrCat("'", kind, "' message");
  const auto &field_descriptor = GetFieldDescriptor(packet, "payload");
  if (!field_descriptor.ok()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        packet_description,
        absl::StrCat(kNewBullet, field_descriptor.status().message())));
  }
  const auto &validate_status = ValidateFieldDescriptorType(
      *field_descriptor, FieldDescriptor::TYPE_BYTES);
  if (!validate_status.ok()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        packet_description,
        absl::StrCat(kNewBullet, validate_status.message())));
  }
  const auto &pd_payload =
      packet.GetReflection()->GetString(packet, *field_descriptor);
  result.set_payload(pd_payload);

  google::protobuf::Map<std::string, IrPacketIoMetadataDefinition>
      metadata_by_name;
  if (kind == "packet-in") {
    metadata_by_name = info.packet_in_metadata_by_name();
  } else if (kind == "packet-out") {
    metadata_by_name = info.packet_out_metadata_by_name();
  } else {
    return absl::InvalidArgumentError(GenerateFormattedError(
        packet_description,
        absl::StrCat(kNewBullet, "Invalid PacketIo type.")));
  }

  const auto &pd_metadata = GetMessageField(packet, "metadata");
  if (!pd_metadata.ok()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        packet_description,
        absl::StrCat(kNewBullet, pd_metadata.status().message())));
  }
  std::vector<std::string> invalid_reasons;
  for (const auto &entry : Ordered(metadata_by_name)) {
    const absl::StatusOr<std::string> &pd_entry =
        GetStringField(**pd_metadata, entry.first);
    if (!pd_entry.ok()) {
      invalid_reasons.push_back(GenerateReason(MetadataName(entry.first),
                                               pd_entry.status().message()));
      continue;
    }
    auto *ir_metadata = result.add_metadata();
    ir_metadata->set_name(entry.first);
    const absl::StatusOr<IrValue> ir_value =
        FormattedStringToIrValue(*pd_entry, entry.second.format());
    if (!ir_value.ok()) {
      invalid_reasons.push_back(GenerateReason(MetadataName(entry.first),
                                               ir_value.status().message()));
      continue;
    }
    *ir_metadata->mutable_value() = *ir_value;
  }

  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        packet_description, absl::StrJoin(invalid_reasons, "\n")));
  }

  return result;
}

absl::StatusOr<IrPacketIn> PdPacketInToIr(
    const IrP4Info &info, const google::protobuf::Message &packet) {
  return PdPacketIoToIr<IrPacketIn>(info, "packet-in", packet);
}
absl::StatusOr<IrPacketOut> PdPacketOutToIr(
    const IrP4Info &info, const google::protobuf::Message &packet) {
  return PdPacketIoToIr<IrPacketOut>(info, "packet-out", packet);
}

absl::StatusOr<IrReadRequest> PdReadRequestToIr(
    const IrP4Info &info, const google::protobuf::Message &read_request) {
  IrReadRequest result;
  ASSIGN_OR_RETURN(auto device_id, GetUint64Field(read_request, "device_id"));
  if (device_id == 0) {
    return InvalidArgumentErrorBuilder() << "Device ID missing";
  }
  result.set_device_id(device_id);
  ASSIGN_OR_RETURN(auto read_counter_data,
                   GetBoolField(read_request, "read_counter_data"));
  result.set_read_counter_data(read_counter_data);
  ASSIGN_OR_RETURN(auto read_meter_configs,
                   GetBoolField(read_request, "read_meter_configs"));
  result.set_read_meter_configs(read_meter_configs);

  return result;
}

absl::StatusOr<IrReadResponse> PdReadResponseToIr(
    const IrP4Info &info, const google::protobuf::Message &read_response) {
  IrReadResponse ir_response;
  ASSIGN_OR_RETURN(const auto table_entries_descriptor,
                   GetFieldDescriptor(read_response, "table_entries"));
  std::vector<std::string> invalid_reasons;
  for (auto i = 0; i < read_response.GetReflection()->FieldSize(
                           read_response, table_entries_descriptor);
       ++i) {
    const absl::StatusOr<IrTableEntry> &table_entry = PdTableEntryToIr(
        info, read_response.GetReflection()->GetRepeatedMessage(
                  read_response, table_entries_descriptor, i));
    if (!table_entry.ok()) {
      invalid_reasons.push_back(std::string(table_entry.status().message()));
      continue;
    }
    *ir_response.add_table_entries() = *table_entry;
  }
  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        "Read Response", absl::StrJoin(invalid_reasons, "\n")));
  }
  return ir_response;
}

absl::StatusOr<IrUpdate> PdUpdateToIr(const IrP4Info &info,
                                      const google::protobuf::Message &update) {
  IrUpdate ir_update;
  ASSIGN_OR_RETURN(const auto *type_descriptor,
                   GetFieldDescriptor(update, "type"));
  const auto &type_value =
      update.GetReflection()->GetEnumValue(update, type_descriptor);

  if (!p4::v1::Update_Type_IsValid(type_value)) {
    return InvalidArgumentErrorBuilder()
           << "Invalid value for type: " << type_value;
  }
  ir_update.set_type((p4::v1::Update_Type)type_value);

  ASSIGN_OR_RETURN(const auto *table_entry,
                   GetMessageField(update, "table_entry"));
  ASSIGN_OR_RETURN(*ir_update.mutable_table_entry(),
                   PdTableEntryToIr(info, *table_entry));
  return ir_update;
}

absl::StatusOr<IrWriteRequest> PdWriteRequestToIr(
    const IrP4Info &info, const google::protobuf::Message &write_request) {
  IrWriteRequest ir_write_request;
  ASSIGN_OR_RETURN(const auto &device_id,
                   GetUint64Field(write_request, "device_id"));
  ir_write_request.set_device_id(device_id);

  ASSIGN_OR_RETURN(const auto *election_id,
                   GetMessageField(write_request, "election_id"));
  ASSIGN_OR_RETURN(const auto &high, GetUint64Field(*election_id, "high"));
  ASSIGN_OR_RETURN(const auto &low, GetUint64Field(*election_id, "low"));
  if (high > 0 || low > 0) {
    auto *ir_election_id = ir_write_request.mutable_election_id();
    ir_election_id->set_high(high);
    ir_election_id->set_low(low);
  }

  ASSIGN_OR_RETURN(const auto updates_descriptor,
                   GetFieldDescriptor(write_request, "updates"));
  std::vector<std::string> invalid_reasons;
  for (auto i = 0; i < write_request.GetReflection()->FieldSize(
                           write_request, updates_descriptor);
       ++i) {
    absl::StatusOr<IrUpdate> ir_update =
        PdUpdateToIr(info, write_request.GetReflection()->GetRepeatedMessage(
                               write_request, updates_descriptor, i));
    if (!ir_update.ok()) {
      invalid_reasons.push_back(GenerateFormattedError(
          absl::StrCat("updates[", i, "]"), ir_update.status().message()));
      continue;
    }
    *ir_write_request.add_updates() = *ir_update;
  }

  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        "Write Request", absl::StrJoin(invalid_reasons, "\n")));
  }

  return ir_write_request;
}

static absl::StatusOr<p4::v1::MasterArbitrationUpdate> PdArbitrationToIr(
    const google::protobuf::Message &stream_message) {
  p4::v1::MasterArbitrationUpdate ir_arbitration;
  ASSIGN_OR_RETURN(const auto *arbitration,
                   GetMessageField(stream_message, "arbitration"));

  ASSIGN_OR_RETURN(const auto device_id,
                   GetUint64Field(*arbitration, "device_id"));
  ir_arbitration.set_device_id(device_id);

  ASSIGN_OR_RETURN(const auto *election_id,
                   GetMessageField(*arbitration, "election_id"));
  ASSIGN_OR_RETURN(const auto high, GetUint64Field(*election_id, "high"));
  ir_arbitration.mutable_election_id()->set_high(high);
  ASSIGN_OR_RETURN(const auto low, GetUint64Field(*election_id, "low"));
  ir_arbitration.mutable_election_id()->set_low(low);

  ASSIGN_OR_RETURN(const auto *status, GetMessageField(*arbitration, "status"));
  ASSIGN_OR_RETURN(const auto code, GetInt32Field(*status, "code"));
  ir_arbitration.mutable_status()->set_code(code);
  ASSIGN_OR_RETURN(const auto message, GetStringField(*status, "message"));
  ir_arbitration.mutable_status()->set_message(message);

  return ir_arbitration;
}

absl::StatusOr<IrStreamMessageRequest> PdStreamMessageRequestToIr(
    const IrP4Info &info, const google::protobuf::Message &stream_message) {
  IrStreamMessageRequest ir_stream_message;
  ASSIGN_OR_RETURN(const std::string update_one_of_name,
                   gutil::GetOneOfFieldName(stream_message, "update"));
  if (update_one_of_name == "arbitration") {
    ASSIGN_OR_RETURN(*ir_stream_message.mutable_arbitration(),
                     PdArbitrationToIr(stream_message));
  } else if (update_one_of_name == "packet") {
    ASSIGN_OR_RETURN(const auto *packet,
                     GetMessageField(stream_message, "packet"));
    ASSIGN_OR_RETURN(*ir_stream_message.mutable_packet(),
                     PdPacketOutToIr(info, *packet));
  } else {
    return absl::InvalidArgumentError(
        absl::StrCat("Unsupported update: ", update_one_of_name, "."));
  }
  return ir_stream_message;
}

absl::StatusOr<IrStreamMessageResponse> PdStreamMessageResponseToIr(
    const IrP4Info &info, const google::protobuf::Message &stream_message) {
  IrStreamMessageResponse ir_stream_message;
  ASSIGN_OR_RETURN(const std::string update_one_of_name,
                   gutil::GetOneOfFieldName(stream_message, "update"));
  if (update_one_of_name == "arbitration") {
    ASSIGN_OR_RETURN(*ir_stream_message.mutable_arbitration(),
                     PdArbitrationToIr(stream_message));
  } else if (update_one_of_name == "packet") {
    ASSIGN_OR_RETURN(const auto *packet,
                     GetMessageField(stream_message, "packet"));
    ASSIGN_OR_RETURN(*ir_stream_message.mutable_packet(),
                     PdPacketInToIr(info, *packet));
  } else if (update_one_of_name == "error") {
    auto *ir_error = ir_stream_message.mutable_error();
    ASSIGN_OR_RETURN(const auto *error,
                     GetMessageField(stream_message, "error"));

    ASSIGN_OR_RETURN(const auto *status, GetMessageField(*error, "status"));
    auto *ir_status = ir_error->mutable_status();
    ASSIGN_OR_RETURN(const auto code, GetInt32Field(*status, "code"));
    ir_status->set_code(code);

    ASSIGN_OR_RETURN(const auto message, GetStringField(*status, "message"));
    ir_status->set_message(message);

    ASSIGN_OR_RETURN(const auto *packet_out,
                     GetMessageField(*error, "packet_out"));
    ASSIGN_OR_RETURN(*ir_error->mutable_packet_out(),
                     PdPacketOutToIr(info, *packet_out));
  } else {
    return absl::InvalidArgumentError(
        absl::StrCat("Unsupported update: ", update_one_of_name, "."));
  }
  return ir_stream_message;
}

static absl::StatusOr<IrUpdateStatus> PdUpdateStatusToIr(
    const google::protobuf::Message &pd) {
  IrUpdateStatus ir_update_status;
  ASSIGN_OR_RETURN(int google_rpc_code, GetEnumField(pd, "code"));
  ASSIGN_OR_RETURN(std::string update_status_message,
                   GetStringField(pd, "message"));
  ir_update_status.set_code(static_cast<google::rpc::Code>(google_rpc_code));
  ir_update_status.set_message(update_status_message);
  return ir_update_status;
}

static absl::StatusOr<IrWriteResponse> PdWriteResponseToIr(
    const google::protobuf::Message &pd) {
  IrWriteResponse ir_write_response;
  ASSIGN_OR_RETURN(const auto *status_message,
                   GetMessageField(pd, "rpc_response"));
  ASSIGN_OR_RETURN(const auto *repeated_update_status_field_descriptor,
                   GetFieldDescriptor(*status_message, "statuses"));
  for (int i = 0;
       i < status_message->GetReflection()->FieldSize(
               *status_message, repeated_update_status_field_descriptor);
       i++) {
    // Extract out the Pd::UpdateStatus and pass to PdUpdateStatusToIr
    ASSIGN_OR_RETURN(const auto *pd_update_status,
                     GetRepeatedFieldMessage(*status_message, "statuses", i));
    ASSIGN_OR_RETURN(const auto ir_update_status,
                     PdUpdateStatusToIr(*pd_update_status));
    *ir_write_response.add_statuses() = ir_update_status;
  }
  return ir_write_response;
}

absl::StatusOr<IrWriteRpcStatus> PdWriteRpcStatusToIr(
    const google::protobuf::Message &pd) {
  IrWriteRpcStatus ir_write_rpc_status;
  ASSIGN_OR_RETURN(std::string status_oneof_name,
                   gutil::GetOneOfFieldName(pd, "status"));
  // status_message is of type WriteResponse with field name rpc_response
  if (status_oneof_name == "rpc_response") {
    ASSIGN_OR_RETURN(*ir_write_rpc_status.mutable_rpc_response(),
                     PdWriteResponseToIr(pd));
  } else if (status_oneof_name == "rpc_wide_error") {
    ASSIGN_OR_RETURN(const auto *rpc_wide_error_message,
                     GetMessageField(pd, "rpc_wide_error"));
    ASSIGN_OR_RETURN(int32_t status_code,
                     GetInt32Field(*rpc_wide_error_message, "code"));
    ASSIGN_OR_RETURN(std::string status_message,
                     GetStringField(*rpc_wide_error_message, "message"));
    auto *rpc_wide_error = ir_write_rpc_status.mutable_rpc_wide_error();
    rpc_wide_error->set_code(status_code);
    rpc_wide_error->set_message(status_message);
    return ir_write_rpc_status;
  } else {
    return gutil::InvalidArgumentErrorBuilder()
           << status_oneof_name << " is not a valid status one_of value."
           << kPdProtoAndP4InfoOutOfSync;
  }
  return ir_write_rpc_status;
}

absl::StatusOr<int> GetEnumField(const google::protobuf::Message &message,
                                 const std::string &field_name) {
  ASSIGN_OR_RETURN(auto *field_descriptor,
                   GetFieldDescriptor(message, field_name));
  RETURN_IF_ERROR(ValidateFieldDescriptorType(field_descriptor,
                                              FieldDescriptor::TYPE_ENUM));
  int enum_value =
      message.GetReflection()->GetEnumValue(message, field_descriptor);
  if (field_descriptor->enum_type()->FindValueByNumber(enum_value) == nullptr) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Enum value within " << field_name << " is : " << enum_value;
  }
  return enum_value;
}

absl::Status SetEnumField(google::protobuf::Message *message,
                          const std::string &enum_field_name, int enum_value) {
  ASSIGN_OR_RETURN(auto *field_descriptor,
                   GetFieldDescriptor(*message, enum_field_name));
  RETURN_IF_ERROR(ValidateFieldDescriptorType(field_descriptor,
                                              FieldDescriptor::TYPE_ENUM));
  if (field_descriptor->enum_type()->FindValueByNumber(enum_value) == nullptr) {
    return gutil::InvalidArgumentErrorBuilder()
           << "enum_value: " << enum_value << " is not a valid enum value ";
  }
  message->GetReflection()->SetEnumValue(message, field_descriptor, enum_value);
  return absl::OkStatus();
}

absl::Status PdTableEntryToOnlyKeyPd(const IrP4Info &info,
                                     const google::protobuf::Message &pd,
                                     google::protobuf::Message *key_only_pd) {
  key_only_pd->CopyFrom(pd);
  ASSIGN_OR_RETURN(const std::string &pd_table_field_name,
                   gutil::GetOneOfFieldName(pd, "entry"));
  ASSIGN_OR_RETURN(
      const std::string &p4_table_name,
      ProtobufFieldNameToP4Name(pd_table_field_name, pdpi::kP4Table));
  ASSIGN_OR_RETURN(const auto &ir_table_info,
                   gutil::FindOrStatus(info.tables_by_name(), p4_table_name),
                   _ << "Table \"" << p4_table_name
                     << "\" does not exist in P4Info."
                     << kPdProtoAndP4InfoOutOfSync);
  ASSIGN_OR_RETURN(auto *pd_table,
                   GetMutableMessage(key_only_pd, pd_table_field_name));

  RETURN_IF_ERROR(ClearField(pd_table, "controller_metadata"));
  if (ir_table_info.uses_oneshot()) {
    RETURN_IF_ERROR(ClearField(pd_table, "wcmp_actions"));
  } else {
    RETURN_IF_ERROR(ClearField(pd_table, "action"));
  }
  if (ir_table_info.has_meter()) {
    RETURN_IF_ERROR(ClearField(pd_table, "meter"));
  }
  if (ir_table_info.has_counter()) {
    RETURN_IF_ERROR(ClearField(pd_table, "counter"));
  }
  return absl::OkStatus();
}

}  // namespace pdpi
