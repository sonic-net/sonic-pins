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

#include "p4_pdpi/ir.h"

#include <ctype.h>
#include <stdint.h>

#include <string>
#include <vector>

#include "absl/algorithm/container.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/ascii.h"
#include "absl/strings/escaping.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/strip.h"
#include "google/protobuf/any.pb.h"
#include "google/protobuf/map.h"
#include "google/protobuf/message.h"
#include "google/rpc/code.pb.h"
#include "google/rpc/status.pb.h"
#include "gutil/collections.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/config/v1/p4types.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/translation_options.h"
#include "p4_pdpi/utils/ir.h"

namespace pdpi {

using ::absl::StatusOr;
using ::gutil::InvalidArgumentErrorBuilder;
using ::gutil::PrintShortTextProto;
using ::gutil::PrintTextProto;
using ::gutil::UnimplementedErrorBuilder;
using ::p4::config::v1::MatchField;
using ::p4::config::v1::P4TypeInfo;
using ::pdpi::Format;
using ::pdpi::IrActionDefinition;
using ::pdpi::IrActionInvocation;
using ::pdpi::IrMatchFieldDefinition;
using ::pdpi::IrP4Info;
using ::pdpi::IrTableDefinition;

namespace {

// Helper for GetFormat that extracts the necessary info from a P4Info
// element. T could be p4::config::v1::ControllerPacketMetadata::Metadata,
// p4::config::v1::MatchField, or p4::config::v1::Action::Param (basically
// anything that has a set of annotations, a bitwidth and named type
// information).
template <typename T>
StatusOr<Format> GetFormatForP4InfoElement(const T &element,
                                           const P4TypeInfo &type_info) {
  bool is_sdn_string = false;
  if (element.has_type_name()) {
    const auto &name = element.type_name().name();
    ASSIGN_OR_RETURN(const auto *named_type,
                     gutil::FindPtrOrStatus(type_info.new_types(), name),
                     _ << "Type definition for \"" << name << "\" not found");
    if (named_type->has_translated_type()) {
      if (named_type->translated_type().sdn_type_case() ==
          p4::config::v1::P4NewTypeTranslation::kSdnString) {
        is_sdn_string = true;
      }
    }
  }
  std::vector<std::string> annotations;
  for (const auto &annotation : element.annotations()) {
    annotations.push_back(annotation);
  }
  return GetFormat(annotations, element.bitwidth(), is_sdn_string);
}

// Add a single packet-io metadata to the IR.
absl::Status ProcessPacketIoMetadataDefinition(
    const p4::config::v1::ControllerPacketMetadata &data,
    google::protobuf::Map<uint32_t, IrPacketIoMetadataDefinition> *by_id,
    google::protobuf::Map<std::string, IrPacketIoMetadataDefinition> *by_name,
    const P4TypeInfo &type_info) {
  const std::string &kind = data.preamble().name();
  if (!by_id->empty()) {
    // Only checking by_id, since by_id->size() == by_name->size()
    return InvalidArgumentErrorBuilder()
           << "Found duplicate \"" << kind << "\" controller packet metadata";
  }
  for (const auto &metadata : data.metadata()) {
    IrPacketIoMetadataDefinition ir_metadata;
    *ir_metadata.mutable_metadata() = metadata;
    ASSIGN_OR_RETURN(const auto &format,
                     GetFormatForP4InfoElement(metadata, type_info));
    ir_metadata.set_format(format);
    if (absl::c_any_of(metadata.annotations(),
                       [](absl::string_view annotation) {
                         return annotation == "@padding";
                       })) {
      ir_metadata.set_is_padding(true);
    }
    RETURN_IF_ERROR(gutil::InsertIfUnique(
        by_id, metadata.id(), ir_metadata,
        absl::StrCat("Found several \"", kind,
                     "\" metadata with the same ID: ", metadata.id())));
    RETURN_IF_ERROR(gutil::InsertIfUnique(
        by_name, metadata.name(), ir_metadata,
        absl::StrCat("Found several \"", kind,
                     "\" metadata with the same name: ", metadata.name())));
  }
  return absl::OkStatus();
}

// Searches for an annotation with the given name and extract a single uint32_t
// number from the argument. Fails if the annotation appears multiple times.
StatusOr<uint32_t> GetNumberInAnnotation(
    const google::protobuf::RepeatedPtrField<std::string> &annotations,
    const std::string &annotation_name) {
  absl::optional<uint32_t> result;
  for (const std::string &annotation : annotations) {
    absl::string_view view = annotation;
    if (absl::ConsumePrefix(&view, absl::StrCat("@", annotation_name, "("))) {
      if (result.has_value()) {
        return InvalidArgumentErrorBuilder()
               << "Cannot have multiple annotations with the name \""
               << annotation_name << "\"";
      }
      const std::string number = std::string(absl::StripSuffix(view, ")"));
      for (const char c : number) {
        if (!isdigit(c)) {
          return InvalidArgumentErrorBuilder()
                 << "Expected the argument to @" << annotation_name
                 << " to be a number, but found non-number character";
        }
      }
      result = std::stoi(number);
    }
  }
  if (!result.has_value()) {
    return InvalidArgumentErrorBuilder()
           << "No annotation found with name \"" << annotation_name << "\"";
  }
  return result.value();
}

absl::flat_hash_set<std::string> GetMandatoryMatches(
    const IrTableDefinition &table) {
  absl::flat_hash_set<std::string> mandatory_matches;
  for (const auto &iter : table.match_fields_by_name()) {
    if (iter.second.match_field().match_type() == MatchField::EXACT) {
      mandatory_matches.insert(iter.second.match_field().name());
    }
  }
  return mandatory_matches;
}

absl::Status ValidateMatchFieldDefinition(const IrMatchFieldDefinition &match) {
  switch (match.match_field().match_type()) {
    case p4::config::v1::MatchField::LPM:
    case p4::config::v1::MatchField::TERNARY:
      if (match.format() == Format::STRING) {
        return InvalidArgumentErrorBuilder()
               << "Only EXACT and OPTIONAL match fields can use "
                  "Format::STRING: "
               << PrintShortTextProto(match.match_field());
      }
      return absl::OkStatus();
    case p4::config::v1::MatchField::EXACT:
    case p4::config::v1::MatchField::OPTIONAL:
      return absl::OkStatus();
    default:
      return InvalidArgumentErrorBuilder()
             << "Match field match type not supported: "
             << PrintShortTextProto(match.match_field());
  }
}

absl::StatusOr<uint32_t> TableAliasToId(const p4::config::v1::P4Info &p4_info,
                                        absl::string_view table_alias) {
  absl::flat_hash_map<std::string, uint32_t> table_alias_to_table_id;
  for (const p4::config::v1::Table &table : p4_info.tables()) {
    if (table.preamble().alias() == table_alias) {
      return table.preamble().id();
    }
  }
  return absl::NotFoundError(
      absl::StrCat("Can't find table id for alias `", table_alias, "`"));
}

absl::StatusOr<uint32_t> MatchFieldNameToId(
    const p4::config::v1::P4Info &p4_info, uint32_t table_id,
    absl::string_view match_field_name) {
  for (const p4::config::v1::Table &table : p4_info.tables()) {
    if (table.preamble().id() != table_id) {
      continue;
    }
    for (const p4::config::v1::MatchField &match_field : table.match_fields()) {
      if (match_field.name() == match_field_name) {
        return match_field.id();
      }
    }
  }
  return absl::NotFoundError(
      absl::StrCat("Can't find match field id for match field name `",
                   match_field_name, "` in table `", table_id, "`"));
}

// Returns the set of references for a given set of annotations. Does not
// validate the table or match field yet.
absl::StatusOr<std::vector<IrMatchFieldReference>> GetRefersToAnnotations(
    const p4::config::v1::P4Info &p4info,
    const ::google::protobuf::RepeatedPtrField<std::string> &annotations) {
  constexpr absl::string_view kError = "Found invalid @refers_to annotation: ";
  std::vector<IrMatchFieldReference> result;
  for (absl::string_view annotation_contents : annotations) {
    if (absl::ConsumePrefix(&annotation_contents, "@refers_to(")) {
      if (!absl::ConsumeSuffix(&annotation_contents, ")")) {
        return gutil::InvalidArgumentErrorBuilder() << kError << "Missing )";
      }
      std::vector<std::string> parts = absl::StrSplit(annotation_contents, ',');
      if (parts.size() != 2) {
        return gutil::InvalidArgumentErrorBuilder()
               << kError << "Incorrect number of arguments, required 2 but got "
               << parts.size() << " instead.";
      }

      absl::string_view table = absl::StripAsciiWhitespace(parts[0]);
      absl::string_view match_field = absl::StripAsciiWhitespace(parts[1]);

      ASSIGN_OR_RETURN(uint32_t table_id, TableAliasToId(p4info, table));
      ASSIGN_OR_RETURN(uint32_t match_field_id,
                       MatchFieldNameToId(p4info, table_id, match_field));

      IrMatchFieldReference reference;
      reference.set_table(std::string(table));
      reference.set_match_field(std::string(match_field));
      reference.set_table_id(table_id);
      reference.set_match_field_id(match_field_id);
      result.push_back(reference);
    }
  }
  return result;
}

std::vector<std::string> GetMissingFields(
    const absl::flat_hash_set<std::string> &actual_fields,
    absl::flat_hash_set<std::string> expected_fields) {
  // Erase actual fields from expected_fields.
  // Whatever remains are the missing fields.
  absl::erase_if(expected_fields,
                 [&](const auto &k) { return actual_fields.contains(k); });

  // Convert to a vector so we can sort the fields to ensure stability.
  std::vector<std::string> missing_fields(expected_fields.begin(),
                                          expected_fields.end());
  std::sort(missing_fields.begin(), missing_fields.end());
  return missing_fields;
}

absl::Status CheckMandatoryMatches(
    const absl::flat_hash_set<std::string> &actual_matches,
    const IrTableDefinition &table) {
  auto expected_matches = GetMandatoryMatches(table);
  if (actual_matches.size() != expected_matches.size()) {
    auto missing_matches = GetMissingFields(actual_matches, expected_matches);
    return InvalidArgumentErrorBuilder()
           << "Missing matches: "
           << absl::StrCat("'", absl::StrJoin(missing_matches, "', '"), "'")
           << ". Expected " << expected_matches.size()
           << " mandatory match conditions, but found " << actual_matches.size()
           << " instead.";
  }
  return absl::OkStatus();
}

absl::Status CheckParams(const absl::flat_hash_set<std::string> &actual_params,
                         const IrActionDefinition &action) {
  absl::flat_hash_set<std::string> expected_params;
  for (const auto &[name, _] : action.params_by_name()) {
    expected_params.insert(name);
  }
  if (actual_params.size() != expected_params.size()) {
    auto missing_params = GetMissingFields(actual_params, expected_params);
    return InvalidArgumentErrorBuilder()
           << "Missing parameters: "
           << absl::StrCat("'", absl::StrJoin(missing_params, "'. '"), "'")
           << ". Expected " << expected_params.size()
           << " parameters, but found " << actual_params.size() << " instead.";
  }
  return absl::OkStatus();
}

// Verifies the contents of the PI representation and translates to the IR
// message
StatusOr<IrMatch> PiMatchFieldToIr(
    const IrP4Info &info, TranslationOptions options,
    const IrMatchFieldDefinition &ir_match_definition,
    const p4::v1::FieldMatch &pi_match) {
  IrMatch match_entry;
  const MatchField &match_field = ir_match_definition.match_field();
  uint32_t bitwidth = match_field.bitwidth();
  absl::string_view match_name = match_field.name();
  std::vector<std::string> invalid_reasons;

  if (ir_match_definition.is_unsupported() && !options.allow_unsupported) {
    invalid_reasons.push_back(
        absl::StrCat(kNewBullet, "Match field has @unsupported annotation."));
  }

  switch (match_field.match_type()) {
    case MatchField::EXACT: {
      if (!pi_match.has_exact()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, "Must be an exact match type."));
        break;
      }
      match_entry.set_name(match_field.name());
      const absl::StatusOr<IrValue> &exact = ArbitraryByteStringToIrValue(
          ir_match_definition.format(), bitwidth, pi_match.exact().value());
      if (!exact.ok()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, exact.status().message()));
        break;
      }
      *match_entry.mutable_exact() = *exact;
      break;
    }
    case MatchField::LPM: {
      if (!pi_match.has_lpm()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, "Must be an LPM match type."));
        break;
      }

      uint32_t prefix_len = pi_match.lpm().prefix_len();
      if (prefix_len == 0) {
        invalid_reasons.push_back(absl::StrCat(
            kNewBullet,
            "A wild-card LPM match (i.e., prefix length of 0) must be "
            "represented by omitting the match altogether."));
      }
      match_entry.set_name(match_field.name());
      const absl::StatusOr<std::string> &mask =
          PrefixLenToMask(prefix_len, bitwidth);
      if (!mask.ok()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, mask.status().message()));
        break;
      }
      const absl::StatusOr<std::string> &value =
          ArbitraryToNormalizedByteString(pi_match.lpm().value(), bitwidth);
      if (!value.ok()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, value.status().message()));
        break;
      }
      const absl::StatusOr<std::string> &intersection =
          Intersection(*value, *mask);
      if (!intersection.ok()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, intersection.status().message()));
        break;
      }
      if (*value != *intersection) {
        invalid_reasons.push_back(absl::StrCat(
            kNewBullet, "Lpm value has masked bits that are set. Value: '",
            absl::CEscape(*value), "' Prefix Length: ", prefix_len));
        break;
      }
      match_entry.mutable_lpm()->set_prefix_length(prefix_len);
      const absl::StatusOr<IrValue> &ir_value = ArbitraryByteStringToIrValue(
          ir_match_definition.format(), bitwidth, *value);
      if (!ir_value.ok()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, ir_value.status().message()));
        break;
      }
      *match_entry.mutable_lpm()->mutable_value() = *ir_value;
      break;
    }
    case MatchField::TERNARY: {
      if (!pi_match.has_ternary()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, "Must be a ternary match type."));
        break;
      }

      const absl::StatusOr<std::string> &value =
          ArbitraryToNormalizedByteString(pi_match.ternary().value(), bitwidth);
      if (!value.ok()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, value.status().message()));
        break;
      }
      const absl::StatusOr<std::string> &mask =
          ArbitraryToNormalizedByteString(pi_match.ternary().mask(), bitwidth);
      if (!mask.ok()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, mask.status().message()));
        break;
      }

      if (IsAllZeros(*mask)) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet,
                         "A wild-card ternary match (i.e., mask of 0) must "
                         "be represented by omitting the match altogether."));
        break;
      }
      match_entry.set_name(match_field.name());
      const absl::StatusOr<std::string> &intersection =
          Intersection(*value, *mask);
      if (!intersection.ok()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, intersection.status().message()));
        break;
      }
      if (*value != *intersection) {
        invalid_reasons.push_back(absl::StrCat(
            kNewBullet, "Ternary value has masked bits that are set. Value: ",
            absl::CEscape(*value), " Mask: ", absl::CEscape(*mask)));
        break;
      }
      const absl::StatusOr<IrValue> &ir_value = ArbitraryByteStringToIrValue(
          ir_match_definition.format(), bitwidth, *value);
      if (!ir_value.ok()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, ir_value.status().message()));
        break;
      }
      *match_entry.mutable_ternary()->mutable_value() = *ir_value;
      const absl::StatusOr<IrValue> &ir_mask = ArbitraryByteStringToIrValue(
          ir_match_definition.format(), bitwidth, *mask);
      if (!ir_mask.ok()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, ir_mask.status().message()));
        break;
      }
      *match_entry.mutable_ternary()->mutable_mask() = *ir_mask;
      break;
    }
    case MatchField::OPTIONAL: {
      if (!pi_match.has_optional()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, "Must be an optional match type."));
        break;
      }

      match_entry.set_name(match_field.name());
      const absl::StatusOr<IrValue> &ir_value = ArbitraryByteStringToIrValue(
          ir_match_definition.format(), bitwidth, pi_match.optional().value());
      if (!ir_value.ok()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, ir_value.status().message()));
        break;
      }
      *match_entry.mutable_optional()->mutable_value() = *ir_value;
      break;
    }
    default:
      invalid_reasons.push_back(absl::StrCat(
          kNewBullet, "Unsupported match type '",
          MatchField_MatchType_Name(match_field.match_type()), "'."));
  }

  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        MatchFieldName(match_name), absl::StrJoin(invalid_reasons, "\n")));
  }
  return match_entry;
}

// Translates the action invocation from its PI form to IR.
StatusOr<IrActionInvocation> PiActionToIr(
    const IrP4Info &info, TranslationOptions options,
    const p4::v1::Action &pi_action,
    const google::protobuf::RepeatedPtrField<IrActionReference>
        &valid_actions) {
  IrActionInvocation action_entry;
  uint32_t action_id = pi_action.action_id();

  const auto &status_or_ir_action_definition =
      gutil::FindPtrOrStatus(info.actions_by_id(), action_id);
  if (!status_or_ir_action_definition.ok()) {
    return absl::InvalidArgumentError(absl::StrCat(
        kNewBullet, "Action ID ", action_id, " does not exist in the P4Info."));
  }
  const auto *ir_action_definition = *status_or_ir_action_definition;

  if (absl::c_find_if(valid_actions,
                      [action_id](const IrActionReference &action) {
                        return action.action().preamble().id() == action_id;
                      }) == valid_actions.end()) {
    return absl::InvalidArgumentError(
        GenerateFormattedError(absl::StrCat("Action ID ", action_id),
                               "It is not a valid action for this table."));
  }

  action_entry.set_name(ir_action_definition->preamble().alias());
  absl::flat_hash_set<uint32_t> used_params;
  std::vector<std::string> invalid_reasons;
  absl::flat_hash_set<std::string> actual_params;

  if (ir_action_definition->is_unsupported() && !options.allow_unsupported) {
    invalid_reasons.push_back(
        absl::StrCat(kNewBullet, "Action has @unsupported annotation."));
  }

  for (const auto &param : pi_action.params()) {
    const absl::Status duplicate = gutil::InsertIfUnique(
        used_params, param.param_id(),
        absl::StrCat("Duplicate param field with ID ", param.param_id(), "."));
    if (!duplicate.ok()) {
      invalid_reasons.push_back(absl::StrCat(kNewBullet, duplicate.message()));
      continue;
    }

    const auto status_or_ir_param_definition = gutil::FindPtrOrStatus(
        ir_action_definition->params_by_id(), param.param_id());
    if (!status_or_ir_param_definition.ok()) {
      invalid_reasons.push_back(absl::StrCat(
          kNewBullet, "Unable to find param ID ", param.param_id(), "."));
      continue;
    }
    const auto *ir_param_definition = *status_or_ir_param_definition;
    IrActionInvocation::IrActionParam *param_entry = action_entry.add_params();
    param_entry->set_name(ir_param_definition->param().name());
    const absl::StatusOr<IrValue> &ir_value = ArbitraryByteStringToIrValue(
        ir_param_definition->format(), ir_param_definition->param().bitwidth(),
        param.value());
    if (!ir_value.ok()) {
      invalid_reasons.push_back(
          GenerateReason(ParamName(ir_param_definition->param().name()),
                         ir_value.status().message()));
      continue;
    }
    actual_params.insert(param_entry->name());
    *param_entry->mutable_value() = *ir_value;
  }
  const auto &num_params_status =
      CheckParams(actual_params, *ir_action_definition);
  if (!num_params_status.ok()) {
    invalid_reasons.push_back(
        absl::StrCat(kNewBullet, num_params_status.message()));
  }
  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        ActionName(action_entry.name()), absl::StrJoin(invalid_reasons, "\n")));
  }
  return action_entry;
}

// Translates the action set from its PI form to IR.
StatusOr<IrActionSet> PiActionSetToIr(
    const IrP4Info &info, TranslationOptions options,
    const p4::v1::ActionProfileActionSet &pi_action_set,
    const google::protobuf::RepeatedPtrField<IrActionReference>
        &valid_actions) {
  IrActionSet ir_action_set;
  std::vector<std::string> invalid_reasons;
  for (const auto &pi_profile_action : pi_action_set.action_profile_actions()) {
    auto *ir_action = ir_action_set.add_actions();
    const absl::StatusOr<IrActionInvocation> &action =
        PiActionToIr(info, options, pi_profile_action.action(), valid_actions);
    // On failure check the returned status as well as the invalid reasons
    // field.
    if (!action.ok()) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet, action.status().message()));
      continue;
    }
    *ir_action->mutable_action() = *action;

    // A action set weight that is not positive does not make sense on a switch.
    if (pi_profile_action.weight() < 1) {
      invalid_reasons.push_back(absl::StrCat(
          kNewBullet, "Expected positive action set weight, but got ",
          pi_profile_action.weight(), " instead."));
      continue;
    }
    ir_action->set_weight(pi_profile_action.weight());
    if (!pi_profile_action.watch_port().empty()) {
      ir_action->set_watch_port(pi_profile_action.watch_port());
    }
  }
  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        "Action Set", absl::StrJoin(invalid_reasons, "\n")));
  }
  return ir_action_set;
}

// Generic helper that works for both packet-in and packet-out. For both, I is
// one of p4::v1::{PacketIn, PacketOut} and O is one of {IrPacketIn,
// IrPacketOut}.
template <typename I, typename O>
StatusOr<O> PiPacketIoToIr(const IrP4Info &info, const std::string &kind,
                           const I &packet) {
  O result;
  result.set_payload(packet.payload());
  absl::flat_hash_set<uint32_t> used_metadata_ids;

  const std::string &packet_description = absl::StrCat("'", kind, "' message");
  google::protobuf::Map<uint32_t, IrPacketIoMetadataDefinition> metadata_by_id;
  if (kind == "packet-in") {
    metadata_by_id = info.packet_in_metadata_by_id();
  } else if (kind == "packet-out") {
    metadata_by_id = info.packet_out_metadata_by_id();
  } else {
    return absl::InvalidArgumentError(GenerateFormattedError(
        packet_description,
        absl::StrCat(kNewBullet, "Invalid PacketIo type.")));
  }

  std::vector<std::string> invalid_reasons;
  for (const auto &metadata : packet.metadata()) {
    uint32_t id = metadata.metadata_id();
    const absl::Status &duplicate = gutil::InsertIfUnique(
        used_metadata_ids, id,
        absl::StrCat("Duplicate metadata found with ID ", id, "."));
    if (!duplicate.ok()) {
      invalid_reasons.push_back(absl::StrCat(kNewBullet, duplicate.message()));
      continue;
    }

    const auto &status_or_metadata_definition_ptr =
        gutil::FindPtrOrStatus(metadata_by_id, id);
    if (!status_or_metadata_definition_ptr.ok()) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet, " Metadata with ID ", id, " not defined."));
      continue;
    }

    const pdpi::IrPacketIoMetadataDefinition metadata_definition =
        **status_or_metadata_definition_ptr;

    // Metadata with @padding annotation must be all zeros and must not be
    // included in IR representation (go/pdpi-padding).
    if (metadata_definition.is_padding()) {
      if (!IsAllZeros(metadata.value())) {
        invalid_reasons.push_back(absl::StrCat(
            kNewBullet, " Metadata with ID ", id,
            " has @padding annotation, so bytestring must be all zeros."));
      }
      continue;
    }

    IrPacketMetadata ir_metadata;
    const std::string &metadata_name = metadata_definition.metadata().name();
    ir_metadata.set_name(metadata_name);
    const absl::StatusOr<IrValue> ir_value = ArbitraryByteStringToIrValue(
        metadata_definition.format(), metadata_definition.metadata().bitwidth(),
        metadata.value());
    if (!ir_value.ok()) {
      invalid_reasons.push_back(GenerateReason(MetadataName(metadata_name),
                                               ir_value.status().message()));
      continue;
    }
    *ir_metadata.mutable_value() = *ir_value;
    *result.add_metadata() = ir_metadata;
  }
  // Check for missing metadata
  for (const auto &item : metadata_by_id) {
    const auto &id = item.first;
    const auto &meta = item.second;
    if (!used_metadata_ids.contains(id)) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet, "Metadata '", meta.metadata().name(),
                       "' with id ", meta.metadata().id(), " is missing."));
      continue;
    }
  }

  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        packet_description, absl::StrJoin(invalid_reasons, "\n")));
  }

  return result;
}

// Verifies the contents of the IR representation and translates to the PI
// message.
StatusOr<p4::v1::FieldMatch> IrMatchFieldToPi(
    const IrP4Info &info, TranslationOptions options,
    const IrMatchFieldDefinition &ir_match_definition,
    const IrMatch &ir_match) {
  p4::v1::FieldMatch match_entry;
  const MatchField &match_field = ir_match_definition.match_field();
  uint32_t bitwidth = match_field.bitwidth();
  absl::string_view match_name = match_field.name();

  std::vector<std::string> invalid_reasons;

  if (ir_match_definition.is_unsupported() && !options.allow_unsupported) {
    invalid_reasons.push_back(
        absl::StrCat(kNewBullet, "Match field has @unsupported annotation."));
  }

  switch (match_field.match_type()) {
    case MatchField::EXACT: {
      if (!ir_match.has_exact()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, "Must be an exact match type."));
        break;
      }

      match_entry.set_field_id(match_field.id());
      const absl::Status &valid =
          ValidateIrValueFormat(ir_match.exact(), ir_match_definition.format());
      if (!valid.ok()) {
        invalid_reasons.push_back(absl::StrCat(kNewBullet, valid.message()));
        break;
      }
      const absl::StatusOr<std::string> &value = IrValueToNormalizedByteString(
          ir_match.exact(), ir_match_definition.match_field().bitwidth());
      if (!value.ok()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, value.status().message()));
        break;
      }
      if (ir_match_definition.format() == STRING) {
        match_entry.mutable_exact()->set_value(*value);
      } else {
        match_entry.mutable_exact()->set_value(
            ArbitraryToCanonicalByteString(*value));
      }
      break;
    }
    case MatchField::LPM: {
      if (!ir_match.has_lpm()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, "Must be an LPM match type."));
        break;
      }

      uint32_t prefix_len = ir_match.lpm().prefix_length();
      if (prefix_len > bitwidth) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, "Prefix length ", prefix_len,
                         " is greater than bitwidth ", bitwidth, " in LPM."));
        break;
      }

      const absl::Status &valid = ValidateIrValueFormat(
          ir_match.lpm().value(), ir_match_definition.format());
      if (!valid.ok()) {
        invalid_reasons.push_back(absl::StrCat(kNewBullet, valid.message()));
        break;
      }
      const absl::StatusOr<std::string> &value = IrValueToNormalizedByteString(
          ir_match.lpm().value(), ir_match_definition.match_field().bitwidth());
      if (!value.ok()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, value.status().message()));
        break;
      }
      if (prefix_len == 0) {
        invalid_reasons.push_back(absl::StrCat(
            kNewBullet,
            "A wild-card LPM match (i.e., prefix length of 0) must be "
            "represented by omitting the match altogether."));
        break;
      }
      match_entry.set_field_id(match_field.id());
      const absl::StatusOr<std::string> &mask =
          PrefixLenToMask(prefix_len, bitwidth);
      if (!mask.ok()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, mask.status().message()));
        break;
      }
      const absl::StatusOr<std::string> &intersection =
          Intersection(*value, *mask);
      if (!intersection.ok()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, intersection.status().message()));
        break;
      }
      if (*value != *intersection) {
        invalid_reasons.push_back(absl::StrCat(
            kNewBullet, "Lpm value has masked bits that are set. Value: ",
            PrintTextProto(ir_match.lpm().value()),
            "Prefix Length: ", prefix_len));
        break;
      }
      match_entry.mutable_lpm()->set_prefix_len(prefix_len);
      match_entry.mutable_lpm()->set_value(
          ArbitraryToCanonicalByteString(*value));
      break;
    }
    case MatchField::TERNARY: {
      if (!ir_match.has_ternary()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, "Must be a ternary match type."));
        break;
      }

      const absl::Status &valid_value = ValidateIrValueFormat(
          ir_match.ternary().value(), ir_match_definition.format());
      if (!valid_value.ok()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, valid_value.message()));
        break;
      }
      const absl::Status &valid_mask = ValidateIrValueFormat(
          ir_match.ternary().mask(), ir_match_definition.format());
      if (!valid_mask.ok()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, valid_mask.message()));
        break;
      }
      const absl::StatusOr<std::string> &value = IrValueToNormalizedByteString(
          ir_match.ternary().value(),
          ir_match_definition.match_field().bitwidth());
      if (!value.ok()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, value.status().message()));
        break;
      }
      const absl::StatusOr<std::string> &mask = IrValueToNormalizedByteString(
          ir_match.ternary().mask(),
          ir_match_definition.match_field().bitwidth());
      if (!mask.ok()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, mask.status().message()));
        break;
      }
      if (IsAllZeros(*mask)) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet,
                         "A wild-card ternary match (i.e., mask of 0) must "
                         "be represented by omitting the match altogether."));
        break;
      }
      match_entry.set_field_id(match_field.id());
      const absl::StatusOr<std::string> &intersection =
          Intersection(*value, *mask);
      if (!intersection.ok()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, intersection.status().message()));
        break;
      }
      if (*value != *intersection) {
        invalid_reasons.push_back(absl::StrCat(
            kNewBullet, "Ternary value has masked bits that are set. Value: ",
            PrintTextProto(ir_match.ternary().value()),
            "Mask: ", PrintTextProto(ir_match.ternary().mask())));
        break;
      }
      match_entry.mutable_ternary()->set_value(
          ArbitraryToCanonicalByteString(*value));
      match_entry.mutable_ternary()->set_mask(
          ArbitraryToCanonicalByteString(*mask));
      break;
    }
    case MatchField::OPTIONAL: {
      if (!ir_match.has_optional()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, "Must be an optional match type."));
      }

      match_entry.set_field_id(match_field.id());
      const absl::Status &valid = ValidateIrValueFormat(
          ir_match.optional().value(), ir_match_definition.format());
      if (!valid.ok()) {
        invalid_reasons.push_back(absl::StrCat(kNewBullet, valid.message()));
        break;
      }
      const absl::StatusOr<std::string> &value = IrValueToNormalizedByteString(
          ir_match.optional().value(),
          ir_match_definition.match_field().bitwidth());
      if (!value.ok()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, value.status().message()));
        break;
      }
      if (ir_match_definition.format() == STRING) {
        match_entry.mutable_optional()->set_value(*value);
      } else {
        match_entry.mutable_optional()->set_value(
            ArbitraryToCanonicalByteString(*value));
      }
      break;
    }
    default:
      invalid_reasons.push_back(absl::StrCat(
          kNewBullet, "Unsupported match type '",
          MatchField_MatchType_Name(match_field.match_type()), "' in ",
          "match field with id ", match_entry.field_id()));
  }
  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        MatchFieldName(match_name), absl::StrJoin(invalid_reasons, "\n")));
  }
  return match_entry;
}

// Translates the action invocation from its IR form to PI.
StatusOr<p4::v1::Action> IrActionInvocationToPi(
    const IrP4Info &info, TranslationOptions options,
    const IrActionInvocation &ir_table_action,
    const google::protobuf::RepeatedPtrField<IrActionReference>
        &valid_actions) {
  const std::string &action_name = ir_table_action.name();

  const auto &status_or_ir_action_definition =
      gutil::FindPtrOrStatus(info.actions_by_name(), action_name);
  if (!status_or_ir_action_definition.ok()) {
    return absl::InvalidArgumentError(absl::StrCat(
        ActionName(action_name), " does not exist in the P4Info."));
  }
  const auto *ir_action_definition = *status_or_ir_action_definition;

  if (absl::c_find_if(
          valid_actions, [action_name](const IrActionReference &action) {
            return action.action().preamble().alias() == action_name;
          }) == valid_actions.end()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        ActionName(action_name), "It is not a valid action for this table."));
  }

  p4::v1::Action action;
  action.set_action_id(ir_action_definition->preamble().id());
  absl::flat_hash_set<std::string> used_params;
  std::vector<std::string> invalid_reasons;

  if (ir_action_definition->is_unsupported() && !options.allow_unsupported) {
    invalid_reasons.push_back(
        absl::StrCat(kNewBullet, "Action has @unsupported annotation."));
  }

  for (const auto &param : ir_table_action.params()) {
    const absl::Status &duplicate = gutil::InsertIfUnique(
        used_params, param.name(),
        absl::StrCat("Duplicate parameter field found with name '",
                     param.name(), "'."));
    if (!duplicate.ok()) {
      invalid_reasons.push_back(absl::StrCat(kNewBullet, duplicate.message()));
      continue;
    }

    const auto &status_or_ir_param_definition = gutil::FindPtrOrStatus(
        ir_action_definition->params_by_name(), param.name());
    if (!status_or_ir_param_definition.ok()) {
      invalid_reasons.push_back(absl::StrCat(
          kNewBullet, "Unable to find parameter '", param.name(), "'."));
      continue;
    }
    const auto *ir_param_definition = *status_or_ir_param_definition;
    p4::v1::Action_Param *param_entry = action.add_params();
    param_entry->set_param_id(ir_param_definition->param().id());
    const absl::Status &valid =
        ValidateIrValueFormat(param.value(), ir_param_definition->format());
    if (!valid.ok()) {
      invalid_reasons.push_back(
          GenerateReason(ParamName(param.name()), valid.message()));
      continue;
    }
    const absl::StatusOr<std::string> &value = IrValueToNormalizedByteString(
        param.value(), ir_param_definition->param().bitwidth());
    if (!value.ok()) {
      invalid_reasons.push_back(
          GenerateReason(ParamName(param.name()), value.status().message()));
      continue;
    }
    if (ir_param_definition->format() == STRING) {
      param_entry->set_value(*value);
    } else {
      param_entry->set_value(ArbitraryToCanonicalByteString(*value));
    }
  }

  const auto &num_params_status =
      CheckParams(used_params, *ir_action_definition);
  if (!num_params_status.ok()) {
    invalid_reasons.push_back(
        absl::StrCat(kNewBullet, num_params_status.message()));
  }

  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        ActionName(action_name), absl::StrJoin(invalid_reasons, "\n")));
  }
  return action;
}

// Translates the action set from its IR form to PI.
StatusOr<p4::v1::ActionProfileActionSet> IrActionSetToPi(
    const IrP4Info &info, TranslationOptions options,
    const IrActionSet &ir_action_set,
    const google::protobuf::RepeatedPtrField<IrActionReference>
        &valid_actions) {
  p4::v1::ActionProfileActionSet pi;
  std::vector<std::string> invalid_reasons;
  for (const auto &ir_action : ir_action_set.actions()) {
    auto *pi_action = pi.add_action_profile_actions();
    const absl::StatusOr<p4::v1::Action> action = IrActionInvocationToPi(
        info, options, ir_action.action(), valid_actions);
    if (!action.ok()) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet, action.status().message()));
      continue;
    }
    *pi_action->mutable_action() = *action;
    if (ir_action.weight() < 1) {
      invalid_reasons.push_back(absl::StrCat(
          kNewBullet, "Expected positive action set weight, but got ",
          ir_action.weight(), " instead."));
      continue;
    }
    pi_action->set_weight(ir_action.weight());
    if (!ir_action.watch_port().empty()) {
      pi_action->set_watch_port(ir_action.watch_port());
    }
  }

  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        "ActionSet", absl::StrJoin(invalid_reasons, "\n")));
  }
  return pi;
}

// Creates a piece of padding metadata. Metadata with the @padding annotation
// must contain a zero value bytestring (go/pdpi-padding).
p4::v1::PacketMetadata CreatePaddingMetadata(uint32_t metadata_id) {
  p4::v1::PacketMetadata metadata;
  metadata.set_metadata_id(metadata_id);
  metadata.set_value(std::string({'\0'}));
  return metadata;
}

template <typename I, typename O>
StatusOr<I> IrPacketIoToPi(const IrP4Info &info, const std::string &kind,
                           const O &packet) {
  I result;
  std::vector<std::string> invalid_reasons;
  result.set_payload(packet.payload());
  absl::flat_hash_set<std::string> used_metadata_names;
  google::protobuf::Map<std::string, IrPacketIoMetadataDefinition>
      metadata_by_name;
  const std::string &packet_description = absl::StrCat("'", kind, "' message");
  if (kind == "packet-in") {
    metadata_by_name = info.packet_in_metadata_by_name();
  } else if (kind == "packet-out") {
    metadata_by_name = info.packet_out_metadata_by_name();
  } else {
    return absl::InvalidArgumentError(GenerateFormattedError(
        packet_description,
        absl::StrCat(kNewBullet, "Invalid PacketIo type.")));
  }

  for (const auto &metadata : packet.metadata()) {
    const std::string &name = metadata.name();
    const absl::Status &duplicate = gutil::InsertIfUnique(
        used_metadata_names, name,
        absl::StrCat("Duplicate metadata found with name '", name, "'."));

    if (!duplicate.ok()) {
      invalid_reasons.push_back(absl::StrCat(kNewBullet, duplicate.message()));
      continue;
    }

    const auto &status_or_metadata_definition_ptr =
        gutil::FindPtrOrStatus(metadata_by_name, name);
    if (!status_or_metadata_definition_ptr.ok()) {
      invalid_reasons.push_back(absl::StrCat(kNewBullet, "Metadata with name ",
                                             name, " not defined."));
      continue;
    }
    const pdpi::IrPacketIoMetadataDefinition &metadata_definition =
        **status_or_metadata_definition_ptr;

    // Metadata with @padding annotation must not be present in IR
    // representation (go/pdpi-padding).
    if (metadata_definition.is_padding()) {
      invalid_reasons.push_back(absl::StrCat(
          kNewBullet, "Metadata '", metadata_definition.metadata().name(),
          "' with id ", metadata_definition.metadata().id(),
          " has @padding annotation so it must be omitted in "
          "IR representation."));
      continue;
    }

    p4::v1::PacketMetadata pi_metadata;
    pi_metadata.set_metadata_id(metadata_definition.metadata().id());
    const absl::Status &valid =
        ValidateIrValueFormat(metadata.value(), metadata_definition.format());
    if (!valid.ok()) {
      invalid_reasons.push_back(
          GenerateReason(MetadataName(name), valid.message()));
      continue;
    }
    const absl::StatusOr<std::string> value = IrValueToNormalizedByteString(
        metadata.value(), metadata_definition.metadata().bitwidth());
    if (!value.ok()) {
      invalid_reasons.push_back(
          GenerateReason(MetadataName(name), value.status().message()));
      continue;
    }
    if (metadata_definition.format() == STRING) {
      pi_metadata.set_value(*value);
    } else {
      pi_metadata.set_value(ArbitraryToCanonicalByteString(*value));
    }
    *result.add_metadata() = pi_metadata;
  }
  // Check for missing metadata
  for (const auto &[name, metadata] : metadata_by_name) {
    // Insert padding metadata into PI representation (go/pdpi-padding).
    if (metadata.is_padding()) {
      *result.add_metadata() = CreatePaddingMetadata(metadata.metadata().id());
    } else if (!used_metadata_names.contains(name)) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet, "Metadata '", metadata.metadata().name(),
                       "' with id ", metadata.metadata().id(), " is missing."));
    }
  }

  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        packet_description, absl::StrJoin(invalid_reasons, "\n")));
  }

  return result;
}

// Checks for an "@unsupported" annotation in the argument.
//
// CAUTION: Calling this function is relatively expensive and should only be
// done during IrP4Info generation. The result is cached in the IrP4Info.
bool ExpensiveIsElementUnsupported(
    const google::protobuf::RepeatedPtrField<std::string> &annotations) {
  return absl::c_any_of(annotations, [](absl::string_view annotation) {
    return annotation == "@unsupported";
  });
}

}  // namespace

StatusOr<IrP4Info> CreateIrP4Info(const p4::config::v1::P4Info &p4_info) {
  IrP4Info info;
  *info.mutable_pkg_info() = p4_info.pkg_info();
  const P4TypeInfo &type_info = p4_info.type_info();

  // Translate all action definitions to IR.
  for (const auto &action : p4_info.actions()) {
    IrActionDefinition ir_action;
    *ir_action.mutable_preamble() = action.preamble();
    for (const auto &param : action.params()) {
      IrActionDefinition::IrActionParamDefinition ir_param;
      *ir_param.mutable_param() = param;
      ASSIGN_OR_RETURN(const auto format,
                       GetFormatForP4InfoElement(param, type_info));
      ir_param.set_format(format);
      ASSIGN_OR_RETURN(
          const std::vector<IrMatchFieldReference> references,
          GetRefersToAnnotations(p4_info, ir_param.param().annotations()));
      for (const IrMatchFieldReference &reference : references) {
        *ir_param.add_references() = reference;
        // If an identical reference already exists, don't add it to the global
        // list of references.
        if (!absl::c_any_of(
                info.references(),
                [&reference](const IrMatchFieldReference &existing_reference) {
                  return google::protobuf::util::MessageDifferencer::Equals(
                      reference, existing_reference);
                })) {
          *info.add_references() = reference;
        }
      }
      RETURN_IF_ERROR(gutil::InsertIfUnique(
          ir_action.mutable_params_by_id(), param.id(), ir_param,
          absl::StrCat("Found several parameters with the same ID ", param.id(),
                       " for action ", action.preamble().alias())));
      RETURN_IF_ERROR(gutil::InsertIfUnique(
          ir_action.mutable_params_by_name(), param.name(), ir_param,
          absl::StrCat("Found several parameters with the same name \"",
                       param.name(), "\" for action \"",
                       action.preamble().alias(), "\"")));
    }
    ir_action.set_is_unsupported(
        ExpensiveIsElementUnsupported(action.preamble().annotations()));
    RETURN_IF_ERROR(gutil::InsertIfUnique(
        info.mutable_actions_by_id(), action.preamble().id(), ir_action,
        absl::StrCat("Found several actions with the same ID: ",
                     action.preamble().id())));
    RETURN_IF_ERROR(gutil::InsertIfUnique(
        info.mutable_actions_by_name(), action.preamble().alias(), ir_action,
        absl::StrCat("Found several actions with the same name: ",
                     action.preamble().name())));
  }

  // Translate all action profiles to IR.
  for (const auto &action_profile : p4_info.action_profiles()) {
    IrActionProfileDefinition ir_action_profile;
    *ir_action_profile.mutable_action_profile() = action_profile;
    RETURN_IF_ERROR(gutil::InsertIfUnique(
        info.mutable_action_profiles_by_id(), action_profile.preamble().id(),
        ir_action_profile,
        absl::StrCat("Found several action profiles with the same ID: ",
                     action_profile.preamble().id())));
    RETURN_IF_ERROR(gutil::InsertIfUnique(
        info.mutable_action_profiles_by_name(),
        action_profile.preamble().alias(), ir_action_profile,
        absl::StrCat("Found several action profiles with the same name: ",
                     action_profile.preamble().name())));
  }

  // Translate all table definitions to IR.
  for (const auto &table : p4_info.tables()) {
    IrTableDefinition ir_table_definition;
    uint32_t table_id = table.preamble().id();
    *ir_table_definition.mutable_preamble() = table.preamble();
    for (const auto &match_field : table.match_fields()) {
      IrMatchFieldDefinition ir_match_definition;
      *ir_match_definition.mutable_match_field() = match_field;
      ASSIGN_OR_RETURN(const auto &format,
                       GetFormatForP4InfoElement(match_field, type_info));
      ir_match_definition.set_format(format);
      RETURN_IF_ERROR(ValidateMatchFieldDefinition(ir_match_definition))
          << "Table " << table.preamble().alias() << " has invalid match field";

      ASSIGN_OR_RETURN(
          const auto &references,
          GetRefersToAnnotations(p4_info, match_field.annotations()));
      for (const auto &reference : references) {
        *ir_match_definition.add_references() = reference;
        if (!absl::c_any_of(
                info.references(),
                [&reference](const IrMatchFieldReference &existing_reference) {
                  return google::protobuf::util::MessageDifferencer::Equals(
                      reference, existing_reference);
                })) {
          *info.add_references() = reference;
        }
      }

      switch (match_field.match_type()) {
        case p4::config::v1::MatchField::OPTIONAL:
        case p4::config::v1::MatchField::RANGE:
        case p4::config::v1::MatchField::TERNARY:
          ir_table_definition.set_requires_priority(true);
          break;
        default:
          break;
      }

      ir_match_definition.set_is_unsupported(
          ExpensiveIsElementUnsupported(match_field.annotations()));

      RETURN_IF_ERROR(gutil::InsertIfUnique(
          ir_table_definition.mutable_match_fields_by_id(), match_field.id(),
          ir_match_definition,
          absl::StrCat("Found several match fields with the same ID ",
                       match_field.id(), " in table \"",
                       table.preamble().alias(), "\"")));
      RETURN_IF_ERROR(gutil::InsertIfUnique(
          ir_table_definition.mutable_match_fields_by_name(),
          match_field.name(), ir_match_definition,
          absl::StrCat("Found several match fields with the same name \"",
                       match_field.name(), "\" in table \"",
                       table.preamble().alias(), "\"")));
    }

    // Is WCMP table?
    const bool is_wcmp = table.implementation_id() != 0;
    const bool has_oneshot = absl::c_any_of(
        table.preamble().annotations(),
        [](const std::string &annotation) { return annotation == "@oneshot"; });
    if (is_wcmp != has_oneshot) {
      return UnimplementedErrorBuilder()
             << "A WCMP table must have a @oneshot annotation, but \""
             << table.preamble().alias()
             << "\" is not valid. is_wcmp = " << is_wcmp
             << ", has_oneshot = " << has_oneshot << "";
    }
    ir_table_definition.set_uses_oneshot(has_oneshot);
    if (is_wcmp) {
      ir_table_definition.set_action_profile_id(table.implementation_id());
    }

    p4::config::v1::ActionRef default_action_ref;
    for (const auto &action_ref : table.action_refs()) {
      IrActionReference ir_action_reference;
      *ir_action_reference.mutable_ref() = action_ref;
      // Make sure the action is defined
      ASSIGN_OR_RETURN(
          *ir_action_reference.mutable_action(),
          gutil::FindOrStatus(info.actions_by_id(), action_ref.id()),
          _ << "Missing definition for action with id " << action_ref.id());
      if (action_ref.scope() == p4::config::v1::ActionRef::DEFAULT_ONLY) {
        *ir_table_definition.add_default_only_actions() = ir_action_reference;
      } else {
        uint32_t proto_id = 0;
        ASSIGN_OR_RETURN(
            proto_id,
            GetNumberInAnnotation(action_ref.annotations(), "proto_id"),
            _ << "Action \"" << ir_action_reference.action().preamble().name()
              << "\" in table \"" << table.preamble().alias()
              << "\" does not have a valid @proto_id annotation");
        ir_action_reference.set_proto_id(proto_id);
        *ir_table_definition.add_entry_actions() = ir_action_reference;
      }
    }
    if (table.const_default_action_id() != 0) {
      const uint32_t const_default_action_id = table.const_default_action_id();
      IrActionReference const_default_action_reference;

      // The const_default_action should always point to a table action.
      for (const auto &action : ir_table_definition.default_only_actions()) {
        if (action.ref().id() == const_default_action_id) {
          const_default_action_reference = action;
          break;
        }
      }
      if (const_default_action_reference.ref().id() == 0) {
        for (const auto &action : ir_table_definition.entry_actions()) {
          if (action.ref().id() == const_default_action_id) {
            const_default_action_reference = action;
            break;
          }
        }
      }
      if (const_default_action_reference.ref().id() == 0) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Table \"" << table.preamble().alias()
               << "\" default action id " << table.const_default_action_id()
               << " does not match any of the table's actions";
      }

      *ir_table_definition.mutable_const_default_action() =
          const_default_action_reference.action();
    }

    // Extract @p4runtime_role annotation.
    for (absl::string_view annotation : table.preamble().annotations()) {
      if (absl::ConsumePrefix(&annotation, "@p4runtime_role(\"") &&
          absl::ConsumeSuffix(&annotation, "\")")) {
        ir_table_definition.set_role(std::string(annotation));
      }
    }

    ir_table_definition.set_size(table.size());
    ir_table_definition.set_is_unsupported(
        ExpensiveIsElementUnsupported(table.preamble().annotations()));

    RETURN_IF_ERROR(gutil::InsertIfUnique(
        info.mutable_tables_by_id(), table_id, ir_table_definition,
        absl::StrCat("Found several tables with the same ID ",
                     table.preamble().id())));
    RETURN_IF_ERROR(gutil::InsertIfUnique(
        info.mutable_tables_by_name(), table.preamble().alias(),
        ir_table_definition,
        absl::StrCat("Found several tables with the same name \"",
                     table.preamble().alias(), "\"")));
  }

  // Validate and translate the packet-io metadata
  for (const auto &metadata : p4_info.controller_packet_metadata()) {
    const std::string &kind = metadata.preamble().name();
    if (kind == "packet_out") {
      RETURN_IF_ERROR(ProcessPacketIoMetadataDefinition(
          metadata, info.mutable_packet_out_metadata_by_id(),
          info.mutable_packet_out_metadata_by_name(), type_info));
    } else if (kind == "packet_in") {
      RETURN_IF_ERROR(ProcessPacketIoMetadataDefinition(
          metadata, info.mutable_packet_in_metadata_by_id(),
          info.mutable_packet_in_metadata_by_name(), type_info));
    } else {
      return InvalidArgumentErrorBuilder()
             << "Unknown controller packet metadata: " << kind
             << ". Only packet_in and packet_out are supported";
    }
  }

  // Counters.
  for (const auto &counter : p4_info.direct_counters()) {
    const auto table_id = counter.direct_table_id();
    RETURN_IF_ERROR(
        gutil::FindPtrOrStatus(info.tables_by_id(), table_id).status())
        << "Missing table " << table_id << " for counter with ID "
        << counter.preamble().id();
    IrCounter ir_counter;
    ir_counter.set_unit(counter.spec().unit());

    // Add to tables_by_id and tables_by_name.
    auto &table1 = (*info.mutable_tables_by_id())[table_id];
    auto &table2 = (*info.mutable_tables_by_name())[table1.preamble().alias()];
    *table1.mutable_counter() = ir_counter;
    *table2.mutable_counter() = ir_counter;
  }

  // Meters.
  for (const auto &meter : p4_info.direct_meters()) {
    const auto table_id = meter.direct_table_id();
    RETURN_IF_ERROR(
        gutil::FindPtrOrStatus(info.tables_by_id(), table_id).status())
        << "Missing table " << table_id << " for meter with ID "
        << meter.preamble().id();
    IrMeter ir_meter;
    ir_meter.set_unit(meter.spec().unit());

    // Add to tables_by_id and tables_by_name.
    auto &table1 = (*info.mutable_tables_by_id())[table_id];
    auto &table2 = (*info.mutable_tables_by_name())[table1.preamble().alias()];
    *table1.mutable_meter() = ir_meter;
    *table2.mutable_meter() = ir_meter;
  }

  // Validate references.
  for (const auto &reference : info.references()) {
    ASSIGN_OR_RETURN(
        const auto *ir_table,
        gutil::FindPtrOrStatus(info.tables_by_name(), reference.table()),
        _ << "Table '" << reference.table()
          << "' referenced in @refers_to does not exist.");
    ASSIGN_OR_RETURN(const auto *ir_match_field,
                     gutil::FindPtrOrStatus(ir_table->match_fields_by_name(),
                                            reference.match_field()),
                     _ << "Match field '" << reference.match_field()
                       << "' referenced in @refers_to does not exist.");
    if (ir_match_field->match_field().match_type() != MatchField::EXACT &&
        ir_match_field->match_field().match_type() != MatchField::OPTIONAL) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Invalid @refers_to annotation: Only exact and optional "
                "match fields can be used.";
    }
  }

  // Validate that tables which designate an action profile implementation are
  // designated as valid tables in that action profile.
  for (const auto &[table_id, table] : info.tables_by_id()) {
    if (table.implementation_id_case() == IrTableDefinition::kActionProfileId) {
      ASSIGN_OR_RETURN(const auto &ir_action_profile,
                       gutil::FindOrStatus(info.action_profiles_by_id(),
                                           table.action_profile_id()),
                       _ << "Implementation id '" << table.action_profile_id()
                         << "' referenced in table '"
                         << table.preamble().alias()
                         << "' is not an action profile.");
      const auto &profile = ir_action_profile.action_profile();
      if (!absl::c_linear_search(profile.table_ids(), table_id)) {
        return gutil::InvalidArgumentErrorBuilder()
               << "The action profile '" << profile.preamble().alias()
               << "' given as implementation id '" << table.action_profile_id()
               << "' by table '" << table.preamble().alias() << "' (id = '"
               << table_id << "') does not contain '" << table_id
               << "' in its table_ids: "
               << absl::StrJoin(profile.table_ids(), ",");
      }
    }
  }

  // Validate that action profiles which designate table_ids are implemented by
  // those tables.
  for (const auto &[action_profile_id, ir_action_profile] :
       info.action_profiles_by_id()) {
    const auto &profile = ir_action_profile.action_profile();
    for (uint32_t table_id : profile.table_ids()) {
      ASSIGN_OR_RETURN(
          const auto &table, gutil::FindOrStatus(info.tables_by_id(), table_id),
          _ << "Table id '" << table_id << "' referenced in action profile '"
            << profile.preamble().alias() << "' is not a table.");
      if (!(table.implementation_id_case() ==
            IrTableDefinition::kActionProfileId) ||
          table.action_profile_id() != action_profile_id) {
        return gutil::InvalidArgumentErrorBuilder()
               << "The table '" << table.preamble().alias()
               << "' given as table id '" << table_id << "' by action profile '"
               << profile.preamble().alias() << "' (id = '" << action_profile_id
               << "') implements id '" << table.action_profile_id() << "' != '"
               << action_profile_id << "'.";
      }
    }
  }

  return info;
}

StatusOr<IrTableEntry> PiTableEntryToIr(const IrP4Info &info,
                                        const p4::v1::TableEntry &pi,
                                        TranslationOptions options) {
  IrTableEntry ir;
  const auto &status_or_table =
      gutil::FindPtrOrStatus(info.tables_by_id(), pi.table_id());
  if (!status_or_table.ok()) {
    return absl::InvalidArgumentError(absl::StrCat(
        "Table ID ", pi.table_id(), " does not exist in the P4Info."));
  }
  const auto *table = *status_or_table;
  ir.set_table_name(table->preamble().alias());
  absl::string_view table_name = ir.table_name();
  std::vector<std::string> invalid_reasons;

  if (table->is_unsupported() && !options.allow_unsupported) {
    invalid_reasons.push_back(absl::StrCat(kNewBullet, "Table '", table_name,
                                           "' has @unsupported annotation."));
  }

  // Validate and translate the matches
  absl::flat_hash_set<uint32_t> used_field_ids;
  absl::flat_hash_set<std::string> mandatory_matches;
  for (const auto &pi_match : pi.match()) {
    const absl::Status &duplicate = gutil::InsertIfUnique(
        used_field_ids, pi_match.field_id(),
        absl::StrCat("Duplicate match field found with ID ",
                     pi_match.field_id(), "."));
    if (!duplicate.ok()) {
      invalid_reasons.push_back(absl::StrCat(kNewBullet, duplicate.message()));
      continue;
    }

    const auto status_or_match = gutil::FindPtrOrStatus(
        table->match_fields_by_id(), pi_match.field_id());
    if (!status_or_match.ok()) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet, "Match field ", pi_match.field_id(),
                       " does not exist in table '", table_name, "'."));
      continue;
    }
    const auto *match = *status_or_match;
    const absl::StatusOr<IrMatch> &match_entry =
        PiMatchFieldToIr(info, options, *match, pi_match);
    if (!match_entry.ok()) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet, match_entry.status().message()));
      continue;
    }
    *ir.add_matches() = *match_entry;

    if (match->match_field().match_type() == MatchField::EXACT) {
      mandatory_matches.insert(match->match_field().name());
    }
  }

  const absl::Status &mandatory_match_status =
      CheckMandatoryMatches(mandatory_matches, *table);
  if (!mandatory_match_status.ok()) {
    invalid_reasons.push_back(
        absl::StrCat(kNewBullet, mandatory_match_status.message()));
  }

  if (table->requires_priority()) {
    if (pi.priority() <= 0) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet,
                       "Table entries with ternary or optional matches require "
                       "a positive non-zero priority. Got ",
                       pi.priority(), " instead."));
    } else {
      ir.set_priority(pi.priority());
    }
  } else if (pi.priority() != 0) {
    invalid_reasons.push_back(
        absl::StrCat(kNewBullet,
                     "Table entries with no ternary or optional matches cannot "
                     "have a priority. Got ",
                     pi.priority(), " instead."));
  }

  if (!options.key_only) {
    ir.set_controller_metadata(pi.metadata());
    // Validate and translate the action.
    if (table->entry_actions().empty()) {
      if (pi.has_action()) {
        invalid_reasons.push_back(absl::StrCat(
            kNewBullet,
            "Action found for table which has no actions defined."));
      }
    } else {
      if (!pi.has_action()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet, "Action is required."));
      } else {
        switch (pi.action().type_case()) {
          case p4::v1::TableAction::kAction: {
            if (table->uses_oneshot()) {
              invalid_reasons.push_back(absl::StrCat(
                  kNewBullet,
                  "Table requires an action set since it uses oneshot. Got "
                  "action instead."));
              break;
            }
            const absl::StatusOr<IrActionInvocation> &ir_action = PiActionToIr(
                info, options, pi.action().action(), table->entry_actions());
            if (!ir_action.ok()) {
              invalid_reasons.push_back(
                  absl::StrCat(kNewBullet, ir_action.status().message()));
              break;
            }
            *ir.mutable_action() = *ir_action;
            break;
          }
          case p4::v1::TableAction::kActionProfileActionSet: {
            if (!table->uses_oneshot()) {
              invalid_reasons.push_back(
                  absl::StrCat(kNewBullet,
                               "Table requires an action since it does not use "
                               "oneshot. Got action set instead."));
              break;
            }
            const absl::StatusOr<IrActionSet> &ir_action_set = PiActionSetToIr(
                info, options, pi.action().action_profile_action_set(),
                table->entry_actions());
            if (!ir_action_set.ok()) {
              invalid_reasons.push_back(
                  absl::StrCat(kNewBullet, ir_action_set.status().message()));
              break;
            }
            *ir.mutable_action_set() = *ir_action_set;
            break;
          }
          default: {
            invalid_reasons.push_back(absl::StrCat(
                kNewBullet,
                "Unsupported action type: ", pi.action().type_case()));
            break;
          }
        }
      }
    }

    // Validate and translate meters.
    if (!table->has_meter() && pi.has_meter_config()) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet,
                       "Table does not have a meter, but table entry "
                       "contained a meter config."));
    } else if (pi.has_meter_config()) {
      ir.mutable_meter_config()->set_cir(pi.meter_config().cir());
      ir.mutable_meter_config()->set_cburst(pi.meter_config().cburst());
      ir.mutable_meter_config()->set_pir(pi.meter_config().pir());
      ir.mutable_meter_config()->set_pburst(pi.meter_config().pburst());
    }

    // Validate and translate meter counter data.
    if (pi.has_meter_counter_data()) {
      if (!table->has_meter()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet,
                         "Table does not support meters, but table entry "
                         "contained a meter counter."));
      }
      if (!pi.has_meter_config()) {
        invalid_reasons.push_back(absl::StrCat(
            kNewBullet,
            "Pi entry does not have a meter config, but table entry "
            "contained a meter counter."));
      }
      if (table->has_meter() && pi.has_meter_config()) {
        *ir.mutable_meter_counter_data() = pi.meter_counter_data();
      }
    }

    // Validate and translate counters.
    if (!table->has_counter() && pi.has_counter_data()) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet,
                       "Table does not have a counter, but table entry "
                       "contained counter data."));
    } else if (pi.has_counter_data()) {
      ir.mutable_counter_data()->set_byte_count(pi.counter_data().byte_count());
      ir.mutable_counter_data()->set_packet_count(
          pi.counter_data().packet_count());
    }
  }

  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        TableName(table_name), absl::StrJoin(invalid_reasons, "\n")));
  }

  return ir;
}

StatusOr<IrReplica> PiReplicaToIr(const IrP4Info &info,
                                  const p4::v1::Replica &pi) {
  IrReplica ir;
  if (pi.port_kind_case() != p4::v1::Replica::kPort) {
    return gutil::InvalidArgumentErrorBuilder()
           << "expected `port` field to be set in Replica, but found < "
           << gutil::PrintShortTextProto(pi) << " >";
  }
  ir.set_port(pi.port());
  ir.set_instance(pi.instance());
  return ir;
}

StatusOr<IrMulticastGroupEntry> PiMulticastGroupEntryToIr(
    const IrP4Info &info, const p4::v1::MulticastGroupEntry &pi,
    TranslationOptions options) {
  IrMulticastGroupEntry ir;
  ir.set_multicast_group_id(pi.multicast_group_id());

  if (options.key_only) {
    return ir;
  }

  absl::flat_hash_map<std::string, absl::flat_hash_set<uint32_t>>
      instances_by_port;
  std::vector<std::string> invalid_reasons;
  for (const auto &replica : pi.replicas()) {
    absl::StatusOr<IrReplica> ir_replica = PiReplicaToIr(info, replica);
    if (!ir_replica.ok()) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet, ir_replica.status().message()));
      continue;
    }
    // Check that {port, instance} pair is unique.
    bool replica_is_unique = instances_by_port[ir_replica->port()]
                                 .insert(ir_replica->instance())
                                 .second;
    if (!replica_is_unique) {
      invalid_reasons.push_back(absl::StrCat(
          kNewBullet,
          "Each replica must have a unique (port, instance)-pair, but found "
          "multiple replicas with pair ('",
          ir_replica->port(), "', ", ir_replica->instance(), ")."));
    }
    *ir.add_replicas() = std::move(*ir_replica);
  }

  if (!invalid_reasons.empty()) {
    return gutil::InvalidArgumentErrorBuilder() << GenerateFormattedError(
               absl::StrCat("MulticastGroupEntry with group id '",
                            pi.multicast_group_id(), "'"),
               absl::StrJoin(invalid_reasons, "\n"));
  }
  return ir;
}

StatusOr<IrPacketReplicationEngineEntry> PiPacketReplicationEngineEntryToIr(
    const IrP4Info &info, const p4::v1::PacketReplicationEngineEntry &pi,
    TranslationOptions options) {
  IrPacketReplicationEngineEntry ir;
  switch (pi.type_case()) {
    case p4::v1::PacketReplicationEngineEntry::kMulticastGroupEntry: {
      ASSIGN_OR_RETURN(
          *ir.mutable_multicast_group_entry(),
          PiMulticastGroupEntryToIr(info, pi.multicast_group_entry(), options));
      break;
    }
    default: {
      return gutil::UnimplementedErrorBuilder()
             << "Only PRE entries of type multicast group entry are supported.";
    }
  }
  return ir;
}

StatusOr<IrPacketIn> PiPacketInToIr(const IrP4Info &info,
                                    const p4::v1::PacketIn &packet) {
  return PiPacketIoToIr<p4::v1::PacketIn, IrPacketIn>(info, "packet-in",
                                                      packet);
}
StatusOr<IrPacketOut> PiPacketOutToIr(const IrP4Info &info,
                                      const p4::v1::PacketOut &packet) {
  return PiPacketIoToIr<p4::v1::PacketOut, IrPacketOut>(info, "packet-out",
                                                        packet);
}

StatusOr<IrReadRequest> PiReadRequestToIr(
    const IrP4Info &info, const p4::v1::ReadRequest &read_request) {
  IrReadRequest result;
  std::vector<std::string> invalid_reasons;
  if (read_request.device_id() == 0) {
    return InvalidArgumentErrorBuilder() << "Device ID missing.";
  }
  result.set_device_id(read_request.device_id());
  std::string base = "Only wildcard reads of all table entries are supported. ";
  if (read_request.entities().size() != 1) {
    return UnimplementedErrorBuilder()
           << base << "Only 1 entity is supported. Found "
           << read_request.entities().size() << " entities in read request.";
  }
  if (!read_request.entities(0).has_table_entry()) {
    invalid_reasons.push_back(absl::StrCat(
        kNewBullet, base, "Found an entity that is not a table entry."));
  }
  const p4::v1::TableEntry entry = read_request.entities(0).table_entry();
  if (entry.table_id() != 0 || entry.priority() != 0 ||
      entry.controller_metadata() != 0 || entry.idle_timeout_ns() != 0 ||
      entry.is_default_action() || !entry.metadata().empty() ||
      entry.has_action() || entry.has_time_since_last_hit() ||
      !entry.match().empty()) {
    invalid_reasons.push_back(
        absl::StrCat(kNewBullet, base,
                     "At least one field (other than counter_data and "
                     "meter_config is set in the table entry."));
  }
  if (entry.has_meter_config()) {
    if (entry.meter_config().ByteSizeLong() != 0) {
      invalid_reasons.push_back(absl::StrCat(
          kNewBullet, base, "Found a non-empty meter_config in table entry."));
    }
    result.set_read_meter_configs(true);
  }
  if (entry.has_counter_data()) {
    if (entry.counter_data().ByteSizeLong() != 0) {
      invalid_reasons.push_back(absl::StrCat(
          kNewBullet, base, "Found a non-empty counter_data in table entry."));
    }
    result.set_read_counter_data(true);
  }

  if (!invalid_reasons.empty()) {
    return absl::UnimplementedError(GenerateFormattedError(
        "Read request", absl::StrJoin(invalid_reasons, "\n")));
  }
  return result;
}

StatusOr<IrEntity> PiEntityToIr(const IrP4Info &info, const p4::v1::Entity &pi,
                                TranslationOptions options) {
  IrEntity ir_entity;
  switch (pi.entity_case()) {
    case p4::v1::Entity::kTableEntry: {
      ASSIGN_OR_RETURN(*ir_entity.mutable_table_entry(),
                       PiTableEntryToIr(info, pi.table_entry(), options));
      break;
    }
    case p4::v1::Entity::kPacketReplicationEngineEntry: {
      ASSIGN_OR_RETURN(
          *ir_entity.mutable_packet_replication_engine_entry(),
          PiPacketReplicationEngineEntryToIr(
              info, pi.packet_replication_engine_entry(), options));
      break;
    }
    default: {
      auto entity_name = gutil::GetOneOfFieldName(pi, "entity");
      if (!entity_name.ok()) {
        return absl::InvalidArgumentError(
            GenerateFormattedError("Entity", entity_name.status().message()));
      }
      return absl::UnimplementedError(GenerateFormattedError(
          "Entity",
          absl::StrCat("Entity '", *entity_name, "' is not supported.")));
    }
  }
  return ir_entity;
}

StatusOr<IrEntities> PiEntitiesToIr(const IrP4Info &info,
                                    const absl::Span<const p4::v1::Entity> pi,
                                    TranslationOptions options) {
  IrEntities ir_entities;
  for (auto &entity : pi) {
    ASSIGN_OR_RETURN(*ir_entities.add_entities(),
                     PiEntityToIr(info, entity, options));
  }
  return ir_entities;
}

StatusOr<IrReadResponse> PiReadResponseToIr(
    const IrP4Info &info, const p4::v1::ReadResponse &read_response,
    TranslationOptions options) {
  IrReadResponse result;
  std::vector<std::string> invalid_reasons;
  for (const auto &entity : read_response.entities()) {
    absl::StatusOr<pdpi::IrEntity> ir_entity = PiEntityToIr(info, entity);
    if (!ir_entity.ok()) {
      invalid_reasons.push_back(
          gutil::StableStatusToString(ir_entity.status()));
      continue;
    }
    *result.add_entities() = std::move(*ir_entity);
  }

  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        "Read response", absl::StrJoin(invalid_reasons, "\n")));
  }
  return result;
}

StatusOr<IrUpdate> PiUpdateToIr(const IrP4Info &info,
                                const p4::v1::Update &update,
                                TranslationOptions options) {
  IrUpdate ir_update;
  if (update.type() == p4::v1::Update_Type_UNSPECIFIED) {
    return absl::InvalidArgumentError(
        GenerateFormattedError("Update", "Update type should be specified."));
  }
  ASSIGN_OR_RETURN(*ir_update.mutable_entity(),
                   PiEntityToIr(info, update.entity(), options));
  ir_update.set_type(update.type());
  return ir_update;
}

StatusOr<IrWriteRequest> PiWriteRequestToIr(
    const IrP4Info &info, const p4::v1::WriteRequest &write_request,
    TranslationOptions options) {
  IrWriteRequest ir_write_request;

  std::vector<std::string> invalid_reasons;
  if (write_request.role_id() != 0) {
    invalid_reasons.push_back(absl::StrCat(
        kNewBullet, "Only the default role is supported, but got role ID ",
        write_request.role_id(), " instead."));
  }

  if (write_request.atomicity() !=
      p4::v1::WriteRequest_Atomicity_CONTINUE_ON_ERROR) {
    invalid_reasons.push_back(absl::StrCat(
        kNewBullet, "Only CONTINUE_ON_ERROR is supported for atomicity."));
  }

  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        "Write request", absl::StrJoin(invalid_reasons, "\n")));
  }

  std::vector<std::string> invalid_update_reasons;
  ir_write_request.set_device_id(write_request.device_id());
  if (write_request.election_id().high() > 0 ||
      write_request.election_id().low() > 0) {
    *ir_write_request.mutable_election_id() = write_request.election_id();
  }

  for (int idx = 0; idx < write_request.updates_size(); ++idx) {
    const auto &update = write_request.updates(idx);
    const absl::StatusOr<IrUpdate> &ir_update =
        PiUpdateToIr(info, update, options);
    if (!ir_update.ok()) {
      invalid_update_reasons.push_back(GenerateFormattedError(
          absl::StrCat("updates[", idx, "]"), ir_update.status().message()));
      continue;
    }
    *ir_write_request.add_updates() = *ir_update;
  }

  if (!invalid_update_reasons.empty()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        "Write request", absl::StrJoin(invalid_reasons, "\n")));
  }
  return ir_write_request;
}

StatusOr<IrStreamMessageRequest> PiStreamMessageRequestToIr(
    const IrP4Info &info,
    const p4::v1::StreamMessageRequest &stream_message_request) {
  IrStreamMessageRequest ir_stream_message_request;

  switch (stream_message_request.update_case()) {
    case p4::v1::StreamMessageRequest::kArbitration: {
      *ir_stream_message_request.mutable_arbitration() =
          stream_message_request.arbitration();
      break;
    }
    case p4::v1::StreamMessageRequest::kPacket: {
      ASSIGN_OR_RETURN(*ir_stream_message_request.mutable_packet(),
                       PiPacketOutToIr(info, stream_message_request.packet()));
      break;
    }
    default: {
      return absl::InvalidArgumentError(absl::StrCat(
          "Unsupported update: ",
          stream_message_request.GetDescriptor()
              ->FindFieldByNumber(stream_message_request.update_case())
              ->name(),
          "."));
    }
  }
  return ir_stream_message_request;
}

StatusOr<IrStreamMessageResponse> PiStreamMessageResponseToIr(
    const IrP4Info &info,
    const p4::v1::StreamMessageResponse &stream_message_response) {
  IrStreamMessageResponse ir_stream_message_response;

  switch (stream_message_response.update_case()) {
    case p4::v1::StreamMessageResponse::kArbitration: {
      *ir_stream_message_response.mutable_arbitration() =
          stream_message_response.arbitration();
      break;
    }
    case p4::v1::StreamMessageResponse::kPacket: {
      ASSIGN_OR_RETURN(*ir_stream_message_response.mutable_packet(),
                       PiPacketInToIr(info, stream_message_response.packet()));
      break;
    }
    case p4::v1::StreamMessageResponse::kError: {
      auto pi_error = stream_message_response.error();
      auto *ir_error = ir_stream_message_response.mutable_error();
      auto *ir_status = ir_error->mutable_status();
      ir_status->set_code(pi_error.canonical_code());
      ir_status->set_message(pi_error.message());
      switch (pi_error.details_case()) {
        case p4::v1::StreamError::kPacketOut: {
          ASSIGN_OR_RETURN(
              *ir_error->mutable_packet_out(),
              PiPacketOutToIr(info, pi_error.packet_out().packet_out()));
          break;
        }
        default: {
          return absl::InvalidArgumentError(
              absl::StrCat("Unsupported error detail: ",
                           pi_error.GetDescriptor()
                               ->FindFieldByNumber(pi_error.details_case())
                               ->name(),
                           "."));
        }
      }
      break;
    }
    default: {
      return absl::InvalidArgumentError(absl::StrCat(
          "Unsupported update: ",
          stream_message_response.GetDescriptor()
              ->FindFieldByNumber(stream_message_response.update_case())
              ->name(),
          "."));
    }
  }
  return ir_stream_message_response;
}

absl::StatusOr<std::vector<p4::v1::TableEntry>> IrTableEntriesToPi(
    const IrP4Info &info, const IrTableEntries &ir,
    TranslationOptions options) {
  std::vector<p4::v1::TableEntry> pi;
  pi.reserve(ir.entries_size());
  for (const IrTableEntry &ir_entry : ir.entries()) {
    ASSIGN_OR_RETURN(pi.emplace_back(),
                     IrTableEntryToPi(info, ir_entry, options));
  }
  return pi;
}
absl::StatusOr<std::vector<p4::v1::TableEntry>> IrTableEntriesToPi(
    const IrP4Info &info, absl::Span<const IrTableEntry> ir,
    TranslationOptions options) {
  std::vector<p4::v1::TableEntry> pi;
  pi.reserve(ir.size());
  for (const IrTableEntry &ir_entry : ir) {
    ASSIGN_OR_RETURN(pi.emplace_back(),
                     IrTableEntryToPi(info, ir_entry, options));
  }
  return pi;
}

absl::StatusOr<IrTableEntries> PiTableEntriesToIr(
    const IrP4Info &info, absl::Span<const p4::v1::TableEntry> pi,
    TranslationOptions options) {
  IrTableEntries ir;
  ir.mutable_entries()->Reserve(pi.size());
  for (const auto &pi_entry : pi) {
    ASSIGN_OR_RETURN(*ir.add_entries(),
                     PiTableEntryToIr(info, pi_entry, options));
  }
  return ir;
}

StatusOr<p4::v1::TableEntry> IrTableEntryToPi(const IrP4Info &info,
                                              const IrTableEntry &ir,
                                              TranslationOptions options) {
  p4::v1::TableEntry pi;
  absl::string_view table_name = ir.table_name();
  const auto &status_or_table =
      gutil::FindPtrOrStatus(info.tables_by_name(), ir.table_name());
  if (!status_or_table.ok()) {
    return absl::InvalidArgumentError(
        absl::StrCat(TableName(table_name), " does not exist in the P4Info."));
  }
  const auto *table = *status_or_table;
  pi.set_table_id(table->preamble().id());

  std::vector<std::string> invalid_reasons;

  if (table->is_unsupported() && !options.allow_unsupported) {
    invalid_reasons.push_back(absl::StrCat(kNewBullet, "Table '", table_name,
                                           "' has @unsupported annotation."));
  }

  // Validate and translate the matches
  absl::flat_hash_set<std::string> used_field_names, mandatory_matches;
  for (const auto &ir_match : ir.matches()) {
    const absl::Status &duplicate = gutil::InsertIfUnique(
        used_field_names, ir_match.name(),
        absl::StrCat("Duplicate match field found with name '", ir_match.name(),
                     "'."));
    if (!duplicate.ok()) {
      invalid_reasons.push_back(absl::StrCat(kNewBullet, duplicate.message()));
      continue;
    }

    const auto &status_or_match =
        gutil::FindPtrOrStatus(table->match_fields_by_name(), ir_match.name());
    if (!status_or_match.ok()) {
      invalid_reasons.push_back(absl::StrCat(kNewBullet, "Match Field '",
                                             ir_match.name(),
                                             "' does not exist in table."));
      continue;
    }
    const auto *match = *status_or_match;
    const absl::StatusOr<p4::v1::FieldMatch> &match_entry =
        IrMatchFieldToPi(info, options, *match, ir_match);
    if (!match_entry.ok()) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet, match_entry.status().message()));
      continue;
    }
    *pi.add_match() = *match_entry;

    if (match->match_field().match_type() == MatchField::EXACT) {
      mandatory_matches.insert(match->match_field().name());
    }
  }

  const absl::Status &mandatory_match_status =
      CheckMandatoryMatches(mandatory_matches, *table);
  if (!mandatory_match_status.ok()) {
    invalid_reasons.push_back(
        absl::StrCat(kNewBullet, mandatory_match_status.message()));
  }
  if (table->requires_priority()) {
    if (ir.priority() <= 0) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet,
                       "Table entries with ternary or optional matches require "
                       "a positive non-zero priority. Got ",
                       ir.priority(), " instead."));
    } else {
      pi.set_priority(ir.priority());
    }
  } else if (ir.priority() != 0) {
    invalid_reasons.push_back(
        absl::StrCat(kNewBullet,
                     "Table entries with no ternary or optional "
                     "matches require a zero priority. Got ",
                     ir.priority(), " instead."));
  }
  if (!options.key_only) {
    pi.set_metadata(ir.controller_metadata());

    // Validate and translate the action.
    switch (ir.type_case()) {
      case IrTableEntry::kAction: {
        if (table->uses_oneshot()) {
          invalid_reasons.push_back(
              absl::StrCat(kNewBullet,
                           "Table requires an action set since it uses "
                           "onseshot. Got action instead."));
          break;
        }
        if (table->entry_actions().empty()) {
          invalid_reasons.push_back(absl::StrCat(
              kNewBullet,
              "Action found for table which has no actions defined."));
          break;
        }
        const absl::StatusOr<p4::v1::Action> &pi_action =
            IrActionInvocationToPi(info, options, ir.action(),
                                   table->entry_actions());
        if (!pi_action.ok()) {
          invalid_reasons.push_back(
              absl::StrCat(kNewBullet, pi_action.status().message()));
          break;
        }
        *pi.mutable_action()->mutable_action() = *pi_action;
        break;
      }
      case IrTableEntry::kActionSet: {
        if (!table->uses_oneshot()) {
          invalid_reasons.push_back(
              absl::StrCat(kNewBullet,
                           "Table requires an action since it does not "
                           "use onseshot. Got action set instead."));
          break;
        }
        if (table->entry_actions().empty()) {
          invalid_reasons.push_back(absl::StrCat(
              kNewBullet,
              "Action set found for table which has no actions defined."));
        }
        const absl::StatusOr<p4::v1::ActionProfileActionSet> &pi_action_set =
            IrActionSetToPi(info, options, ir.action_set(),
                            table->entry_actions());
        if (!pi_action_set.ok()) {
          invalid_reasons.push_back(
              absl::StrCat(kNewBullet, pi_action_set.status().message()));
          break;
        }
        *pi.mutable_action()->mutable_action_profile_action_set() =
            *pi_action_set;
        break;
      }
      default: {
        if (!table->entry_actions().empty()) {
          invalid_reasons.push_back(
              absl::StrCat(kNewBullet, "Action is required."));
        }
      }
    }

    // Validate and translate meters.
    if (!table->has_meter() && ir.has_meter_config()) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet,
                       "Table does not have a meter, but table entry "
                       "contained a meter config."));
    } else if (ir.has_meter_config()) {
      pi.mutable_meter_config()->set_cir(ir.meter_config().cir());
      pi.mutable_meter_config()->set_cburst(ir.meter_config().cburst());
      pi.mutable_meter_config()->set_pir(ir.meter_config().pir());
      pi.mutable_meter_config()->set_pburst(ir.meter_config().pburst());
    }

    // Validate and translate meter counter data.
    if (ir.has_meter_counter_data()) {
      if (!table->has_meter()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet,
                         "Table does not support meters but IR entry "
                         "contained a meter counter."));
      }
      if (!ir.has_meter_config()) {
        invalid_reasons.push_back(
            absl::StrCat(kNewBullet,
                         "IR entry does not have a meter config but "
                         "contained a meter counter."));
      }
      if (table->has_meter() && ir.has_meter_config()) {
        *pi.mutable_meter_counter_data() = ir.meter_counter_data();
      }
    }

    // Validate and translate counters.
    if (!table->has_counter() && ir.has_counter_data()) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet,
                       "Table does not have a counter, but table "
                       "entry contained counter data."));
    } else if (ir.has_counter_data()) {
      pi.mutable_counter_data()->set_byte_count(ir.counter_data().byte_count());
      pi.mutable_counter_data()->set_packet_count(
          ir.counter_data().packet_count());
    }
  }

  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        TableName(table_name), absl::StrJoin(invalid_reasons, "\n")));
  }

  return pi;
}

StatusOr<p4::v1::Replica> IrReplicaToPi(const IrP4Info &info,
                                        const IrReplica &ir) {
  p4::v1::Replica pi;
  pi.set_port(ir.port());
  pi.set_instance(ir.instance());
  return pi;
}

StatusOr<p4::v1::MulticastGroupEntry> IrMulticastGroupEntryToPi(
    const IrP4Info &info, const IrMulticastGroupEntry &ir,
    TranslationOptions options) {
  p4::v1::MulticastGroupEntry pi;
  pi.set_multicast_group_id(ir.multicast_group_id());

  if (options.key_only) {
    return pi;
  }

  absl::flat_hash_map<std::string, absl::flat_hash_set<uint32_t>>
      instances_by_port;
  std::vector<std::string> invalid_reasons;
  for (const auto &replica : ir.replicas()) {
    absl::StatusOr<p4::v1::Replica> pi_replica = IrReplicaToPi(info, replica);
    if (!pi_replica.ok()) {
      invalid_reasons.push_back(
          absl::StrCat(kNewBullet, pi_replica.status().message()));
      continue;
    }
    // Check that {port, instance} pair is unique.
    bool replica_is_unique = instances_by_port[pi_replica->port()]
                                 .insert(pi_replica->instance())
                                 .second;
    if (!replica_is_unique) {
      invalid_reasons.push_back(absl::StrCat(
          kNewBullet,
          "Each replica must have a unique (port, instance)-pair, but found "
          "multiple replicas with pair ('",
          pi_replica->port(), "', ", pi_replica->instance(), ")."));
    }
    *pi.add_replicas() = std::move(*pi_replica);
  }
  if (!invalid_reasons.empty()) {
    return gutil::InvalidArgumentErrorBuilder() << GenerateFormattedError(
               absl::StrCat("MulticastGroupEntry with group id '",
                            ir.multicast_group_id(), "'"),
               absl::StrJoin(invalid_reasons, "\n"));
  }
  return pi;
}

StatusOr<p4::v1::PacketReplicationEngineEntry>
IrPacketReplicationEngineEntryToPi(const IrP4Info &info,
                                   const IrPacketReplicationEngineEntry &ir,
                                   TranslationOptions options) {
  p4::v1::PacketReplicationEngineEntry pi;
  switch (ir.type_case()) {
    case IrPacketReplicationEngineEntry::kMulticastGroupEntry: {
      ASSIGN_OR_RETURN(
          *pi.mutable_multicast_group_entry(),
          IrMulticastGroupEntryToPi(info, ir.multicast_group_entry(), options));
      break;
    }
    default:
      return gutil::UnimplementedErrorBuilder()
             << "Only PRE entries of type multicast group entry are supported.";
  }
  return pi;
}

StatusOr<p4::v1::PacketIn> IrPacketInToPi(const IrP4Info &info,
                                          const IrPacketIn &packet) {
  return IrPacketIoToPi<p4::v1::PacketIn, IrPacketIn>(info, "packet-in",
                                                      packet);
}
StatusOr<p4::v1::PacketOut> IrPacketOutToPi(const IrP4Info &info,
                                            const IrPacketOut &packet) {
  return IrPacketIoToPi<p4::v1::PacketOut, IrPacketOut>(info, "packet-out",
                                                        packet);
}

StatusOr<p4::v1::ReadRequest> IrReadRequestToPi(
    const IrP4Info &info, const IrReadRequest &read_request) {
  p4::v1::ReadRequest result;
  if (read_request.device_id() == 0) {
    return UnimplementedErrorBuilder() << "Device ID missing.";
  }
  result.set_device_id(read_request.device_id());
  p4::v1::TableEntry *entry = result.add_entities()->mutable_table_entry();
  if (read_request.read_counter_data()) {
    entry->mutable_counter_data();
  }
  if (read_request.read_meter_configs()) {
    entry->mutable_meter_config();
  }
  return result;
}

StatusOr<p4::v1::Entity> IrEntityToPi(const IrP4Info &info, const IrEntity &ir,
                                      TranslationOptions options) {
  p4::v1::Entity pi_entity;
  switch (ir.entity_case()) {
    case IrEntity::kTableEntry: {
      ASSIGN_OR_RETURN(*pi_entity.mutable_table_entry(),
                       IrTableEntryToPi(info, ir.table_entry(), options));
      break;
    }
    case IrEntity::kPacketReplicationEngineEntry: {
      ASSIGN_OR_RETURN(
          *pi_entity.mutable_packet_replication_engine_entry(),
          IrPacketReplicationEngineEntryToPi(
              info, ir.packet_replication_engine_entry(), options));
      break;
    }
    default: {
      auto entity_name = gutil::GetOneOfFieldName(ir, "entity");
      if (!entity_name.ok()) {
        return absl::InvalidArgumentError(
            GenerateFormattedError("Entity", entity_name.status().message()));
      }
      return absl::UnimplementedError(GenerateFormattedError(
          "Entity",
          absl::StrCat("Entity '", *entity_name, "' is not supported.")));
    }
  }
  return pi_entity;
}

absl::StatusOr<std::vector<p4::v1::Entity>> IrEntitiesToPi(
    const IrP4Info &info, const IrEntities &ir, TranslationOptions options) {
  std::vector<p4::v1::Entity> pi_entities;
  pi_entities.reserve(ir.entities_size());
  for (auto &entity : ir.entities()) {
    ASSIGN_OR_RETURN(pi_entities.emplace_back(),
                     IrEntityToPi(info, entity, options));
  }
  return pi_entities;
}

StatusOr<p4::v1::ReadResponse> IrReadResponseToPi(
    const IrP4Info &info, const IrReadResponse &read_response,
    TranslationOptions options) {
  p4::v1::ReadResponse result;
  std::vector<std::string> invalid_reasons;
  for (const auto &entity : read_response.entities()) {
    absl::StatusOr<p4::v1::Entity> pi_entity = IrEntityToPi(info, entity);
    if (!pi_entity.ok()) {
      invalid_reasons.push_back(
          std::string(gutil::StableStatusToString(pi_entity.status())));
      continue;
    }
    *result.add_entities() = std::move(*pi_entity);
  }

  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        "Read response", absl::StrJoin(invalid_reasons, "\n")));
  }
  return result;
}

StatusOr<p4::v1::Update> IrUpdateToPi(const IrP4Info &info,
                                      const IrUpdate &update,
                                      TranslationOptions options) {
  p4::v1::Update pi_update;

  std::vector<std::string> invalid_reasons;
  if (!p4::v1::Update_Type_IsValid(update.type())) {
    invalid_reasons.push_back(
        absl::StrCat(kNewBullet, "Invalid type value: ", update.type()));
  }
  if (update.type() == p4::v1::Update_Type_UNSPECIFIED) {
    invalid_reasons.push_back(
        absl::StrCat(kNewBullet, "Update type should be specified."));
  }
  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(
        GenerateFormattedError("Update", absl::StrJoin(invalid_reasons, "\n")));
  }

  ASSIGN_OR_RETURN(*pi_update.mutable_entity(),
                   IrEntityToPi(info, update.entity()));

  pi_update.set_type(update.type());
  return pi_update;
}

StatusOr<p4::v1::WriteRequest> IrWriteRequestToPi(
    const IrP4Info &info, const IrWriteRequest &ir_write_request,
    TranslationOptions options) {
  p4::v1::WriteRequest pi_write_request;

  pi_write_request.set_role_id(0);
  pi_write_request.set_atomicity(
      p4::v1::WriteRequest_Atomicity_CONTINUE_ON_ERROR);
  pi_write_request.set_device_id(ir_write_request.device_id());
  if (ir_write_request.election_id().high() > 0 ||
      ir_write_request.election_id().low() > 0) {
    *pi_write_request.mutable_election_id() = ir_write_request.election_id();
  }

  std::vector<std::string> invalid_reasons;
  for (int idx = 0; idx < ir_write_request.updates_size(); ++idx) {
    const auto &update = ir_write_request.updates(idx);
    const absl::StatusOr<p4::v1::Update> &pi_update =
        IrUpdateToPi(info, update, options);
    if (!pi_update.ok()) {
      invalid_reasons.push_back(GenerateFormattedError(
          absl::StrCat("updates[", idx, "]"), pi_update.status().message()));
      continue;
    }
    *pi_write_request.add_updates() = *pi_update;
  }
  if (!invalid_reasons.empty()) {
    return absl::InvalidArgumentError(GenerateFormattedError(
        "Write Request", absl::StrJoin(invalid_reasons, "\n")));
  }
  return pi_write_request;
}

StatusOr<p4::v1::StreamMessageRequest> IrStreamMessageRequestToPi(
    const IrP4Info &info,
    const IrStreamMessageRequest &ir_stream_message_request) {
  p4::v1::StreamMessageRequest pi_stream_message_request;

  switch (ir_stream_message_request.update_case()) {
    case IrStreamMessageRequest::kArbitration: {
      *pi_stream_message_request.mutable_arbitration() =
          ir_stream_message_request.arbitration();
      break;
    }
    case IrStreamMessageRequest::kPacket: {
      ASSIGN_OR_RETURN(
          *pi_stream_message_request.mutable_packet(),
          IrPacketOutToPi(info, ir_stream_message_request.packet()));
      break;
    }
    default: {
      return absl::InvalidArgumentError(absl::StrCat(
          "Unsupported update: ",
          ir_stream_message_request.GetDescriptor()
              ->FindFieldByNumber(ir_stream_message_request.update_case())
              ->name(),
          "."));
    }
  }
  return pi_stream_message_request;
}

StatusOr<p4::v1::StreamMessageResponse> IrStreamMessageResponseToPi(
    const IrP4Info &info,
    const IrStreamMessageResponse &ir_stream_message_response) {
  p4::v1::StreamMessageResponse pi_stream_message_response;

  switch (ir_stream_message_response.update_case()) {
    case IrStreamMessageResponse::kArbitration: {
      *pi_stream_message_response.mutable_arbitration() =
          ir_stream_message_response.arbitration();
      break;
    }
    case IrStreamMessageResponse::kPacket: {
      ASSIGN_OR_RETURN(
          *pi_stream_message_response.mutable_packet(),
          IrPacketInToPi(info, ir_stream_message_response.packet()));
      break;
    }
    case IrStreamMessageResponse::kError: {
      auto *pi_error = pi_stream_message_response.mutable_error();
      auto ir_error = ir_stream_message_response.error();

      pi_error->set_canonical_code(ir_error.status().code());
      pi_error->set_message(ir_error.status().message());

      ASSIGN_OR_RETURN(*pi_error->mutable_packet_out()->mutable_packet_out(),
                       IrPacketOutToPi(info, ir_error.packet_out()));
      break;
    }
    default: {
      return absl::InvalidArgumentError(absl::StrCat(
          "Unsupported update: ",
          ir_stream_message_response.GetDescriptor()
              ->FindFieldByNumber(ir_stream_message_response.update_case())
              ->name(),
          "."));
    }
  }
  return pi_stream_message_response;
}

// Formats a grpc status about write request into a readible string.
std::string WriteRequestGrpcStatusToString(const grpc::Status &status) {
  std::string readable_status = absl::StrCat(
      "gRPC_error_code: ", status.error_code(), "\n",
      "gRPC_error_message: ", "\"", status.error_message(), "\"", "\n");
  if (status.error_details().empty()) {
    absl::StrAppend(&readable_status, "gRPC_error_details: <empty>\n");
  } else {
    google::rpc::Status inner_status;
    if (inner_status.ParseFromString(status.error_details())) {
      absl::StrAppend(&readable_status, "details in google.rpc.Status:\n",
                      "inner_status.code:", inner_status.code(),
                      "\n"
                      "inner_status.message:\"",
                      inner_status.message(), "\"\n",
                      "inner_status.details:\n");
      p4::v1::Error p4_error;
      for (const auto &inner_status_detail : inner_status.details()) {
        absl::StrAppend(&readable_status, "  ");
        if (inner_status_detail.UnpackTo(&p4_error)) {
          absl::StrAppend(
              &readable_status, "error_status: ",
              absl::StatusCodeToString(
                  static_cast<absl::StatusCode>(p4_error.canonical_code())));
          absl::StrAppend(&readable_status, " error_message: ", "\"",
                          p4_error.message(), "\"", "\n");
        } else {
          absl::StrAppend(&readable_status, "<Can not unpack p4error>\n");
        }
      }
    } else {
      absl::StrAppend(&readable_status,
                      "<Can not parse google::rpc::status>\n");
    }
  }
  return readable_status;
}

absl::StatusOr<IrWriteRpcStatus> GrpcStatusToIrWriteRpcStatus(
    const grpc::Status &grpc_status, int number_of_updates_in_write_request) {
  IrWriteRpcStatus ir_write_status;
  if (grpc_status.ok()) {
    // If all batch updates succeeded, `status` is ok and neither
    // error_message nor error_details is populated. If either error_message
    // or error_details is populated, `status` is ill-formed and should return
    // InvalidArgumentError.
    if (!grpc_status.error_message().empty() ||
        !grpc_status.error_details().empty()) {
      return gutil::InvalidArgumentErrorBuilder()
             << "gRPC status can not be ok and contain an error message or "
                "error details";
    }
    ir_write_status.mutable_rpc_response();
    for (int i = 0; i < number_of_updates_in_write_request; i++) {
      ir_write_status.mutable_rpc_response()->add_statuses()->set_code(
          ::google::rpc::OK);
    }
    return ir_write_status;
  } else if (!grpc_status.ok() && grpc_status.error_details().empty()) {
    // Rpc-wide error
    RETURN_IF_ERROR(
        IsGoogleRpcCode(static_cast<int>(grpc_status.error_code())));
    RETURN_IF_ERROR(ValidateGenericUpdateStatus(
        static_cast<google::rpc::Code>(grpc_status.error_code()),
        grpc_status.error_message()));
    ir_write_status.mutable_rpc_wide_error()->set_code(
        static_cast<int>(grpc_status.error_code()));
    ir_write_status.mutable_rpc_wide_error()->set_message(
        grpc_status.error_message());
    return ir_write_status;
  } else if (grpc_status.error_code() == grpc::StatusCode::UNKNOWN &&
             !grpc_status.error_details().empty()) {
    google::rpc::Status inner_rpc_status;
    if (!inner_rpc_status.ParseFromString(grpc_status.error_details())) {
      return absl::InvalidArgumentError(
          "Can not parse error_details in grpc_status");
    }
    if (inner_rpc_status.code() != static_cast<int>(grpc_status.error_code())) {
      return gutil::InvalidArgumentErrorBuilder()
             << "google::rpc::Status's status code does not match "
                "with status code in grpc_status";
    }

    auto *ir_rpc_response = ir_write_status.mutable_rpc_response();
    p4::v1::Error p4_error;
    bool all_p4_errors_ok = true;
    if (inner_rpc_status.details_size() != number_of_updates_in_write_request) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Number of rpc status in google::rpc::status doesn't match "
                "number_of_update_in_write_request. inner_rpc_status: "
             << inner_rpc_status.details_size()
             << " number_of_updates_in_write_request: "
             << number_of_updates_in_write_request;
    }
    for (const auto &inner_rpc_status_detail : inner_rpc_status.details()) {
      if (!inner_rpc_status_detail.UnpackTo(&p4_error)) {
        return gutil::InvalidArgumentErrorBuilder()
               << "Can not parse google::rpc::Status contained in grpc_status: "
               << PrintTextProto(inner_rpc_status_detail);
      }
      RETURN_IF_ERROR(IsGoogleRpcCode(p4_error.canonical_code()));
      RETURN_IF_ERROR(ValidateGenericUpdateStatus(
          static_cast<google::rpc::Code>(p4_error.canonical_code()),
          p4_error.message()));
      if (p4_error.canonical_code() !=
          static_cast<int>(google::rpc::Code::OK)) {
        all_p4_errors_ok = false;
      }
      IrUpdateStatus *ir_update_status = ir_rpc_response->add_statuses();
      ir_update_status->set_code(
          static_cast<google::rpc::Code>(p4_error.canonical_code()));
      ir_update_status->set_message(p4_error.message());
    }
    if (all_p4_errors_ok) {
      return gutil::InvalidArgumentErrorBuilder()
             << "gRPC status should contain a mixure of successful and failed "
                "update status but all p4 errors are ok";
    }
    return ir_write_status;

  } else {
    return gutil::InvalidArgumentErrorBuilder()
           << "Only rpc-wide error and batch update status formats are "
              "supported for non-ok gRPC status";
  }
}

static absl::StatusOr<grpc::Status> IrWriteResponseToGrpcStatus(
    const IrWriteResponse &ir_write_response) {
  p4::v1::Error p4_error;
  google::rpc::Status inner_rpc_status;
  for (const IrUpdateStatus &ir_update_status : ir_write_response.statuses()) {
    RETURN_IF_ERROR(ValidateGenericUpdateStatus(ir_update_status.code(),
                                                ir_update_status.message()));
    RETURN_IF_ERROR(IsGoogleRpcCode(ir_update_status.code()));
    p4_error.set_canonical_code(static_cast<int>(ir_update_status.code()));
    p4_error.set_message(ir_update_status.message());
    inner_rpc_status.add_details()->PackFrom(p4_error);
  }
  inner_rpc_status.set_code(static_cast<int>(google::rpc::UNKNOWN));

  return grpc::Status(static_cast<grpc::StatusCode>(inner_rpc_status.code()),
                      IrWriteResponseToReadableMessage(ir_write_response),
                      inner_rpc_status.SerializeAsString());
}

absl::StatusOr<grpc::Status> IrWriteRpcStatusToGrpcStatus(
    const IrWriteRpcStatus &ir_write_status) {
  switch (ir_write_status.status_case()) {
    case IrWriteRpcStatus::kRpcResponse: {
      bool all_ir_update_status_ok =
          absl::c_all_of(ir_write_status.rpc_response().statuses(),
                         [](const IrUpdateStatus &ir_update_status) {
                           return ir_update_status.code() == google::rpc::OK;
                         });
      bool ir_update_status_has_no_error_message =
          absl::c_all_of(ir_write_status.rpc_response().statuses(),
                         [](const IrUpdateStatus &ir_update_status) {
                           return ir_update_status.message().empty();
                         });
      if (all_ir_update_status_ok && ir_update_status_has_no_error_message) {
        return grpc::Status(grpc::StatusCode::OK, "");
      } else {
        return IrWriteResponseToGrpcStatus(ir_write_status.rpc_response());
      }
    }
    case IrWriteRpcStatus::kRpcWideError: {
      RETURN_IF_ERROR(IsGoogleRpcCode(ir_write_status.rpc_wide_error().code()));
      if (ir_write_status.rpc_wide_error().code() ==
          static_cast<int>(google::rpc::Code::OK)) {
        return gutil::InvalidArgumentErrorBuilder()
               << "IR rpc-wide error should not have ok status";
      }
      RETURN_IF_ERROR(ValidateGenericUpdateStatus(
          static_cast<google::rpc::Code>(
              ir_write_status.rpc_wide_error().code()),
          ir_write_status.rpc_wide_error().message()));
      return grpc::Status(static_cast<grpc::StatusCode>(
                              ir_write_status.rpc_wide_error().code()),
                          ir_write_status.rpc_wide_error().message());
    }
    case IrWriteRpcStatus::STATUS_NOT_SET:
      break;
  }
  return gutil::InvalidArgumentErrorBuilder()
         << "Invalid IrWriteRpcStatus: " << PrintTextProto(ir_write_status);
}

absl::Status WriteRpcGrpcStatusToAbslStatus(
    const grpc::Status &grpc_status, int number_of_updates_in_write_request) {
  ASSIGN_OR_RETURN(IrWriteRpcStatus write_rpc_status,
                   GrpcStatusToIrWriteRpcStatus(
                       grpc_status, number_of_updates_in_write_request),
                   _.SetPrepend()
                       << "Invalid gRPC status w.r.t. P4RT specification: ");

  switch (write_rpc_status.status_case()) {
    case IrWriteRpcStatus::kRpcWideError: {
      return absl::Status(static_cast<absl::StatusCode>(
                              write_rpc_status.rpc_wide_error().code()),
                          write_rpc_status.rpc_wide_error().message());
    }
    case IrWriteRpcStatus::kRpcResponse: {
      const IrWriteResponse &ir_write_response =
          write_rpc_status.rpc_response();
      bool all_ir_update_status_ok =
          absl::c_all_of(ir_write_response.statuses(),
                         [](const IrUpdateStatus &ir_update_status) {
                           return ir_update_status.code() == google::rpc::OK;
                         });
      return (all_ir_update_status_ok)
                 ? absl::OkStatus()
                 : gutil::UnknownErrorBuilder()
                       << IrWriteResponseToReadableMessage(ir_write_response);
    }
    case IrWriteRpcStatus::STATUS_NOT_SET:
      break;
  }
  return gutil::InternalErrorBuilder()
         << "GrpcStatusToIrWriteRpcStatus returned invalid IrWriteRpcStatus: "
         << PrintTextProto(write_rpc_status);
}

namespace {

template <class Value>
bool IsSupported(const Value &value) {
  return !value.is_unsupported();
}

template <>
bool IsSupported(const pdpi::IrActionReference &value) {
  return !value.action().is_unsupported();
}

template <class Key, class Value>
void RemoveUnsupportedValues(google::protobuf::Map<Key, Value> &map) {
  google::protobuf::Map<Key, Value> tmp;
  for (auto &[key, value] : map) {
    if (IsSupported(value)) tmp.insert({key, std::move(value)});
  }
  map = std::move(tmp);
}
template <class Value>
void RemoveUnsupportedValues(
    google::protobuf::RepeatedPtrField<Value> &values) {
  google::protobuf::RepeatedPtrField<Value> tmp;
  for (auto &value : values) {
    if (IsSupported(value)) tmp.Add(std::move(value));
  }
  values = std::move(tmp);
}

void RemoveUnsupportedTables(IrP4Info &p4_info) {
  RemoveUnsupportedValues(*p4_info.mutable_tables_by_id());
  RemoveUnsupportedValues(*p4_info.mutable_tables_by_name());
}

void RemoveUnsupportedActions(IrP4Info &p4_info) {
  RemoveUnsupportedValues(*p4_info.mutable_actions_by_id());
  RemoveUnsupportedValues(*p4_info.mutable_actions_by_name());
  for (auto &[id, table] : *p4_info.mutable_tables_by_id()) {
    RemoveUnsupportedValues(*table.mutable_entry_actions());
    RemoveUnsupportedValues(*table.mutable_default_only_actions());
  }
  for (auto &[name, table] : *p4_info.mutable_tables_by_name()) {
    RemoveUnsupportedValues(*table.mutable_entry_actions());
    RemoveUnsupportedValues(*table.mutable_default_only_actions());
  }
}

void RemoveUnsupportedMatchFields(IrP4Info &p4_info) {
  for (auto &[id, table] : *p4_info.mutable_tables_by_id()) {
    RemoveUnsupportedValues(*table.mutable_match_fields_by_id());
    RemoveUnsupportedValues(*table.mutable_match_fields_by_name());
  }
  for (auto &[name, table] : *p4_info.mutable_tables_by_name()) {
    RemoveUnsupportedValues(*table.mutable_match_fields_by_id());
    RemoveUnsupportedValues(*table.mutable_match_fields_by_name());
  }
}

}  // namespace

void RemoveUnsupportedEntities(IrP4Info &p4_info) {
  RemoveUnsupportedTables(p4_info);
  RemoveUnsupportedActions(p4_info);
  RemoveUnsupportedMatchFields(p4_info);
}

}  // namespace pdpi
