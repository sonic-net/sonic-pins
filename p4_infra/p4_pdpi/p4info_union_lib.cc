// Copyright 2025 Google LLC
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

#include "p4_infra/p4_pdpi/p4info_union_lib.h"

#include <algorithm>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/types/optional.h"
#include "absl/types/span.h"
#include "google/protobuf/descriptor.h"
#include "google/protobuf/message.h"
#include "google/protobuf/util/message_differencer.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/config/v1/p4types.pb.h"

namespace pdpi {
namespace {
// Checks if `infos` contains any field that is not supported by UnionP4Info,
// such as Extern.
absl::Status ContainsUnsupportedField(
    const std::vector<p4::config::v1::P4Info>& infos) {
  for (const auto& info : infos) {
    if (!info.externs().empty()) {
      return absl::UnimplementedError(
          "UnionP4Info can not union Extern field.");
    }
  }
  return absl::OkStatus();
}

// Returns the id of the given `p4info.proto` Message (e.g. `Table`, `Action`,
// etc.) The generic implementation expects the message to contain a preamble,
// which contains an id. Messages without preambles have specialized
// implementations given below.
template <typename T>
uint32_t GetId(const T& field) {
  return field.preamble().id();
}
uint32_t GetId(const p4::config::v1::MatchField& field) { return field.id(); }
uint32_t GetId(const p4::config::v1::ActionRef& field) { return field.id(); }
uint32_t GetId(const p4::config::v1::Preamble& field) { return field.id(); }
uint32_t GetId(
    const p4::config::v1::ControllerPacketMetadata::Metadata& field) {
  return field.id();
}
uint32_t GetId(const p4::config::v1::Action::Param& field) {
  return field.id();
}

// Checks if two messages are equal, returning their diff otherwise.
absl::optional<std::string> DiffMessages(
    const google::protobuf::Message& message1,
    const google::protobuf::Message& message2,
    absl::Span<const std::string> ignored_fields = {}) {
  std::string diff_result;
  google::protobuf::util::MessageDifferencer differencer;
  differencer.ReportDifferencesToString(&diff_result);
  for (const auto& field_name : ignored_fields) {
    differencer.IgnoreField(
        message1.GetDescriptor()->FindFieldByName(field_name));
  }
  if (differencer.Compare(message1, message2)) {
    return absl::nullopt;
  } else {
    return diff_result;
  }
}

// Asserts that the ids of two fields are equal returning an InternalError
// otherwise. The error should be unreachable code unless something has gone
// horribly wrong.
template <typename T>
absl::Status AssertIdsAreEqualForUnioning(const T& field1, const T& field2) {
  // We throw an internal error here, rather than an InvalidArgumentError, to
  // signal that this is a catastrophic failure, which should be unreachable
  // code. The function has been used incorrectly in a way suggesting that the
  // library is wrong, rather than the p4infos given to its entry function.
  if (GetId(field1) != GetId(field2)) {
    return absl::InternalError(absl::Substitute(
        "attempted to union fields of type $0 with different ids: $1 and $2",
        field1.GetDescriptor()->name(), GetId(field1), GetId(field2)));
  }
  return absl::OkStatus();
}

// Checks that two tables are compatible with one another, returning an
// InvalidArgumentError otherwise. For tables, their id,
// const_default_action_id, implementation_id, size, idle_timeout_behavior, and
// is_const_table should be equal.
// CAUTION: It is always a critical error to call this function on two tables
// without the same id. This will give you an internal error signaling that
// something has gone horribly wrong.
// Requires: GetId(table1) == GetId(table2)
absl::Status AssertTableCompatibility(const p4::config::v1::Table& table1,
                                      const p4::config::v1::Table& table2) {
  // This function should only ever get called if the two tables have the
  // same id.
  RETURN_IF_ERROR(AssertIdsAreEqualForUnioning(table1, table2));

  if (auto diff_result =
          DiffMessages(table1, table2,
                       /*ignored_fields=*/
                       {"preamble", "match_fields", "action_refs",
                        "direct_resource_ids", "other_properties", "size"});
      diff_result.has_value()) {
    return absl::InvalidArgumentError(absl::StrCat(
        "tables were incompatible. Relevant differences: ", *diff_result));
  }

  return absl::OkStatus();
}

// Checks that two preambles are 'compatible' with one another returning an
// InvalidArgumentError otherwise. For preambles, their id, name, alias, and
// documentation should be equal.
// CAUTION: It is always a critical error to call this function on two preambles
// without the same id. This will give you an internal error signaling that
// something has gone horribly wrong.
// Requires: GetId(preamble1) == GetId(preamble2)
absl::Status AssertPreambleCompatibility(
    const p4::config::v1::Preamble& preamble1,
    const p4::config::v1::Preamble& preamble2) {
  // This function should only ever get called if the two preambles have the
  // same id.
  RETURN_IF_ERROR(AssertIdsAreEqualForUnioning(preamble1, preamble2));

  if (auto diff_result = DiffMessages(
          preamble1, preamble2,
          /*ignored_fields=*/
          {"annotations", "annotation_locations", "structured_annotations"});
      diff_result.has_value()) {
    return absl::InvalidArgumentError(absl::StrCat(
        "preambles were incompatible. Relevant differences: ", *diff_result));
  }

  return absl::OkStatus();
}

// Unions `fields` of type T into `unioned_fields` using their ids (as returned
// by GetId) as keys to a map of the rest of their contents. Forward declared
// here because UnionFirstFieldIntoSecondAssertingIdenticalId and
// MapUnionFirstRepeatedFieldIntoSecondById are mutually recursive functions.
template <class T>
absl::Status MapUnionFirstRepeatedFieldIntoSecondById(
    const google::protobuf::RepeatedPtrField<T>& fields,
    google::protobuf::RepeatedPtrField<T>& unioned_fields);

// Unions repeated fields as though they were sets. Barring major changes to PD,
// this should only be the right thing to do for fields without ids. Otherwise,
// use MapUnionFirstRepeatedFieldIntoSecondById. This function should only be
// used when T is a RepeatedField or a RepeatedPtrField, i.e. when there exists
// an X such that T = RepeatedField<X> or T = RepeatedPtrField<X>.
template <typename T>
absl::Status SetUnionFirstRepeatedFieldIntoSecond(const T& fields,
                                                  T& unioned_fields) {
  for (const auto& field : fields) {
    bool field_exists = false;
    for (const auto& unioned_field : unioned_fields) {
      if (field == unioned_field) {
        field_exists = true;
        break;
      }
    }
    if (!field_exists) {
      *unioned_fields.Add() = field;
    }
  }
  return absl::OkStatus();
}

// Unions the `PlatformProperties` fields by taking the max of all respective
// sizes. Returns an InvalidArgumentError if there are unexpected fields.
absl::Status UnionFirstPlatformPropertiesIntoSecond(
    const p4::config::v1::PlatformProperties& properties,
    p4::config::v1::PlatformProperties& unioned_properties) {
  unioned_properties.set_multicast_group_table_size(
      std::max(unioned_properties.multicast_group_table_size(),
               properties.multicast_group_table_size()));
  unioned_properties.set_multicast_group_table_total_replicas(
      std::max(unioned_properties.multicast_group_table_total_replicas(),
               properties.multicast_group_table_total_replicas()));
  unioned_properties.set_multicast_group_table_max_replicas_per_entry(std::max(
      unioned_properties.multicast_group_table_max_replicas_per_entry(),
      properties.multicast_group_table_max_replicas_per_entry()));

  // Ensure only the 3 fields mentioned above are present in either proto.
  std::vector<const google::protobuf::FieldDescriptor*> fields;
  unioned_properties.GetReflection()->ListFields(unioned_properties, &fields);
  if (fields.size() <= 3) {
    fields.clear();
    unioned_properties.GetReflection()->ListFields(properties, &fields);
  };
  if (fields.size() > 3) {
    return absl::InvalidArgumentError(absl::StrCat(
        "PlatformProperties has unexpected fields: ",
        absl::StrJoin(
            fields, ",",
            [](std::string* out,
               const google::protobuf::FieldDescriptor* field) {
              if (field->name() != "multicast_group_table_size" &&
                  field->name() != "multicast_group_table_total_replicas" &&
                  field->name() ==
                      "multicast_group_table_max_replicas_per_entry") {
                // Only append the unexpected fields.
                return absl::StrAppend(out, field->name());
              }
            })));
  }
  return absl::OkStatus();
}

// Unions `PkgInfo`s by combining their names, versions, and PlatformProperties,
// asserting all other fields are equal and returning InvalidArgumentError if
// that is not the case.
absl::Status UnionFirstPkgInfoIntoSecond(
    const p4::config::v1::PkgInfo& info,
    p4::config::v1::PkgInfo& unioned_info) {
  // Base case.
  if (gutil::IsEmptyProto(unioned_info)) {
    unioned_info = info;
    unioned_info.set_name(absl::StrCat("Union of ", info.name()));
    unioned_info.set_version(absl::StrCat("Versions ", info.version()));
    return absl::OkStatus();
  }

  // Take union of `name` and `version` fields.
  absl::StrAppend(unioned_info.mutable_name(), ", ", info.name());
  absl::StrAppend(unioned_info.mutable_version(), ", ", info.version());

  // Take union of `platform_properties` field.
  if (info.has_platform_properties() ||
      unioned_info.has_platform_properties()) {
    RETURN_IF_ERROR(UnionFirstPlatformPropertiesIntoSecond(
        info.platform_properties(),
        *unioned_info.mutable_platform_properties()));
  }

  // Ensure all other fields are equal.
  if (auto diff = DiffMessages(
          info, unioned_info,
          /*ignored_fields=*/{"name", "version", "platform_properties"});
      diff.has_value()) {
    return absl::InvalidArgumentError(absl::StrCat(
        "PkgInfos are incompatible. Relevant differences: ", *diff));
  }

  return absl::OkStatus();
}

// Unions the annotations as though they were sets. Ignores the
// annotation_locations (since we don't currently need them) and asserts that
// there are no structured_annotations (returning an UnimplementedError
// otherwise). Checks that everything else is equal.
// Requires: GetId(preamble) == GetId(unioned_preamble)
absl::Status UnionFirstPreambleIntoSecondAssertingIdenticalId(
    const p4::config::v1::Preamble& preamble,
    p4::config::v1::Preamble& unioned_preamble) {
  RETURN_IF_ERROR(AssertPreambleCompatibility(preamble, unioned_preamble));

  RETURN_IF_ERROR(SetUnionFirstRepeatedFieldIntoSecond(
      preamble.annotations(), *unioned_preamble.mutable_annotations()));
  // `annotation_locations` are ignored.
  // `structured_annotations` are asserted to be empty.
  if (!preamble.structured_annotations().empty() ||
      !unioned_preamble.structured_annotations().empty()) {
    unioned_preamble.mutable_structured_annotations()->MergeFrom(
        preamble.structured_annotations());
    return absl::UnimplementedError(absl::Substitute(
        "$0 failed since `structured_annotations` was not empty "
        "for a field with id '$1'. `structured_annotations` = '$2'",
        __func__, preamble.id(),
        absl::StrJoin(unioned_preamble.structured_annotations(), ",",
                      [](std::string* out,
                         const p4::config::v1::StructuredAnnotation& element) {
                        return absl::StrAppend(out, element.DebugString());
                      })));
  }

  return absl::OkStatus();
}

// Unions the given two instances of a field, asserting also that their IDs are
// equal. Returns invalid argument error if unioning fails, and internal error
// if the IDs are not equal, since the latter is always a serious programming
// flaw. The default implementation here only allows fields to be exactly equal,
// doing no additional unioning; the function may be specialized for concrete
// fields to implement a more sophisticated unioning logic.
// Requires: GetId(field) == GetId(unioned_field)
template <typename T>
absl::Status UnionFirstFieldIntoSecondAssertingIdenticalId(
    const T& field, const T& unioned_field) {
  // This function should only ever get called if the two fields have the
  // same id.
  RETURN_IF_ERROR(AssertIdsAreEqualForUnioning(field, unioned_field));

  // We fail unless the fields are identical.
  if (auto diff_result = DiffMessages(field, unioned_field);
      diff_result.has_value()) {
    return absl::InvalidArgumentError(absl::Substitute(
        "$0 failed since fields of type '$1' sharing the same id, '$2', were "
        "different: $3",
        __func__, field.GetDescriptor()->name(), GetId(field), *diff_result));
  }
  return absl::OkStatus();
}

// Specializes UnionFirstFieldIntoSecondAssertingIdenticalId for tables. Instead
// of requiring equality for all fields, it unions all repeated fields and the
// preamble. It asserts that other_properties is unset, giving an
// UnimplementedError otherwise.
// Requires: GetId(table) == GetId(unioned_table)
absl::Status UnionFirstFieldIntoSecondAssertingIdenticalId(
    const p4::config::v1::Table& table, p4::config::v1::Table& unioned_table) {
  RETURN_IF_ERROR(AssertTableCompatibility(table, unioned_table)).SetPrepend()
      << absl::Substitute(
             "$0 failed since tables sharing the same id, '$1', were "
             "incompatible: ",
             __func__, GetId(table));

  // Use the max size of any table.
  unioned_table.set_size(std::max(unioned_table.size(), table.size()));
  // For tables, we union their repeated fields and preambles.
  RETURN_IF_ERROR(UnionFirstPreambleIntoSecondAssertingIdenticalId(
      table.preamble(), *unioned_table.mutable_preamble()));
  RETURN_IF_ERROR(MapUnionFirstRepeatedFieldIntoSecondById(
      table.match_fields(), *unioned_table.mutable_match_fields()));
  RETURN_IF_ERROR(MapUnionFirstRepeatedFieldIntoSecondById(
      table.action_refs(), *unioned_table.mutable_action_refs()));
  RETURN_IF_ERROR(SetUnionFirstRepeatedFieldIntoSecond(
      table.direct_resource_ids(),
      *unioned_table.mutable_direct_resource_ids()));
  // `other_properties` is asserted to be unset.
  if (table.has_other_properties() || unioned_table.has_other_properties()) {
    return absl::UnimplementedError(absl::Substitute(
        "$0 failed since `other_properties` was not unset "
        "for a table with id '$1'. `other_properties` = '$2,$3'",
        __func__, GetId(table), table.other_properties().DebugString(),
        unioned_table.other_properties().DebugString()));
  }
  return absl::OkStatus();
}

// Specializes UnionFirstFieldIntoSecondAssertingIdenticalId for actions.
// Instead of requiring equality for all fields, it unions the preamble. This is
// done to allow differing annotations for the same action.
// Requires: GetId(action) == GetId(unioned_action)
absl::Status UnionFirstFieldIntoSecondAssertingIdenticalId(
    const p4::config::v1::Action& action,
    p4::config::v1::Action& unioned_action) {
  RETURN_IF_ERROR(AssertIdsAreEqualForUnioning(action, unioned_action));

  RETURN_IF_ERROR(UnionFirstPreambleIntoSecondAssertingIdenticalId(
      action.preamble(), *unioned_action.mutable_preamble()));

  if (auto diff_result =
          DiffMessages(action, unioned_action, /*ignored_fields=*/{"preamble"});
      diff_result.has_value()) {
    return absl::InvalidArgumentError(
        absl::Substitute("actions with identical id '$0' were incompatible. "
                         "Relevant differences: $1",
                         action.preamble().id(), *diff_result));
  }

  return absl::OkStatus();
}

// Specializes UnionFirstFieldIntoSecondAssertingIdenticalId for action
// Profiles. Instead of requiring equality for all fields, it uses the max of
// the sizes. This is to allow different roles to use different sizes.
// Requires: GetId(action_profile) == GetId(unioned_action_profile)
absl::Status UnionFirstFieldIntoSecondAssertingIdenticalId(
    const p4::config::v1::ActionProfile& action_profile,
    p4::config::v1::ActionProfile& unioned_action_profile) {
  RETURN_IF_ERROR(
      AssertIdsAreEqualForUnioning(action_profile, unioned_action_profile));

  // For all sizes, use the max size of any action profile.
  unioned_action_profile.set_size(
      std::max(unioned_action_profile.size(), action_profile.size()));
  unioned_action_profile.set_max_group_size(
      std::max(unioned_action_profile.max_group_size(),
               action_profile.max_group_size()));

  if (auto diff_result =
          DiffMessages(action_profile, unioned_action_profile,
                       /*ignored_fields=*/{"size", "max_group_size"});
      diff_result.has_value()) {
    return absl::InvalidArgumentError(absl::Substitute(
        "action profiles with identical id '$0' were incompatible. "
        "Relevant differences: $1",
        action_profile.preamble().id(), *diff_result));
  }

  return absl::OkStatus();
}

// Unions `fields` of type T into `unioned_fields` using their ids (as returned
// by GetId) as keys to a map of the rest of their contents.
template <class T>
absl::Status MapUnionFirstRepeatedFieldIntoSecondById(
    const google::protobuf::RepeatedPtrField<T>& fields,
    google::protobuf::RepeatedPtrField<T>& unioned_fields) {
  for (const auto& field : fields) {
    // If a field matching the given field's ID is already in
    // `unioned_fields`, checks that the fields are equal, returning
    // an error with the diff if they're not.
    uint32_t id = GetId(field);
    bool field_with_same_id_exists = false;
    for (auto& unioned_field : unioned_fields) {
      if (GetId(unioned_field) == id) {
        field_with_same_id_exists = true;
        RETURN_IF_ERROR(UnionFirstFieldIntoSecondAssertingIdenticalId(
            field, unioned_field));
        break;
      }
    }
    if (!field_with_same_id_exists) {
      *unioned_fields.Add() = field;
    }
  }
  return absl::OkStatus();
}

// Unions all type_info in `info` into `unioned_info` using the key of
// P4TypeInfo::new_types. Return UnimplementedError if fields other than
// new_types is in type_info of any of `info`
absl::Status UnionFirstTypeInfoIntoSecond(
    const p4::config::v1::P4Info& info, p4::config::v1::P4Info& unioned_info) {
  if (info.type_info().structs_size() != 0 ||
      info.type_info().headers_size() != 0 ||
      info.type_info().header_unions_size() != 0 ||
      info.type_info().enums_size() != 0 || info.type_info().has_error() ||
      info.type_info().serializable_enums_size()) {
    return absl::InvalidArgumentError(absl::Substitute(
        "$0 only supports P4TypeInfo::new_types. P4TypeInfo: $1", __func__,
        info.type_info().DebugString()));
  }
  if (!unioned_info.has_type_info()) {
    *unioned_info.mutable_type_info() = info.type_info();
    return absl::OkStatus();
  }
  for (const auto& [type_name, type_spec] : info.type_info().new_types()) {
    auto it = unioned_info.type_info().new_types().find(type_name);
    if (it != unioned_info.type_info().new_types().end()) {
      if (auto diff_result = DiffMessages(type_spec, it->second);
          diff_result.has_value()) {
        return absl::InvalidArgumentError(absl::Substitute(
            "$0 failed since type specifications sharing the same key, '$1', "
            "were different: $2",
            __func__, it->first, *diff_result));
      }
    } else {
      (*unioned_info.mutable_type_info()->mutable_new_types())[type_name] =
          type_spec;
    }
  }
  return absl::OkStatus();
}

}  // namespace

absl::StatusOr<p4::config::v1::P4Info> UnionP4info(
    const std::vector<p4::config::v1::P4Info>& infos) {
  RETURN_IF_ERROR(ContainsUnsupportedField(infos));

  p4::config::v1::P4Info unioned_info;
  for (const auto& info : infos) {
    RETURN_IF_ERROR(UnionFirstPkgInfoIntoSecond(
        info.pkg_info(), *unioned_info.mutable_pkg_info()));
    RETURN_IF_ERROR(MapUnionFirstRepeatedFieldIntoSecondById(
        info.tables(), *unioned_info.mutable_tables()));
    RETURN_IF_ERROR(MapUnionFirstRepeatedFieldIntoSecondById(
        info.actions(), *unioned_info.mutable_actions()));
    RETURN_IF_ERROR(MapUnionFirstRepeatedFieldIntoSecondById(
        info.action_profiles(), *unioned_info.mutable_action_profiles()));
    RETURN_IF_ERROR(MapUnionFirstRepeatedFieldIntoSecondById(
        info.counters(), *unioned_info.mutable_counters()));
    RETURN_IF_ERROR(MapUnionFirstRepeatedFieldIntoSecondById(
        info.direct_counters(), *unioned_info.mutable_direct_counters()));
    RETURN_IF_ERROR(MapUnionFirstRepeatedFieldIntoSecondById(
        info.meters(), *unioned_info.mutable_meters()));
    RETURN_IF_ERROR(MapUnionFirstRepeatedFieldIntoSecondById(
        info.direct_meters(), *unioned_info.mutable_direct_meters()));
    RETURN_IF_ERROR(MapUnionFirstRepeatedFieldIntoSecondById(
        info.controller_packet_metadata(),
        *unioned_info.mutable_controller_packet_metadata()));
    RETURN_IF_ERROR(MapUnionFirstRepeatedFieldIntoSecondById(
        info.value_sets(), *unioned_info.mutable_value_sets()));
    RETURN_IF_ERROR(MapUnionFirstRepeatedFieldIntoSecondById(
        info.registers(), *unioned_info.mutable_registers()));
    RETURN_IF_ERROR(MapUnionFirstRepeatedFieldIntoSecondById(
        info.digests(), *unioned_info.mutable_digests()));
    RETURN_IF_ERROR(UnionFirstTypeInfoIntoSecond(info, unioned_info));
  }

  return unioned_info;
}
}  // namespace pdpi
