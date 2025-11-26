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
#ifndef PINS_P4RT_APP_UTILS_IR_BUILDER_H_
#define PINS_P4RT_APP_UTILS_IR_BUILDER_H_

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/strings/string_view.h"
#include "google/protobuf/text_format.h"
#include "p4_pdpi/ir.pb.h"

namespace p4rt_app {

// This file provides builders for constructing pdpi::Ir* protobufs.

class IrActionProfileDefinitionBuilder {
 public:
  IrActionProfileDefinitionBuilder() = default;
  explicit IrActionProfileDefinitionBuilder(
      pdpi::IrActionProfileDefinition action_profile)
      : action_profile_(std::move(action_profile)) {}

  const pdpi::IrActionProfileDefinition& operator()() const {
    return action_profile_;
  }

  IrActionProfileDefinitionBuilder& preamble(absl::string_view preamble_str) {
    google::protobuf::TextFormat::ParseFromString(
        std::string(preamble_str),
        action_profile_.mutable_action_profile()->mutable_preamble());
    return *this;
  }
  IrActionProfileDefinitionBuilder& preamble(
      p4::config::v1::Preamble preamble_proto) {
    *action_profile_.mutable_action_profile()->mutable_preamble() =
        std::move(preamble_proto);
    return *this;
  }
  IrActionProfileDefinitionBuilder& name(absl::string_view name_str) {
    action_profile_.mutable_action_profile()->mutable_preamble()->set_name(
        name_str);
    action_profile_.mutable_action_profile()->mutable_preamble()->set_alias(
        name_str);
    return *this;
  }
  IrActionProfileDefinitionBuilder& id(int id_number) {
    action_profile_.mutable_action_profile()->mutable_preamble()->set_id(
        id_number);
    return *this;
  }

  // Set up the action definition with a static size. Overwrites any previous
  // wcmp_selector_size, max_sum_of_weights, or max_sum_of_members setting.
  IrActionProfileDefinitionBuilder& static_size(int64_t size) {
    action_profile_.mutable_action_profile()->set_size(size);
    action_profile_.mutable_action_profile()->set_max_group_size(0);
    action_profile_.mutable_action_profile()->set_with_selector(false);
    action_profile_.mutable_action_profile()->clear_sum_of_members();
    action_profile_.mutable_action_profile()->clear_sum_of_weights();
    return *this;
  }

  // Set up the action definition with a selector size. Overwrites any previous
  // static_size, max_sum_of_weights, or max_sum_of_members setting.
  IrActionProfileDefinitionBuilder& wcmp_selector_size(int64_t size,
                                                       int max_group_size) {
    action_profile_.mutable_action_profile()->set_size(size);
    action_profile_.mutable_action_profile()->set_max_group_size(
        max_group_size);
    action_profile_.mutable_action_profile()->set_with_selector(true);
    action_profile_.mutable_action_profile()->clear_sum_of_members();
    action_profile_.mutable_action_profile()->clear_sum_of_weights();
    return *this;
  }

  // Set up the action definition with sum-of-weights accounting. Overwrites any
  // previous static_size, wcmp_selector_size, or max_sum_of_members setting.
  IrActionProfileDefinitionBuilder& max_sum_of_weights(int64_t size,
                                                       int max_group_size) {
    action_profile_.mutable_action_profile()->set_size(size);
    action_profile_.mutable_action_profile()->set_with_selector(true);
    action_profile_.mutable_action_profile()->set_max_group_size(
        max_group_size);
    action_profile_.mutable_action_profile()->mutable_sum_of_weights();
    return *this;
  }

  // Set up the action definition with sum-of-members accounting. Overwrites any
  // previous static_size, wcmp_selector_size, or max_sum_of_weights setting.
  IrActionProfileDefinitionBuilder& max_sum_of_members(int64_t size,
                                                       int max_group_size,
                                                       int max_member_weight) {
    action_profile_.mutable_action_profile()->set_size(size);
    action_profile_.mutable_action_profile()->set_with_selector(true);
    action_profile_.mutable_action_profile()->set_max_group_size(
        max_group_size);
    action_profile_.mutable_action_profile()
        ->mutable_sum_of_members()
        ->set_max_member_weight(max_member_weight);
    return *this;
  }
  IrActionProfileDefinitionBuilder& table_ids(std::vector<int> table_ids) {
    for (int table_id : table_ids) {
      action_profile_.mutable_action_profile()->add_table_ids(table_id);
    }
    return *this;
  }

  private:
   pdpi::IrActionProfileDefinition action_profile_;
};


class IrActionDefinitionBuilder {
public:
  IrActionDefinitionBuilder() = default;
  explicit IrActionDefinitionBuilder(pdpi::IrActionDefinition action)
      : action_(std::move(action)) {}

  const pdpi::IrActionDefinition &operator()() const { return action_; }

  IrActionDefinitionBuilder &preamble(absl::string_view preamble_str) {
    google::protobuf::TextFormat::ParseFromString(std::string(preamble_str),
                                                  action_.mutable_preamble());
    return *this;
  }
  IrActionDefinitionBuilder &preamble(p4::config::v1::Preamble preamble_proto) {
    *action_.mutable_preamble() = std::move(preamble_proto);
    return *this;
  }
  IrActionDefinitionBuilder &name(absl::string_view name_str) {
    action_.mutable_preamble()->set_alias(std::string(name_str));
    return *this;
  }
  IrActionDefinitionBuilder& id(int id_number) {
    action_.mutable_preamble()->set_id(id_number);
    return *this;
  }

  IrActionDefinitionBuilder &
  param(p4::config::v1::Action::Param param_proto,
        pdpi::Format format = pdpi::Format::HEX_STRING) {
    pdpi::IrActionDefinition::IrActionParamDefinition param_def;
    *param_def.mutable_param() = std::move(param_proto);
    param_def.set_format(format);
    (*action_.mutable_params_by_id())[param_def.param().id()] = param_def;
    (*action_.mutable_params_by_name())[param_def.param().name()] =
        std::move(param_def);
    return *this;
  }

  IrActionDefinitionBuilder &
  param(absl::string_view param_str,
        pdpi::Format format = pdpi::Format::HEX_STRING) {
    p4::config::v1::Action::Param param_proto;
    google::protobuf::TextFormat::ParseFromString(std::string(param_str),
                                                  &param_proto);
    return param(param_proto, format);
  }

  IrActionDefinitionBuilder &unsupported() {
    action_.set_is_unsupported(true);
    return *this;
  }
  IrActionDefinitionBuilder &supported() {
    action_.set_is_unsupported(false);
    return *this;
  }

private:
  pdpi::IrActionDefinition action_;
};

class IrTableDefinitionBuilder {
public:
  IrTableDefinitionBuilder() = default;
  explicit IrTableDefinitionBuilder(pdpi::IrTableDefinition table)
      : table_(std::move(table)) {}

  const pdpi::IrTableDefinition &operator()() const { return table_; }

  IrTableDefinitionBuilder &preamble(absl::string_view preamble_str) {
    google::protobuf::TextFormat::ParseFromString(std::string(preamble_str),
                                                  table_.mutable_preamble());
    return *this;
  }
  IrTableDefinitionBuilder &preamble(p4::config::v1::Preamble preamble_proto) {
    *table_.mutable_preamble() = std::move(preamble_proto);
    return *this;
  }

  IrTableDefinitionBuilder &name(absl::string_view name_str) {
    table_.mutable_preamble()->set_alias(std::string(name_str));
    return *this;
  }
  IrTableDefinitionBuilder& id(int id_number) {
    table_.mutable_preamble()->set_id(id_number);
    return *this;
  }

  IrTableDefinitionBuilder &
  match_field(p4::config::v1::MatchField match_field_proto, pdpi::Format format,
              bool unsupported = false) {
    pdpi::IrMatchFieldDefinition match_field_def;
    *match_field_def.mutable_match_field() = std::move(match_field_proto);
    match_field_def.set_format(format);
    match_field_def.set_is_unsupported(unsupported);
    (*table_.mutable_match_fields_by_id())[match_field_def.match_field().id()] =
        match_field_def;
    (*table_.mutable_match_fields_by_name())[match_field_def.match_field()
                                                 .name()] =
        std::move(match_field_def);
    return *this;
  }
  IrTableDefinitionBuilder &match_field(absl::string_view match_field_str,
                                        pdpi::Format format,
                                        bool unsupported = false) {
    p4::config::v1::MatchField match_field_proto;
    google::protobuf::TextFormat::ParseFromString(std::string(match_field_str),
                                                  &match_field_proto);
    return match_field(match_field_proto, format, unsupported);
  }

  IrTableDefinitionBuilder &
  entry_action(pdpi::IrActionDefinition action_proto) {
    *table_.add_entry_actions()->mutable_action() = std::move(action_proto);
    return *this;
  }
  IrTableDefinitionBuilder &entry_action(absl::string_view action_str) {
    google::protobuf::TextFormat::ParseFromString(std::string(action_str),
                                                  table_.add_entry_actions());
    return *this;
  }
  IrTableDefinitionBuilder &
  entry_action(const IrActionDefinitionBuilder &builder) {
    *table_.add_entry_actions()->mutable_action() = builder();
    return *this;
  }

  IrTableDefinitionBuilder &
  default_only_action(pdpi::IrActionDefinition action_proto) {
    *table_.add_default_only_actions()->mutable_action() =
        std::move(action_proto);
    return *this;
  }
  IrTableDefinitionBuilder &default_only_action(absl::string_view action_str) {
    google::protobuf::TextFormat::ParseFromString(
        std::string(action_str), table_.add_default_only_actions());
    return *this;
  }
  IrTableDefinitionBuilder &
  default_only_action(const IrActionDefinitionBuilder &builder) {
    *table_.add_default_only_actions()->mutable_action() = builder();
    return *this;
  }

  IrTableDefinitionBuilder &
  const_default_action(pdpi::IrActionDefinition action_proto) {
    *table_.mutable_const_default_action() = std::move(action_proto);
    return *this;
  }
  IrTableDefinitionBuilder &const_default_action(absl::string_view action_str) {
    google::protobuf::TextFormat::ParseFromString(
        std::string(action_str), table_.mutable_const_default_action());
    return *this;
  }
  IrTableDefinitionBuilder &
  const_default_action(const IrActionDefinitionBuilder &builder) {
    *table_.mutable_const_default_action() = builder();
    return *this;
  }

  IrTableDefinitionBuilder &size(uint32_t table_size) {
    table_.set_size(table_size);
    return *this;
  }
  IrTableDefinitionBuilder &
  counter_unit(p4::config::v1::CounterSpec::Unit unit) {
    table_.mutable_counter()->set_unit(unit);
    return *this;
  }
  IrTableDefinitionBuilder &meter_unit(p4::config::v1::MeterSpec::Unit unit) {
    table_.mutable_meter()->set_unit(unit);
    return *this;
  }
  IrTableDefinitionBuilder &unsupported() {
    table_.set_is_unsupported(true);
    return *this;
  }
  IrTableDefinitionBuilder &supported() {
    table_.set_is_unsupported(false);
    return *this;
  }
  std::string GetTableAsTextProto() const {
    std::string textproto;
    google::protobuf::TextFormat::PrintToString(table_, &textproto);
    return textproto;
  }

private:
  pdpi::IrTableDefinition table_;
};

// Currently only supports the following P4Info fields:
//   tables_by_name
//   tables_by_id
//   actions_by_name
//   actions_by_id
//   action_profiles_by_name
//   action_profiles_by_id
class IrP4InfoBuilder {
public:
  IrP4InfoBuilder() = default;
  explicit IrP4InfoBuilder(pdpi::IrP4Info p4info)
      : p4info_(std::move(p4info)) {}

  const pdpi::IrP4Info &operator()() const { return p4info_; }

  IrP4InfoBuilder& table(pdpi::IrTableDefinition ir_table);
  IrP4InfoBuilder &action(pdpi::IrActionDefinition ir_action) {
    if (ir_action.preamble().id() == 0) {
      ir_action.mutable_preamble()->set_id(++action_id_);
    }
    (*p4info_.mutable_actions_by_id())[ir_action.preamble().id()] = ir_action;
    (*p4info_.mutable_actions_by_name())[ir_action.preamble().alias()] =
        std::move(ir_action);
    return *this;
  }

  IrP4InfoBuilder &table(const IrTableDefinitionBuilder &builder) {
    return table(builder());
  }

  IrP4InfoBuilder &action(const IrActionDefinitionBuilder &builder) {
    return action(builder());
  }

  IrP4InfoBuilder& action_profile(
      pdpi::IrActionProfileDefinition ir_action_profile);
  IrP4InfoBuilder& action_profile(
      const IrActionProfileDefinitionBuilder& builder) {
    return action_profile(builder());
  }
private:
  pdpi::IrP4Info p4info_;
  // Current ID numbers for ID auto-generation.
  int table_id_ = 0;
  int action_id_ = 0;
  int action_profile_id_ = 0;

  // Map of action-profile associations to be processed when the table is
  // installed.
  absl::flat_hash_map<int, int> action_profile_associations_;
};

} // namespace p4rt_app

#endif // PINS_P4RT_APP_UTILS_IR_BUILDER_H_
