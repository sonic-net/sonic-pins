#include "p4_fuzzer/fuzzer_config.h"

#include <string>
#include <utility>
#include <vector>

#include "absl/container/flat_hash_set.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_split.h"
#include "google/protobuf/repeated_ptr_field.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"  // IWYU pragma: keep
#include "gutil/gutil/status.h"
#include "p4_constraints/ast.h"
#include "p4_constraints/backend/constraint_info.h"
#include "p4_infra/p4_pdpi/ir.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_pdpi/ir_properties.h"
#include "p4_infra/p4_pdpi/reference_annotations.h"

namespace p4_fuzzer {
namespace {

// Checks the following assumptions made about table references:
// TODO: b/317402124 - Remove when match+action references are supported.
// 1) No reference includes both a match field and an action parameter. This
//    simplifies the implementation by allowing each to be independently fuzzed.
// TODO: b/263309221 - Remove when multiple references are supported.
// 2) No single field contains 2 or more references. This simplifies the
//    implementation by avoiding implicit dependencies between fields.
// 3) Only EXACT match fields can have outgoing/incoming references.
absl::Status CheckReferenceAssumptions(
    const google::protobuf::RepeatedPtrField<pdpi::IrTableReference>&
        references) {
  absl::flat_hash_set<std::string> encountered_fields;
  for (const pdpi::IrTableReference& reference : references) {
    bool has_match_reference = false;
    bool has_action_reference = false;
    for (const auto& field_reference : reference.field_references()) {
      switch (field_reference.source().field_case()) {
        case pdpi::IrField::kMatchField: {
          has_match_reference = true;
          break;
        }
        case pdpi::IrField::kActionField: {
          has_action_reference = true;
          break;
        }
        default:
          return gutil::InvalidArgumentErrorBuilder()
                 << "Unknown IrField type in field reference source: "
                 << field_reference.source().DebugString();
      }
      ASSIGN_OR_RETURN(std::string field_name,
                       pdpi::GetNameOfField(field_reference.source()));
      auto [it, fresh] = encountered_fields.insert(field_name);
      // TODO: b/317404235 - Remove once a less "baked-in" way of masking this
      // is found.
      // This is a mask used to maintain the second assumption made in
      // CheckReferenceAssumptions. Some actions contain both @refers_to
      // (router_interface_table, router_interface_id) and @refers_to
      // (neighbor_table, router_interface_id). The neighbor table also
      // contains the former reference, making the information redundant.
      // Therefore only the latter is counted and former is ignored.
      bool masked =
          reference.destination_table().p4_table().table_name() ==
              "router_interface_table" &&
          reference.source_table().p4_table().table_name() != "neighbor_table";

      // Check the second assumption.
      if (!fresh && !masked) {
        ASSIGN_OR_RETURN(std::string table_name,
                         pdpi::GetNameOfTable(reference.source_table()));
        return gutil::AlreadyExistsErrorBuilder()
               << "Multiple references coming from the same field are not "
                  "supported. Field '"
               << field_name << "' in table '" << table_name
               << "' contains multiple references.";
      }
    }

    // Check the first assumption.
    if (has_match_reference && has_action_reference) {
      return gutil::UnimplementedErrorBuilder()
             << "References to a table involving both match fields and action "
                "parameters are not supported.";
    }
  }
  return absl::OkStatus();
}
}  // namespace

absl::StatusOr<std::string> GetFullyQualifiedMatchFieldName(
    const pdpi::IrP4Info& ir_p4info, const std::string& table_name,
    const std::string& match_field_name) {
  // P4Infos in pins_infra have been using the last component of a
  // period-separated fully qualified table name as the table alias and IrP4Info
  // uses table.preamble().alias() to index table definitions.
  std::string table_alias =
      std::vector<std::string>(absl::StrSplit(table_name, '.')).back();
  if (!ir_p4info.tables_by_name().contains(table_alias)) {
    return absl::NotFoundError(absl::StrCat("P4Info ", ir_p4info.DebugString(),
                                            " does not contain table '",
                                            table_name, "'."));
  }
  if (!ir_p4info.tables_by_name()
           .at(table_alias)
           .match_fields_by_name()
           .contains(match_field_name)) {
    return absl::NotFoundError(absl::StrCat("Table '", table_name,
                                            "' does not contain match field '",
                                            match_field_name, "'."));
  }
  return absl::StrCat(table_name, ".", match_field_name);
}
absl::StatusOr<std::string> GetFullyQualifiedMatchFieldName(
    const pdpi::IrTableDefinition& table_def,
    const pdpi::IrMatchFieldDefinition& match_field_def) {
  if (!table_def.match_fields_by_name().contains(
          match_field_def.match_field().name())) {
    return absl::NotFoundError(
        absl::StrCat("Table '", table_def.preamble().name(),
                     "' does not contain match field '",
                     match_field_def.match_field().name(), "'."));
  }
  return absl::StrCat(table_def.preamble().name(), ".",
                      match_field_def.match_field().name());
}

absl::Status FuzzerConfig::CheckConstraintAssumptions() {
  for (const auto& [table_id, table] : ir_info_.tables_by_id()) {
    if (GetIgnoreConstraintsOnTables().contains(table.preamble().name()))
      continue;

    auto* table_constraint_info =
        p4_constraints::GetTableInfoOrNull(constraint_info_, table_id);

    // The constraint info is generated from the p4 info, all ids should be
    // accounted for.
    if (table_constraint_info == nullptr) {
      return gutil::InternalErrorBuilder()
             << "table with ID '" << table.preamble().id()
             << "' does not exist in constraint info: "
             << table.preamble().alias();
    };

    // Ignore tables without constraints.
    if (!table_constraint_info->constraint.has_value()) continue;
    absl::flat_hash_set<std::string> constrained_fields =
        p4_constraints::ast::GetVariables(*table_constraint_info->constraint);

    for (const auto& [match_name, match_field] : table.match_fields_by_name()) {
      // Ignore match fields without constraints.
      if (!constrained_fields.contains(match_field.match_field().name()))
        continue;
      if (pdpi::HasP4RuntimeTranslatedType(match_field) &&
          match_field.match_field().match_type() ==
              p4::config::v1::MatchField::EXACT) {
        return gutil::UnimplementedErrorBuilder()
               << "Match field '" << match_name << "' in table '"
               << table.preamble().alias()
               << "' is a P4Runtime translated type, constrained, AND is "
                  "EXACT. P4-Fuzzer cannot generate constrained values for "
                  "this type and exact fields are required so this combination "
                  "is forbidden. Table:\n"
               << gutil::PrintTextProto(table);
      } else if (pdpi::HasP4RuntimeTranslatedType(match_field)) {
        LOG(WARNING) << "Match field '" << match_name << "' in table '"
                     << table.preamble().alias()
                     << "' is a P4Runtime translated type, constrained, and "
                        "omittable. The fuzzer cannot satisfy constraints on "
                        "this type, but valid entries may still be fuzzed if "
                        "this field is omitted when fuzzing.";
      }

      for (const auto& reference : table.outgoing_references()) {
        for (const auto& field_reference : reference.field_references()) {
          if (field_reference.source()
                  .match_field()
                  .p4_match_field()
                  .field_name() == match_name) {
            LOG(WARNING) << "Field '" << match_name << "' in table '"
                         << table.preamble().alias()
                         << "' is both constrained and has a reference. The "
                            "fuzzer will choose to satisfy references over "
                            "constraints, which means the resulting entry may "
                            "not satisfy constraints.";
          }
        }
      }

      // TODO: b/324084334 - Make similar assumptions on action constraints once
      // they are incorporated into the fuzzer.
    }
  }

  return absl::OkStatus();
}

absl::Status FuzzerConfig::SetP4Info(const p4::config::v1::P4Info& info) {
  ASSIGN_OR_RETURN(this->ir_info_, pdpi::CreateIrP4Info(info));
  ASSIGN_OR_RETURN(this->constraint_info_,
                   p4_constraints::P4ToConstraintInfo(info));
  RETURN_IF_ERROR(CheckConstraintAssumptions());
  for (const auto& [unused, table_def] : this->ir_info_.tables_by_id()) {
    RETURN_IF_ERROR(CheckReferenceAssumptions(table_def.outgoing_references()));
  }

  for (const auto& [unused, table_def] : this->ir_info_.built_in_tables()) {
    RETURN_IF_ERROR(CheckReferenceAssumptions(table_def.outgoing_references()));
  }

  this->info_ = info;
  return absl::OkStatus();
}

absl::StatusOr<FuzzerConfig> FuzzerConfig::Create(
    const p4::config::v1::P4Info& info, const ConfigParams params) {
  FuzzerConfig config;
  config.params_ = std::move(params);
  // MUST be called after populating params.
  RETURN_IF_ERROR(config.SetP4Info(info))
      << "Failed to set P4Info: " << gutil::PrintTextProto(info);
  return config;
}

}  // namespace p4_fuzzer
