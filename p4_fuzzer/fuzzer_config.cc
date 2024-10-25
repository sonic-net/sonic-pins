#include "p4_fuzzer/fuzzer_config.h"

#include <string>

#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "google/protobuf/repeated_ptr_field.h"
#include "gutil/status.h"  // IWYU pragma: keep
#include "gutil/status.h"
#include "p4_constraints/backend/constraint_info.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/reference_annotations.h"

namespace p4_fuzzer {
namespace {

// TODO: b/317402124, b/263309221 - Remove once assumptions are no longer
// needed. Checks the following assumptions made about table references:
// 1) No reference includes both a match field and an action parameter. This
// simplifies the implementation by allowing each to be independently fuzzed.
// 2) No single field contains 2 or more references. This simplifies the
// implementation by avoiding implicit dependencies between fields.
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

absl::Status FuzzerConfig::SetP4Info(const p4::config::v1::P4Info& info) {
  ASSIGN_OR_RETURN(this->ir_info_, pdpi::CreateIrP4Info(info));
  ASSIGN_OR_RETURN(this->constraint_info_,
                   p4_constraints::P4ToConstraintInfo(info));
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
    const p4::config::v1::P4Info& info) {
  FuzzerConfig config;
  RETURN_IF_ERROR(config.SetP4Info(info));
  return config;
}

}  // namespace p4_fuzzer
