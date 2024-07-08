#ifndef PINS_P4_PDPI_REFERENCE_ANNOTATIONS_H_
#define PINS_P4_PDPI_REFERENCE_ANNOTATIONS_H_

#include <string>
#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "google/protobuf/repeated_ptr_field.h"
#include "p4_pdpi/ir.pb.h"

namespace pdpi {

// Parsed contents of an `@refers_to(table, field)` annotation.
struct ParsedRefersToAnnotation {
  std::string table;
  std::string field;
};

// Contents of an `@reference_by(table, field)` annotation.
struct ParsedReferencedByAnnotation {
  std::string table;
  std::string field;
};

// Returns a list of `IrTableReferences` parsed from all @refers_to and
// @referenced by annotations in `info`.
// Returns InvalidArgumentError if:
//   - there are references to/from non-existing table/fields
//   - an @reference_by annotation that can be represented as an @refer_to
//     annotation. @referenced_by should only be used for built-ins
// Returns UnimplementedError if:
//   - there is a reference to an action
//   - there is a reference involving a match field whose type is not `EXACT`
absl::StatusOr<std::vector<IrTableReference>> ParseIrTableReferences(
    const IrP4Info &info);

// Returns a list of `RefersToAnnotation` parsed from the `annotations`.
// Returns empty list if no annotation contained the label `@refers_to`.
// Return InvalidArgument if any annotation with the label `@refers_to` did not
// contain exactly 2 arguments.
absl::StatusOr<std::vector<ParsedRefersToAnnotation>>
ParseAllRefersToAnnotations(
    const google::protobuf::RepeatedPtrField<std::string> &annotations);

// Returns a list of `ReferencedByAnnotation`s parsed from the `annotations`.
// Returns empty list if no annotation contained the label `@referenced_by`.
// Return InvalidArgument if any annotation with the label `@referenced_by` did
// not contain exactly 2 arguments.
absl::StatusOr<std::vector<ParsedReferencedByAnnotation>>
ParseAllReferencedByAnnotations(
    const google::protobuf::RepeatedPtrField<std::string> &annotations);

// Returns an `IrField` created from an @refers_to annotation. Returns error
// if annotation has invalid information or is a reference to an action.
absl::StatusOr<IrField> CreateIrFieldFromRefersTo(
    const ParsedRefersToAnnotation &annotation, const IrP4Info &info);

// Returns an `IrField` created from an @referenced_by annotation. Returns
// error if annotation has invalid information or if the information can be
// captured by an @refers_to annotation (this is an opinionated choice we make
// to steer users towards using @refers_to over @referenced_by when possible).
absl::StatusOr<IrField> CreateIrFieldFromReferencedBy(
    const ParsedReferencedByAnnotation &annotation, const IrP4Info &info);

// Returns an `IrTable` corresponding to `table_name`. `table_name` can be a
// user-defined or built-in table. Return error if `table_name` does not exist.
absl::StatusOr<IrTable> CreateIrTable(absl::string_view table_name,
                                      const IrP4Info &info);

// Returns the `IrBuiltInField` named by `field_name`, or an error if
// `table_name` does not name a built-in table containing a field named
// `field_name`.
absl::StatusOr<IrBuiltInField> CreateIrBuiltInField(
    absl::string_view table_name, absl::string_view field_name);

// Returns an `IrMatchField` whose name and ID are from the definition of
// `field_name` in `table_name` in `info`. Returns error if `table_name` or
// `field_name` do not exist in `info`.
absl::StatusOr<IrMatchField> CreateIrMatchField(absl::string_view table_name,
                                                absl::string_view field_name,
                                                const IrP4Info &info);

// Returns an `IrActionField` whose name and ID are from the definition of
// `param_name` in `action_name` in `info`. Returns error if `action_name` or
// `param_name` do not exist in `info`.
absl::StatusOr<IrActionField> CreateIrActionField(absl::string_view action_name,
                                                  absl::string_view param_name,
                                                  const IrP4Info &info);

}  // namespace pdpi

#endif  // PINS_P4_PDPI_REFERENCE_ANNOTATIONS_H_
