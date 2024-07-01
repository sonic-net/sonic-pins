#ifndef PINS_P4_PDPI_REFERENCE_ANNOTATIONS_H_
#define PINS_P4_PDPI_REFERENCE_ANNOTATIONS_H_

#include <string>
#include <vector>

#include "absl/status/statusor.h"
#include "google/protobuf/repeated_ptr_field.h"

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

// Returns a list of `RefersToAnnotation` parsed from the `annotations`.
// Returns empty list if no annotation contained the label `@refers_to`.
// Return InvalidArgument if any annotation with the label `@refers_to` did not
// contain exactly 2 arguments.
absl::StatusOr<std::vector<ParsedRefersToAnnotation>>
ParseAllRefersToAnnotations(
    const google::protobuf::RepeatedPtrField<std::string>& annotations);

// Returns a list of `ReferencedByAnnotation`s parsed from the `annotations`.
// Returns empty list if no annotation contained the label `@referenced_by`.
// Return InvalidArgument if any annotation with the label `@referenced_by` did
// not contain exactly 2 arguments.
absl::StatusOr<std::vector<ParsedReferencedByAnnotation>>
ParseAllReferencedByAnnotations(
    const google::protobuf::RepeatedPtrField<std::string>& annotations);

}  // namespace pdpi

#endif  // PINS_P4_PDPI_REFERENCE_ANNOTATIONS_H_
