#include "p4_pdpi/reference_annotations.h"

#include <string>
#include <vector>

#include "absl/status/statusor.h"
#include "google/protobuf/repeated_ptr_field.h"
#include "gutil/status.h"
#include "p4_pdpi/utils/annotation_parser.h"

namespace pdpi {

using google::protobuf::RepeatedPtrField;

namespace {

absl::StatusOr<ParsedRefersToAnnotation> ParseAsRefersToAnnotation(
    std::string body) {
  ASSIGN_OR_RETURN(auto arg_list, annotation::ParseAsArgList(body));
  if (arg_list.size() != 2) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Invalid argument. Expected 2 args, but got " << arg_list.size();
  }
  return ParsedRefersToAnnotation{.table = arg_list[0], .field = arg_list[1]};
}

absl::StatusOr<ParsedReferencedByAnnotation> ParseAsReferencedByAnnotation(
    std::string body) {
  ASSIGN_OR_RETURN(auto arg_list, annotation::ParseAsArgList(body));
  if (arg_list.size() != 2) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Invalid argument. Expected 2 args, but got " << arg_list.size();
  }
  return ParsedReferencedByAnnotation{.table = arg_list[0],
                                      .field = arg_list[1]};
}

}  // namespace

absl::StatusOr<std::vector<ParsedRefersToAnnotation>>
ParseAllRefersToAnnotations(const RepeatedPtrField<std::string>& annotations) {
  return GetAllParsedAnnotations<ParsedRefersToAnnotation>(
      "refers_to", annotations, ParseAsRefersToAnnotation);
}

absl::StatusOr<std::vector<ParsedReferencedByAnnotation>>
ParseAllReferencedByAnnotations(
    const RepeatedPtrField<std::string>& annotations) {
  return GetAllParsedAnnotations<ParsedReferencedByAnnotation>(
      "referenced_by", annotations, ParseAsReferencedByAnnotation);
}
}  // namespace pdpi
