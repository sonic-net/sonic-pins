#include "p4_pdpi/reference_annotations.h"

#include <string>

#include "absl/status/status.h"
#include "absl/strings/substitute.h"
#include "gmock/gmock.h"
#include "google/protobuf/repeated_ptr_field.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"

namespace pdpi {
namespace {

using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::ElementsAre;

// -- Matchers -----------------------------------------------------------------

MATCHER_P2(HasTableAndField, table, field,
           absl::Substitute("Matches: [table: $0, field: $1]", table, field)) {
  return arg.table == table && arg.field == field;
}

// -- Tests --------------------------------------------------------------------

TEST(ParseAllRefersToAnnotationArgs, ReturnsAllRefersToAnnotations) {
  google::protobuf::RepeatedPtrField<std::string> annotations;
  annotations.Add("@refers_to(a,b)");
  annotations.Add("@referenced_by(c,d)");
  annotations.Add("@refers_to(\n        e,f  \t)");
  EXPECT_THAT(ParseAllRefersToAnnotations(annotations),
              IsOkAndHolds(ElementsAre(HasTableAndField("a", "b"),
                                       HasTableAndField("e", "f"))));
}

TEST(ParseAllRefersToAnnotationArgs,
     FailsWithRefersToWithMoreThanTwoArguments) {
  google::protobuf::RepeatedPtrField<std::string> annotations;
  annotations.Add("@refers_to(a,b,c)");
  EXPECT_THAT(ParseAllRefersToAnnotations(annotations),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(ParseAllReferencedByAnnotationArgs, ReturnsAllRefersToAnnotations) {
  google::protobuf::RepeatedPtrField<std::string> annotations;
  annotations.Add("@referenced_by(a,b)");
  annotations.Add("@refers_to(c,d)");
  annotations.Add("@referenced_by(\n        e,f  \t)");
  EXPECT_THAT(ParseAllReferencedByAnnotations(annotations),
              IsOkAndHolds(ElementsAre(HasTableAndField("a", "b"),
                                       HasTableAndField("e", "f"))));
}

TEST(ParseAllReferencedByAnnotationArgs,
     FailsWithReferencedByWithMoreThanTwoArguments) {
  google::protobuf::RepeatedPtrField<std::string> annotations;
  annotations.Add("@referenced_by(a,b,c)");
  EXPECT_THAT(ParseAllReferencedByAnnotations(annotations),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

}  // namespace
}  // namespace pdpi
