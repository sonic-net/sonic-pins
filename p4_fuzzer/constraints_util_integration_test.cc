#include <memory>
#include <string>

#include "glog/logging.h"
#include "gtest/gtest.h"
#include "gutil/proto.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_constraints/backend/constraint_info.h"
#include "p4_fuzzer/constraints_util.h"

namespace p4_fuzzer {

namespace {

constexpr char kBinaryEqualsP4InfoFile[] =
    "p4_fuzzer/constraints_equals.p4info.pb.txt";

constexpr char kBinaryNotEqualsP4InfoFile[] =
    "p4_fuzzer/constraints_not_equals.p4info.pb.txt";

p4_constraints::ConstraintInfo GetConstraintInfoFromP4Info(
    const std::string& p4info_file) {
  p4::config::v1::P4Info p4_info;

  CHECK_EQ(gutil::ReadProtoFromFile(p4info_file, &p4_info), absl::OkStatus());

  auto constraints = p4_constraints::P4ToConstraintInfo(p4_info);
  CHECK(constraints.ok()) << "Failed to parse ConstraintInfo from P4Info file";

  return *constraints;
}

p4_constraints::ast::Expression GetFirstExpressionFromConstraintInfo(
    const p4_constraints::ConstraintInfo& constraints) {
  for (auto& [id, table_info] : constraints) {
    if (table_info.constraint) {
      return table_info.constraint.value();
    }
  }

  LOG(FATAL) << "No expressions in constraint info";
}

TEST(ConstraintsUtilTest, BDDConversionTest) {
  Cudd mgr(0, 0);

  p4_constraints::ConstraintInfo constraints =
      GetConstraintInfoFromP4Info(kBinaryEqualsP4InfoFile);

  p4_constraints::ast::Expression expr =
      GetFirstExpressionFromConstraintInfo(constraints);
  LOG(INFO) << "Binary equals constraint:\n" << expr.DebugString();

  MatchKeyToBddVariableMapping equals_mapping;

  auto status_or_bdd = ExpressionToBDD(expr, &mgr, &equals_mapping);

  LOG(INFO) << "Done..";

  if (!status_or_bdd.ok()) {
    LOG(ERROR) << status_or_bdd.status();
  }

  BDD bdd = status_or_bdd.value();

  LOG(INFO) << "Converted BDD:";
  PrintBDDAsDotFile(bdd, &mgr);

  constraints = GetConstraintInfoFromP4Info(kBinaryNotEqualsP4InfoFile);

  expr = GetFirstExpressionFromConstraintInfo(constraints);
  LOG(INFO) << "Binary not equals constraint:\n" << expr.DebugString();

  MatchKeyToBddVariableMapping not_equals_mapping;

  status_or_bdd = ExpressionToBDD(expr, &mgr, &not_equals_mapping);
  if (!status_or_bdd.ok()) {
    LOG(ERROR) << status_or_bdd.status();
  }

  bdd = status_or_bdd.value();

  LOG(INFO) << "Converted BDD:";
  PrintBDDAsDotFile(bdd, &mgr);
}

}  // namespace

}  // namespace p4_fuzzer
