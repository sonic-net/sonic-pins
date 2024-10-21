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
#include <string>

#include "absl/types/optional.h"
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

TEST(ConstraintsUtilTest, BDDConversionTest) {
  Cudd mgr(0, 0);

  p4_constraints::ConstraintInfo constraints =
      GetConstraintInfoFromP4Info(kBinaryEqualsP4InfoFile);

  constexpr int kTblFuzzTableId = 49497980;
  auto* table_info =
      p4_constraints::GetTableInfoOrNull(constraints, kTblFuzzTableId);
  ASSERT_NE(table_info, nullptr)
      << "No table_info associated with table_id " << kTblFuzzTableId;
  const absl::optional<p4_constraints::ast::Expression>& constraint1 =
      table_info->constraint;
  ASSERT_TRUE(constraint1.has_value());
  LOG(INFO) << "Binary equals constraint:\n" << constraint1->DebugString();

  MatchKeyToBddVariableMapping equals_mapping;

  auto status_or_bdd = ExpressionToBDD(*constraint1, &mgr, &equals_mapping);

  LOG(INFO) << "Done..";

  ASSERT_EQ(status_or_bdd.status(), absl::OkStatus());

  BDD bdd = status_or_bdd.value();

  LOG(INFO) << "Converted BDD:";
  PrintBDDAsDotFile(bdd, &mgr);

  constraints = GetConstraintInfoFromP4Info(kBinaryNotEqualsP4InfoFile);

  table_info = p4_constraints::GetTableInfoOrNull(constraints, 49497980);
  ASSERT_NE(table_info, nullptr)
      << "No table_info associated with table_id " << kTblFuzzTableId;
  const absl::optional<p4_constraints::ast::Expression>& constraint2 =
      table_info->constraint;
  ASSERT_TRUE(constraint2.has_value());
  LOG(INFO) << "Binary not equals constraint:\n" << constraint2->DebugString();

  MatchKeyToBddVariableMapping not_equals_mapping;

  status_or_bdd = ExpressionToBDD(*constraint2, &mgr, &not_equals_mapping);

  LOG(INFO) << "Done..";

  ASSERT_EQ(status_or_bdd.status(), absl::OkStatus());

  bdd = status_or_bdd.value();

  LOG(INFO) << "Converted BDD:";
  PrintBDDAsDotFile(bdd, &mgr);
}

}  // namespace

}  // namespace p4_fuzzer
