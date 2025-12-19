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
#include <cstdint>
#include <vector>

#include "absl/strings/ascii.h"
#include "absl/strings/str_cat.h"
#include "gmock/gmock.h"
#include "grpcpp/security/credentials.h"
#include "gtest/gtest.h"
#include "include/nlohmann/json.hpp"
#include "gutil/status_matchers.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/utils/annotation_parser.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/tests/lib/p4runtime_grpc_service.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace p4rt_app {
namespace {

using ::testing::Contains;
using ::testing::Key;

MATCHER_P2(HasJsonObject, key, value, "") {
  nlohmann::json json = nlohmann::json::parse(arg);
  if (json.count(key) == 0) {
    *result_listener << "Missing JSON object \"" << key << "\"";
    return false;
  }
  return json[key] == value;
}

bool IsCompositeUdfMatchField(
    const pdpi::IrMatchFieldDefinition& match_field_def) {
  // They will be marked by the 'composite_field'.
  auto composite_field = pdpi::GetAnnotationAsArgList(
      "composite_field", match_field_def.match_field().annotations());
  if (!composite_field.ok() || composite_field->empty()) return false;

  // And all the sub annotations should be marked as 'sai_udf'.
  for (const auto& sub_annotation : pdpi::GetAllAnnotations(*composite_field)) {
    if (sub_annotation.label != "sai_udf") return false;
  }

  return true;
}

// The P4 programs tests verify that the P4 programs can be pushed end-to-end
// through the P4RT App. They are also used to verify the P4 programs match
// SONiC expectations. Sanity checks that
// using P4ProgramsTest = testing::TestWithParam<sai::Instantiation>;
class P4ProgramsTest : public testing::TestWithParam<sai::Instantiation> {
 protected:
  void SetUp() override {
    uint64_t device_id = 100402;
    ASSERT_OK(p4rt_service_.GetP4rtServer().UpdateDeviceId(device_id));

    // Create a P4RT session, and connect.
    std::string address = absl::StrCat("localhost:", p4rt_service_.GrpcPort());
    auto stub =
        pdpi::CreateP4RuntimeStub(address, grpc::InsecureChannelCredentials());
    ASSERT_OK_AND_ASSIGN(p4rt_session_, pdpi::P4RuntimeSession::Create(
                                            std::move(stub), device_id));
  }

  test_lib::P4RuntimeGrpcService p4rt_service_ =
      test_lib::P4RuntimeGrpcService(P4RuntimeImplOptions{});
  std::unique_ptr<pdpi::P4RuntimeSession> p4rt_session_;
};

TEST_P(P4ProgramsTest, CanPushP4InfoWithoutFailure) {
  EXPECT_OK(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      p4rt_session_.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      sai::GetP4Info(GetParam())));
}

// SONiC requires any composite UDF field to be formatted as a HEX_STRING.
// However, P4Info isn't limited by this same restriction. It can use other
// formats for ease of readability. Therefore, the P4RT App should update any
// composite UDFs to use HEX_STRING before writing to the AppDb.
TEST_P(P4ProgramsTest, CompositeUdfFieldsShouldAlwaysUseHexStrings) {
  const p4::config::v1::P4Info& p4_info = sai::GetP4Info(GetParam());
  const pdpi::IrP4Info& ir_p4_info = sai::GetIrP4Info(GetParam());
  struct AppDbField {
    std::string table_name;
    std::string field_name;
  };

  // Push the P4Info for the instance under test.
  EXPECT_OK(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      p4rt_session_.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      p4_info));

  // Go through all match fields for the table definitions looking for composite
  // UDF fields.
  std::vector<AppDbField> composite_udf_fields;
  for (const auto& [table_name, table_def] : ir_p4_info.tables_by_name()) {
    for (const auto& [match_field_name, match_field_def] :
         table_def.match_fields_by_name()) {
      if (!IsCompositeUdfMatchField(match_field_def)) continue;

      LOG(INFO) << "Found composite UDF: " << match_field_def.DebugString();
      composite_udf_fields.push_back({
          .table_name = absl::StrCat("ACL_TABLE_DEFINITION_TABLE:ACL_",
                                     absl::AsciiStrToUpper(table_name)),
          .field_name = absl::StrCat("match/", match_field_name),
      });
    }
  }

  // Ensure all the identified fields are using a HEX_STRING.
  for (const AppDbField& app_db_field : composite_udf_fields) {
    ASSERT_OK_AND_ASSIGN(auto app_db_definition,
                         p4rt_service_.GetP4rtAppDbTable().ReadTableEntry(
                             app_db_field.table_name));
    ASSERT_THAT(app_db_definition, Contains(Key(app_db_field.field_name)));
    const std::string& composite_udf_field =
        app_db_definition.at(app_db_field.field_name);

    EXPECT_THAT(composite_udf_field, HasJsonObject("format", "HEX_STRING"));
  }
}

INSTANTIATE_TEST_SUITE_P(
    P4ProgramsTestInstance, P4ProgramsTest,
    testing::ValuesIn(sai::AllSaiInstantiations()),
    [](const testing::TestParamInfo<P4ProgramsTest::ParamType>& param) {
      return sai::InstantiationToString(param.param);
    });

}  // namespace
}  // namespace p4rt_app
