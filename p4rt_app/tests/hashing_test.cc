// Copyright 2024 Google LLC
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
#include <memory>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

#include "absl/container/btree_set.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "gmock/gmock.h"
#include "grpcpp/security/credentials.h"
#include "gtest/gtest.h"
#include "include/nlohmann/json.hpp"
#include "gutil/status_matchers.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/tests/lib/p4runtime_grpc_service.h"
#include "sai_p4/instantiations/google/clos_stage.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_p4info_fetcher.h"

namespace p4rt_app {
namespace {

using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::Combine;
using ::testing::Contains;
using ::testing::HasSubstr;
using ::testing::IsSupersetOf;
using ::testing::Key;
using ::testing::Pair;
using ::testing::UnorderedElementsAreArray;
using ::testing::Values;

// The ECMP hashing test verifies a P4 instance has a valid configuration for
// ECMP.
using EcmpHashingTest =
    testing::TestWithParam<std::tuple<sai::Instantiation, sai::ClosStage>>;

MATCHER_P(IsUnorderedJsonListOf, hash_fields_list,
          absl::StrCat(negation ? "isn't" : "is",
                       " a json list containing the expected fields: {",
                       absl::StrJoin(hash_fields_list, ", "), "}")) {
  nlohmann::json json = nlohmann::json::parse(arg);
  if (!json.is_array()) {
    *result_listener << "Expected a JSON array.";
  }
  absl::btree_set<std::string> arg_values;
  for (const auto& field : json) {
    arg_values.insert(field.get<std::string>());
  }
  return ExplainMatchResult(UnorderedElementsAreArray(hash_fields_list),
                            arg_values, result_listener);
}

TEST_P(EcmpHashingTest, MustConfigureEcmpHashing) {
  // Start the P4RT service
  uint64_t device_id = 100400;
  test_lib::P4RuntimeGrpcService p4rt_service =
      test_lib::P4RuntimeGrpcService(P4RuntimeImplOptions{});
  ASSERT_OK(p4rt_service.GetP4rtServer().UpdateDeviceId(device_id));

  // Create a P4RT session, and connect.
  std::string address = absl::StrCat("localhost:", p4rt_service.GrpcPort());
  auto stub =
      pdpi::CreateP4RuntimeStub(address, grpc::InsecureChannelCredentials());
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<pdpi::P4RuntimeSession> p4rt_session,
      pdpi::P4RuntimeSession::Create(std::move(stub), device_id));

  // Push the P4Info for the instance under test.
  ASSERT_OK(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      p4rt_session.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      sai::FetchP4Info(std::get<0>(GetParam()), std::get<1>(GetParam()))));

  // Verify the AppDb HASH_TABLE has entries for both the IPv4 and IPv6
  // configurations.
  EXPECT_THAT(
      p4rt_service.GetHashAppDbTable().ReadTableEntry("compute_ecmp_hash_ipv4"),
      IsOkAndHolds(Contains(
          Pair("hash_field_list",
               IsUnorderedJsonListOf(std::vector<std::string>{
                   "src_ip", "dst_ip", "l4_src_port", "l4_dst_port"})))));
  EXPECT_THAT(
      p4rt_service.GetHashAppDbTable().ReadTableEntry("compute_ecmp_hash_ipv6"),
      IsOkAndHolds(Contains(Pair("hash_field_list",
                                 IsUnorderedJsonListOf(std::vector<std::string>{
                                     "src_ip", "dst_ip", "l4_src_port",
                                     "l4_dst_port", "ipv6_flow_label"})))));

  // Verify the AppDb SWITCH_TABLE has an entry for all the ECMP configuration
  // fields.
  EXPECT_THAT(p4rt_service.GetSwitchAppDbTable().ReadTableEntry("switch"),
              IsOkAndHolds(IsSupersetOf({
                  Key("ecmp_hash_seed"),
                  Key("ecmp_hash_ipv6"),
                  Key("ecmp_hash_ipv4"),
              })));
}

INSTANTIATE_TEST_SUITE_P(
    EcmpHashingTestInstance, EcmpHashingTest,
    Combine(Values(sai::Instantiation::kMiddleblock,
                   sai::Instantiation::kFabricBorderRouter),
            Values(sai::ClosStage::kStage2, sai::ClosStage::kStage3)),
    [](const testing::TestParamInfo<EcmpHashingTest::ParamType>& param) {
      return absl::StrCat(sai::InstantiationToString(std::get<0>(param.param)),
                          sai::ClosStageToString(std::get<1>(param.param)));
    });

// The LAG hashing test verifies a P4 instance has a valid configuration for
// LAGs.
using LagHashingTest = EcmpHashingTest;

TEST_P(LagHashingTest, MustConfigureLagHashing) {
  // Start the P4RT service
  uint64_t device_id = 100400;
  test_lib::P4RuntimeGrpcService p4rt_service =
      test_lib::P4RuntimeGrpcService(P4RuntimeImplOptions{});
  ASSERT_OK(p4rt_service.GetP4rtServer().UpdateDeviceId(device_id));

  // Create a P4RT session, and connect.
  std::string address = absl::StrCat("localhost:", p4rt_service.GrpcPort());
  auto stub =
      pdpi::CreateP4RuntimeStub(address, grpc::InsecureChannelCredentials());
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<pdpi::P4RuntimeSession> p4rt_session,
      pdpi::P4RuntimeSession::Create(std::move(stub), device_id));

  // Push the P4Info for the instance under test.
  ASSERT_OK(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      p4rt_session.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      sai::FetchP4Info(std::get<0>(GetParam()), std::get<1>(GetParam()))));

  // Verify the AppDb HASH_TABLE has entries for both the IPv4 and IPv6
  // configurations.
  EXPECT_THAT(
      p4rt_service.GetHashAppDbTable().ReadTableEntry("compute_lag_hash_ipv4"),
      IsOkAndHolds(Contains(
          Pair("hash_field_list",
               IsUnorderedJsonListOf(std::vector<std::string>{
                   "src_ip", "dst_ip", "l4_src_port", "l4_dst_port"})))));
  EXPECT_THAT(
      p4rt_service.GetHashAppDbTable().ReadTableEntry("compute_lag_hash_ipv6"),
      IsOkAndHolds(Contains(Pair("hash_field_list",
                                 IsUnorderedJsonListOf(std::vector<std::string>{
                                     "src_ip", "dst_ip", "l4_src_port",
                                     "l4_dst_port", "ipv6_flow_label"})))));

  // Verify the AppDb SWITCH_TABLE has an entry for all the lag configuration
  // fields.
  EXPECT_THAT(p4rt_service.GetSwitchAppDbTable().ReadTableEntry("switch"),
              IsOkAndHolds(IsSupersetOf({
                  Key("lag_hash_algorithm"),
                  Key("lag_hash_seed"),
                  Key("lag_hash_offset"),
                  Key("lag_hash_ipv6"),
                  Key("lag_hash_ipv4"),
              })));
}

INSTANTIATE_TEST_SUITE_P(
    LagHashingTestInstance, LagHashingTest,
    Combine(Values(sai::Instantiation::kFabricBorderRouter),
            Values(sai::ClosStage::kStage2, sai::ClosStage::kStage3)),
    [](const testing::TestParamInfo<EcmpHashingTest::ParamType>& param) {
      return absl::StrCat(sai::InstantiationToString(std::get<0>(param.param)),
                          sai::ClosStageToString(std::get<1>(param.param)));
    });

class HashingTest : public testing::Test {
 protected:
  void SetUp() override {
    uint64_t device_id = 100401;
    ASSERT_OK(p4rt_service_.GetP4rtServer().UpdateDeviceId(device_id));

    std::string address = absl::StrCat("localhost:", p4rt_service_.GrpcPort());
    LOG(INFO) << "Opening P4RT connection to " << address << ".";
    auto stub =
        pdpi::CreateP4RuntimeStub(address, grpc::InsecureChannelCredentials());
    ASSERT_OK_AND_ASSIGN(p4rt_session_, pdpi::P4RuntimeSession::Create(
                                            std::move(stub), device_id));
  }

  test_lib::P4RuntimeGrpcService p4rt_service_ =
      test_lib::P4RuntimeGrpcService(P4RuntimeImplOptions{});
  std::unique_ptr<pdpi::P4RuntimeSession> p4rt_session_;
};

TEST_F(HashingTest, HashTableInsertionFails) {
  p4::config::v1::P4Info p4_info =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);
  std::string action_name;
  for (const auto& action : p4_info.actions()) {
    if (absl::StartsWith(action.preamble().name(), "ingress.hashing")) {
      action_name = action.preamble().alias();
    }
  }

  p4rt_service_.GetHashAppDbTable().SetResponseForKey(
      action_name, "SWSS_RC_INVALID_PARAM", "my error message");
  EXPECT_THAT(
      pdpi::SetMetadataAndSetForwardingPipelineConfig(
          p4rt_session_.get(),
          p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
          p4_info),
      StatusIs(absl::StatusCode::kInternal, HasSubstr("my error message")));
}

TEST_F(HashingTest, SwitchTableInsertionFails) {
  p4::config::v1::P4Info p4_info =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);
  p4rt_service_.GetSwitchAppDbTable().SetResponseForKey(
      "switch", "SWSS_RC_INVALID_PARAM", "my error message");
  EXPECT_THAT(
      pdpi::SetMetadataAndSetForwardingPipelineConfig(
          p4rt_session_.get(),
          p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
          p4_info),
      StatusIs(absl::StatusCode::kInternal, HasSubstr("my error message")));
}

}  // namespace
}  // namespace p4rt_app
