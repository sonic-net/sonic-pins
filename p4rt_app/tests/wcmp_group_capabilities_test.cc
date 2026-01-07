// Copyright 2026 Google LLC
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
#include <utility>

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "gmock/gmock.h"
#include "grpcpp/security/credentials.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4rt_app/sonic/adapters/fake_sonic_db_table.h"
#include "p4rt_app/tests/lib/p4runtime_component_test_fixture.h"
#include "p4rt_app/tests/lib/p4runtime_request_helpers.h"
#include "sai_p4/capabilities.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"

namespace p4rt_app {

namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;

class WcmpGroupCapabilitiesTest
    : public test_lib::P4RuntimeComponentTestFixture {
 protected:
  WcmpGroupCapabilitiesTest()
      : test_lib::P4RuntimeComponentTestFixture(
            sai::Instantiation::kMiddleblock) {}

  void SetUp() override {
    // Configure the Device ID on the P4RT Server.
    ASSERT_OK(p4rt_service_.GetP4rtServer().UpdateDeviceId(device_id_));

    // Open a P4RT client connection to the gRPC server.
    std::string address = absl::StrCat("localhost:", p4rt_service_.GrpcPort());
    auto stub =
        pdpi::CreateP4RuntimeStub(address, grpc::InsecureChannelCredentials());
    ASSERT_OK_AND_ASSIGN(p4rt_session_, pdpi::P4RuntimeSession::Create(
                                            std::move(stub), device_id_));
    LOG(INFO) << "Opening P4RT connection to " << address << ".";
  }
};

TEST_F(WcmpGroupCapabilitiesTest, InvalidWcmpGroupCapabilityValuesInDbTest) {
  {
    // Set non-integer values for the WCMP group capabilities in the DB.
    sonic::SonicDbEntryList values = {
        {"max_total_weight_per_group", "invalid"},
        {"max_distinct_weights_per_group", "10"},
    };
    p4rt_service_.SetSwitchCapabilitiesTableInDb(values);
    EXPECT_THAT(test_lib::GetWcmpGroupCapabilities(p4rt_session_.get()),
                gutil::StatusIs(absl::StatusCode::kUnknown));
  }

  {
    // Set value < 0 in the DB.
    sonic::SonicDbEntryList values = {
        {"max_total_weight_per_group", "30"},
        {"max_distinct_weights_per_group", "-1"},
    };
    p4rt_service_.SetSwitchCapabilitiesTableInDb(values);
    EXPECT_THAT(test_lib::GetWcmpGroupCapabilities(p4rt_session_.get()),
                gutil::StatusIs(absl::StatusCode::kUnknown));
  }
}

TEST_F(WcmpGroupCapabilitiesTest, WcmpGroupCapabilitySuccessTest) {
  {
    // Don't set any WCMP group capabilities in the DB.
    sai::WcmpGroupLimitations expected_wcmp_group_capabilities;
    EXPECT_THAT(test_lib::GetWcmpGroupCapabilities(p4rt_session_.get()),
                IsOkAndHolds(EqualsProto(expected_wcmp_group_capabilities)));
  }

  {
    // Set non-zero values for the WCMP group capabilities in the DB.
    const int kMaxTotalWeight = 31;
    const int kMaxDistinctWeight = 28;
    sonic::SonicDbEntryList values = {
        {"max_total_weight_per_group", absl::StrCat(kMaxTotalWeight)},
        {"max_distinct_weights_per_group", absl::StrCat(kMaxDistinctWeight)},
    };
    p4rt_service_.SetSwitchCapabilitiesTableInDb(values);
    sai::WcmpGroupLimitations expected_wcmp_group_capabilities;
    expected_wcmp_group_capabilities.set_max_total_weight_per_group(
        kMaxTotalWeight);
    expected_wcmp_group_capabilities.set_max_distinct_weights_per_group(
        kMaxDistinctWeight);
    EXPECT_THAT(test_lib::GetWcmpGroupCapabilities(p4rt_session_.get()),
                IsOkAndHolds(EqualsProto(expected_wcmp_group_capabilities)));
  }

  {
    // Set zero values for the WCMP group capabilities in the DB.
    const int kMaxTotalWeight = 0;
    const int kMaxDistinctWeight = 0;
    sonic::SonicDbEntryList values = {
        {"max_total_weight_per_group", absl::StrCat(kMaxTotalWeight)},
        {"max_distinct_weights_per_group", absl::StrCat(kMaxDistinctWeight)},
    };
    p4rt_service_.SetSwitchCapabilitiesTableInDb(values);
    sai::WcmpGroupLimitations expected_wcmp_group_capabilities;
    expected_wcmp_group_capabilities.set_max_total_weight_per_group(
        kMaxTotalWeight);
    expected_wcmp_group_capabilities.set_max_distinct_weights_per_group(
        kMaxDistinctWeight);
    EXPECT_THAT(test_lib::GetWcmpGroupCapabilities(p4rt_session_.get()),
                IsOkAndHolds(EqualsProto(expected_wcmp_group_capabilities)));
  }
}

}  // namespace
}  // namespace p4rt_app

