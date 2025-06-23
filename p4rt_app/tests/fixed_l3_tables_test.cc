// Copyright 2020 Google LLC
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
#include <memory>
#include <set>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "gmock/gmock.h"
#include "grpcpp/security/credentials.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/p4_runtime/p4_runtime_session.h"
#include "p4_infra/p4_pdpi/pd.h"
#include "p4rt_app/tests/lib/app_db_entry_builder.h"
#include "p4rt_app/tests/lib/p4runtime_component_test_fixture.h"
#include "p4rt_app/tests/lib/p4runtime_grpc_service.h"
#include "p4rt_app/tests/lib/p4runtime_request_helpers.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

namespace p4rt_app {
namespace {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;
using ::gutil::StatusIs;
using ::testing::HasSubstr;
using ::testing::UnorderedElementsAreArray;

// Ensure we can program each of the L3 flows.
class FixedL3TableTest : public test_lib::P4RuntimeComponentTestFixture {
 protected:
  FixedL3TableTest()
      : test_lib::P4RuntimeComponentTestFixture(
            sai::Instantiation::kMiddleblock) {}
};

TEST_F(FixedL3TableTest, SupportRouterInterfaceTableFlows) {
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet4", "2"));

  // P4 write request.
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::PdWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               table_entry {
                                 router_interface_table_entry {
                                   match { router_interface_id: "16" }
                                   action {
                                     set_port_and_src_mac {
                                       port: "2"
                                       src_mac: "00:02:03:04:05:06"
                                     }
                                   }
                                 }
                               }
                             }
                           )pb",
                           ir_p4_info_));

  // Expected P4RT AppDb entry.
  auto expected_entry = test_lib::AppDbEntryBuilder{}
                            .SetTableName("FIXED_ROUTER_INTERFACE_TABLE")
                            .AddMatchField("router_interface_id", "16")
                            .SetAction("set_port_and_src_mac")
                            .AddActionParam("port", "Ethernet4")
                            .AddActionParam("src_mac", "00:02:03:04:05:06");

  EXPECT_OK(p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                         request));
  EXPECT_THAT(
      p4rt_service_.GetP4rtAppDbTable().ReadTableEntry(expected_entry.GetKey()),
      IsOkAndHolds(UnorderedElementsAreArray(expected_entry.GetValueMap())));

  // Sanity check that port_id_t translations are read back correctly.
  p4::v1::ReadRequest read_request;
  read_request.add_entities()->mutable_table_entry();
  ASSERT_OK_AND_ASSIGN(p4::v1::ReadResponse read_response,
                       p4_runtime::SetMetadataAndSendPiReadRequest(
                           p4rt_session_.get(), read_request));
  ASSERT_EQ(read_response.entities_size(), 1);  // Only one write.
  EXPECT_THAT(read_response.entities(0),
              EqualsProto(request.updates(0).entity()));
}

TEST_F(FixedL3TableTest, SupportNeighborTableFlows) {
  // P4 write request.
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest request,
      test_lib::PdWriteRequestToPi(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                neighbor_table_entry {
                  match {
                    neighbor_id: "fe80::21a:11ff:fe17:5f80"
                    router_interface_id: "1"
                  }
                  action { set_dst_mac { dst_mac: "00:1a:11:17:5f:80" } }
                }
              }
            }
          )pb",
          ir_p4_info_));

  // Expected P4RT AppDb entries.
  auto neighbor_entry =
      test_lib::AppDbEntryBuilder{}
          .SetTableName("FIXED_NEIGHBOR_TABLE")
          .AddMatchField("neighbor_id", "fe80::21a:11ff:fe17:5f80")
          .AddMatchField("router_interface_id", "1")
          .SetAction("set_dst_mac")
          .AddActionParam("dst_mac", "00:1a:11:17:5f:80");

  EXPECT_OK(p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                         request));
  EXPECT_THAT(
      p4rt_service_.GetP4rtAppDbTable().ReadTableEntry(neighbor_entry.GetKey()),
      IsOkAndHolds(UnorderedElementsAreArray(neighbor_entry.GetValueMap())));
}

TEST_F(FixedL3TableTest, SupportNexthopTableRouterInterfaceActionFlows) {
  // P4 write request.
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::PdWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               table_entry {
                                 nexthop_table_entry {
                                   match { nexthop_id: "8" }
                                   action {
                                     set_ip_nexthop {
                                       router_interface_id: "8"
                                       neighbor_id: "fe80::21a:11ff:fe17:5f80"
                                     }
                                   }
                                 }
                               }
                             }
                           )pb",
                           ir_p4_info_));

  // Expected P4RT AppDb entries.
  auto nexthop_entry =
      test_lib::AppDbEntryBuilder{}
          .SetTableName("FIXED_NEXTHOP_TABLE")
          .AddMatchField("nexthop_id", "8")
          .SetAction("set_ip_nexthop")
          .AddActionParam("router_interface_id", "8")
          .AddActionParam("neighbor_id", "fe80::21a:11ff:fe17:5f80");

  EXPECT_OK(p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                         request));
  EXPECT_THAT(
      p4rt_service_.GetP4rtAppDbTable().ReadTableEntry(nexthop_entry.GetKey()),
      IsOkAndHolds(UnorderedElementsAreArray(nexthop_entry.GetValueMap())));
}

TEST_F(FixedL3TableTest, SupportMyStationFlowWithPort) {
  ASSERT_OK(p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet4", "2"));

  // P4 write request.
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::PdWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               table_entry {
                                 l3_admit_table_entry {
                                   match {
                                     dst_mac {
                                       value: "00:AA:BB:CC:00:00"
                                       mask: "FF:FF:FF:FF:00:00"
                                     }
                                     in_port { value: "2" }
                                   }
                                   action { admit_to_l3 {} }
                                   priority: 1000
                                 }
                               }
                             }
                           )pb",
                           ir_p4_info_));

  // Expected P4RT AppDb entry.
  auto expected_entry =
      test_lib::AppDbEntryBuilder{}
          .SetTableName("FIXED_L3_ADMIT_TABLE")
          .SetPriority(1000)
          .AddMatchField("dst_mac", R"(00:aa:bb:cc:00:00&ff:ff:ff:ff:00:00)")
          .AddMatchField("in_port", "Ethernet4")
          .SetAction("admit_to_l3");

  EXPECT_OK(p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                         request));
  EXPECT_THAT(
      p4rt_service_.GetP4rtAppDbTable().ReadTableEntry(expected_entry.GetKey()),
      IsOkAndHolds(UnorderedElementsAreArray(expected_entry.GetValueMap())));

  p4rt_service_.GetP4rtAppDbTable().DebugState();
}

TEST_F(FixedL3TableTest, SupportMyStationFlowWithoutPort) {
  // P4 write request.
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::PdWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               table_entry {
                                 l3_admit_table_entry {
                                   match {
                                     dst_mac {
                                       value: "00:AA:BB:CC:00:00"
                                       mask: "FF:FF:FF:FF:00:00"
                                     }
                                   }
                                   action { admit_to_l3 {} }
                                   priority: 1000
                                 }
                               }
                             }
                           )pb",
                           ir_p4_info_));

  // Expected P4RT AppDb entry.
  auto expected_entry =
      test_lib::AppDbEntryBuilder{}
          .SetTableName("FIXED_L3_ADMIT_TABLE")
          .SetPriority(1000)
          .AddMatchField("dst_mac", R"(00:aa:bb:cc:00:00&ff:ff:ff:ff:00:00)")
          .SetAction("admit_to_l3");

  EXPECT_OK(p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                         request));
  EXPECT_THAT(
      p4rt_service_.GetP4rtAppDbTable().ReadTableEntry(expected_entry.GetKey()),
      IsOkAndHolds(UnorderedElementsAreArray(expected_entry.GetValueMap())));

  p4rt_service_.GetP4rtAppDbTable().DebugState();
}

TEST_F(FixedL3TableTest, InvalidPortIdFails) {
  // P4 write request with an unassigned port value (i.e. 999).
  ASSERT_OK_AND_ASSIGN(p4::v1::WriteRequest request,
                       test_lib::PdWriteRequestToPi(
                           R"pb(
                             updates {
                               type: INSERT
                               table_entry {
                                 router_interface_table_entry {
                                   match { router_interface_id: "16" }
                                   action {
                                     set_port_and_src_mac {
                                       port: "999"
                                       src_mac: "00:02:03:04:05:06"
                                     }
                                   }
                                 }
                               }
                             }
                           )pb",
                           ir_p4_info_));

  EXPECT_THAT(
      p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kUnknown, HasSubstr("#1: INVALID_ARGUMENT")));
}

TEST_F(FixedL3TableTest, IncorrectlyFormatedRequestFailsConstraintCheck) {
  // P4 write request for the "router interface table", but its match field is
  // missing a value making it invalid.
  p4::v1::WriteRequest request;
  ASSERT_OK(gutil::ReadProtoFromString(
      R"pb(updates {
             type: INSERT
             entity {
               table_entry {
                 table_id: 33554497
                 match { field_id: 1 }
                 action {
                   action {
                     action_id: 16777218
                     params { param_id: 1 value: "2" }
                     params { param_id: 2 value: "\002\003\004\005\006" }
                   }
                 }
               }
             }
           })pb",
      &request));

  EXPECT_THAT(
      p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kUnknown, HasSubstr("#1: INVALID_ARGUMENT")));
}

TEST_F(FixedL3TableTest, MissingActionWhenRequiredFails) {
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest write_request,
      test_lib::PdWriteRequestToPi(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                ipv6_table_entry {
                  match {
                    vrf_id: "80"
                    ipv6_dst { value: "2002:a17:506:c114::" prefix_length: 64 }
                  }
                  action { set_nexthop_id { nexthop_id: "20" } }
                }
              }
            }
          )pb",
          ir_p4_info_));

  write_request.mutable_updates(0)
      ->mutable_entity()
      ->mutable_table_entry()
      ->mutable_action()
      ->Clear();

  EXPECT_THAT(
      p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                             write_request),
      StatusIs(absl::StatusCode::kUnknown, HasSubstr("#1: INVALID_ARGUMENT")));
}

// Ensure we can program each of the L3 flow actions.
class L3LpmTableTest : public FixedL3TableTest,
                       public testing::WithParamInterface<std::string> {
 public:
  struct TestData {
    struct AppDbEntry {
      std::string action;
      std::vector<std::pair<std::string, std::string>> params;
    };

    std::string pd_action;
    AppDbEntry app_db;
  };
  using TestMap = absl::flat_hash_map<std::string, L3LpmTableTest::TestData>;

  static const TestMap& GetTestMap();
  static const std::set<std::string>& TestCases();

 protected:
  absl::StatusOr<p4::v1::WriteRequest> WriteRequest(const TestData& test_case);
};

const L3LpmTableTest::TestMap& L3LpmTableTest::GetTestMap() {
  static const auto* const kTestMap = new TestMap({
      {"drop", {.pd_action = R"pb(drop {})pb", .app_db = {.action = "drop"}}},
      {"set_nexthop_id",
       {.pd_action = R"pb(set_nexthop_id { nexthop_id: "13" })pb",
        .app_db = {.action = "set_nexthop_id",
                   .params = {{"nexthop_id", "13"}}}}},
      {"set_wcmp_group_id",
       {.pd_action = R"pb(set_wcmp_group_id { wcmp_group_id: "23" })pb",
        .app_db = {.action = "set_wcmp_group_id",
                   .params = {{"wcmp_group_id", "23"}}}}},
      {"set_nexthop_id_and_metadata",
       {.pd_action = R"pb(set_nexthop_id_and_metadata {
                            nexthop_id: "13"
                            route_metadata: "0x07"
                          })pb",
        .app_db = {.action = "set_nexthop_id_and_metadata",
                   .params = {{"nexthop_id", "13"},
                              {"route_metadata", "0x07"}}}}},
      {"set_wcmp_group_id_and_metadata",
       {.pd_action = R"pb(set_wcmp_group_id_and_metadata {
                            wcmp_group_id: "23"
                            route_metadata: "0x07"
                          })pb",
        .app_db = {.action = "set_wcmp_group_id_and_metadata",
                   .params = {{"wcmp_group_id", "23"},
                              {"route_metadata", "0x07"}}}}},
  });
  return *kTestMap;
}

const std::set<std::string>& L3LpmTableTest::TestCases() {
  static const auto* const kTestCases = []() {
    auto* test_cases = new std::set<std::string>();
    for (const auto& [test_case_name, test_data] : GetTestMap()) {
      test_cases->insert(test_case_name);
    }
    return test_cases;
  }();
  return *kTestCases;
}

TEST_P(L3LpmTableTest, SupportIpv4TableFlow) {
  constexpr absl::string_view kPdRequestTemplate = R"pb(
    updates {
      type: INSERT
      table_entry {
        ipv4_table_entry {
          match {
            vrf_id: "50"
            ipv4_dst { value: "10.81.8.0" prefix_length: 23 }
          }
          action { $0 }
        }
      }
    }
  )pb";
  TestData test_data = GetTestMap().at(GetParam());
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest request,
      test_lib::PdWriteRequestToPi(
          absl::Substitute(kPdRequestTemplate, test_data.pd_action),
          ir_p4_info_));

  test_lib::AppDbEntryBuilder expected_entry;
  expected_entry.SetTableName("FIXED_IPV4_TABLE")
      .AddMatchField("ipv4_dst", "10.81.8.0/23")
      .AddMatchField("vrf_id", "50")
      .SetAction(test_data.app_db.action);
  for (const auto& [param, value] : test_data.app_db.params) {
    expected_entry.AddActionParam(param, value);
  }

  EXPECT_OK(p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                         request));
  EXPECT_THAT(
      p4rt_service_.GetP4rtAppDbTable().ReadTableEntry(expected_entry.GetKey()),
      IsOkAndHolds(UnorderedElementsAreArray(expected_entry.GetValueMap())));
}

TEST_P(L3LpmTableTest, SupportIpv6TableFlow) {
  constexpr absl::string_view kPdRequestTemplate = R"pb(
    updates {
      type: INSERT
      table_entry {
        ipv6_table_entry {
          match {
            vrf_id: "50"
            ipv6_dst { value: "2002:a17:506:c114::" prefix_length: 64 }
          }
          action { $0 }
        }
      }
    }
  )pb";
  TestData test_data = GetTestMap().at(GetParam());
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest request,
      test_lib::PdWriteRequestToPi(
          absl::Substitute(kPdRequestTemplate, test_data.pd_action),
          ir_p4_info_));

  test_lib::AppDbEntryBuilder expected_entry;
  expected_entry.SetTableName("FIXED_IPV6_TABLE")
      .AddMatchField("ipv6_dst", "2002:a17:506:c114::/64")
      .AddMatchField("vrf_id", "50")
      .SetAction(test_data.app_db.action);
  for (const auto& [param, value] : test_data.app_db.params) {
    expected_entry.AddActionParam(param, value);
  }

  EXPECT_OK(p4_runtime::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(),
                                                         request));
  EXPECT_THAT(
      p4rt_service_.GetP4rtAppDbTable().ReadTableEntry(expected_entry.GetKey()),
      IsOkAndHolds(UnorderedElementsAreArray(expected_entry.GetValueMap())));
}

INSTANTIATE_TEST_SUITE_P(PerAction, L3LpmTableTest,
                         testing::ValuesIn(L3LpmTableTest::TestCases()),
                         [](testing::TestParamInfo<std::string> info) {
                           return info.param;
                         });

}  // namespace
}  // namespace p4rt_app
