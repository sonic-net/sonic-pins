// Copyright (c) 2024, Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "lib/basic_traffic/basic_p4rt_util.h"

#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace pins_test::basic_traffic {
namespace {

using ::gutil::EqualsProto;
using ::testing::_;
using ::testing::MockFunction;
using ::testing::Return;

TEST(BasicTraffic, ProgramDefaultVrf) {
  MockFunction<absl::Status(pdpi::P4RuntimeSession*, p4::v1::WriteRequest&)>
      mock_write_request;
  EXPECT_CALL(
      mock_write_request,
      Call(_, EqualsProto(R"pb(updates {
                                 type: INSERT
                                 entity {
                                   table_entry {
                                     table_id: 33554506
                                     match {
                                       field_id: 1
                                       exact { value: "traffic-vrf" }
                                     }
                                     action { action { action_id: 24742814 } }
                                   }
                                 }
                               })pb")))
      .WillOnce(Return(absl::OkStatus()));
  EXPECT_CALL(mock_write_request,
              Call(_, EqualsProto(R"pb(
                     updates {
                       type: INSERT
                       entity {
                         table_entry {
                           table_id: 33554689
                           action {
                             action {
                               action_id: 16777472
                               params { param_id: 1 value: "traffic-vrf" }
                             }
                           }
                           priority: 1132
                         }
                       }
                     }
                   )pb")))
      .WillOnce(Return(absl::OkStatus()));
  EXPECT_OK(ProgramTrafficVrf(
      /*session=*/nullptr, sai::GetIrP4Info(sai::Instantiation::kMiddleblock),
      mock_write_request.AsStdFunction()));
}

TEST(BasicTraffic, ProgramRouterInterface) {
  MockFunction<absl::Status(pdpi::P4RuntimeSession*, p4::v1::WriteRequest&)>
      mock_write_request;
  EXPECT_CALL(mock_write_request,
              Call(_, EqualsProto(R"pb(
                     updates {
                       type: INSERT
                       entity {
                         table_entry {
                           table_id: 33554497
                           match {
                             field_id: 1
                             exact { value: "traffic-router-interface-5" }
                           }
                           action {
                             action {
                               action_id: 16777264
                               params { param_id: 1 value: "5" }
                               params { param_id: 2 value: "\005" }
                             }
                           }
                         }
                       }
                     }
                   )pb")))
      .WillOnce(Return(absl::OkStatus()));
  EXPECT_OK(
      ProgramRouterInterface(/*session=*/nullptr, /*port_id=*/5,
                             sai::GetIrP4Info(sai::Instantiation::kMiddleblock),
                             mock_write_request.AsStdFunction()));
}

TEST(BasicTraffic, ProgramIPv4Route) {
  MockFunction<absl::Status(pdpi::P4RuntimeSession*, p4::v1::WriteRequest&)>
      mock_write_request;
  // Neighbor entry.
  EXPECT_CALL(
      mock_write_request,
      Call(
          _, EqualsProto(R"pb(
            updates {
              type: INSERT
              entity {
                table_entry {
                  table_id: 33554496
                  match {
                    field_id: 1
                    exact { value: "traffic-router-interface-5" }
                  }
                  match {
                    field_id: 2
                    exact {
                      value: "\376\200\000\000\000\000\000\000\002\032\021\377\376\027\000\200"
                    }
                  }
                  action {
                    action {
                      action_id: 16777217
                      params { param_id: 1 value: "\032\021\027\000\200" }
                    }
                  }
                }
              }
            }
          )pb")))
      .WillOnce(Return(absl::OkStatus()));

  // Nexthop entry.
  EXPECT_CALL(
      mock_write_request,
      Call(
          _, EqualsProto(R"pb(
            updates {
              type: INSERT
              entity {
                table_entry {
                  table_id: 33554498
                  match {
                    field_id: 1
                    exact { value: "traffic-nexthop-5" }
                  }
                  action {
                    action {
                      action_id: 16777236
                      params { param_id: 1 value: "traffic-router-interface-5" }
                      params {
                        param_id: 2
                        value: "\376\200\000\000\000\000\000\000\002\032\021\377\376\027\000\200"
                      }
                    }
                  }
                }
              }
            }
          )pb")))
      .WillOnce(Return(absl::OkStatus()));

  // IPv4 table entry.
  EXPECT_CALL(mock_write_request,
              Call(_, EqualsProto(R"pb(
                     updates {
                       type: INSERT
                       entity {
                         table_entry {
                           table_id: 33554500
                           match {
                             field_id: 1
                             exact { value: "traffic-vrf" }
                           }
                           match {
                             field_id: 2
                             lpm { value: "\x0a\x00\x00\x05" prefix_len: 32 }
                           }
                           action {
                             action {
                               action_id: 16777221
                               params { param_id: 1 value: "traffic-nexthop-5" }
                             }
                           }
                         }
                       }
                     }
                   )pb")))
      .WillOnce(Return(absl::OkStatus()));
  EXPECT_OK(ProgramIPv4Route(/*session=*/nullptr, /*port_id=*/5,
                             sai::GetIrP4Info(sai::Instantiation::kMiddleblock),
                             mock_write_request.AsStdFunction()));
}

TEST(BasicTraffic, ProgramL3AdmitTableEntry) {
  MockFunction<absl::Status(pdpi::P4RuntimeSession*, p4::v1::WriteRequest&)>
      mock_write_request;
  EXPECT_CALL(
      mock_write_request,
      Call(_, EqualsProto(R"pb(
             updates {
               type: INSERT
               entity {
                 table_entry {
                   table_id: 33554503
                   match {
                     field_id: 1
                     ternary { value: "\000" mask: "\001\000\000\000\000\000" }
                   }
                   action { action { action_id: 16777224 } }
                   priority: 1
                   metadata: "Experimental_type: VARIOUS_L3ADMIT_PUNTFLOW"
                 }
               }
             }
           )pb")))
      .WillOnce(Return(absl::OkStatus()));

  EXPECT_OK(ProgramL3AdmitTableEntry(
      /*session=*/nullptr, sai::GetIrP4Info(sai::Instantiation::kMiddleblock),
      mock_write_request.AsStdFunction()));
}

}  // namespace
}  // namespace pins_test::basic_traffic
