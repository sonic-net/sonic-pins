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
#include <iostream>
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
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4rt_app/p4runtime/p4runtime_impl.h"
#include "p4rt_app/tests/lib/p4runtime_component_test_fixture.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

namespace p4rt_app {
namespace {

class P4ConstraintsTest : public test_lib::P4RuntimeComponentTestFixture {
 public:
  static void SetUpTestSuite() {
    // Insert log marker to indicate where "actual test" log begins.
    // Everything up to this marker is stripped for golden testing.
    std::cout << "### START OF GOLDEN OUTPUT ###############################\n";
  }

 protected:
  P4ConstraintsTest()
      : test_lib::P4RuntimeComponentTestFixture(
            sai::Instantiation::kFabricBorderRouter) {}

  // Sends the given write request to P4RT app and prints the request and the
  // resulting response to stdout for the purpose of golden testing.
  absl::Status SendIrWriteRequestAndPrintGoldenOutput(
      absl::string_view ir_request_pb_string);
};

absl::Status P4ConstraintsTest::SendIrWriteRequestAndPrintGoldenOutput(
    absl::string_view ir_request_pb_string) {
  ASSIGN_OR_RETURN(
      pdpi::IrWriteRequest ir_request,
      gutil::ParseTextProto<pdpi::IrWriteRequest>(ir_request_pb_string));
  ASSIGN_OR_RETURN(p4::v1::WriteRequest pi_request,
                   pdpi::IrWriteRequestToPi(ir_p4_info_, ir_request));

  std::cout << "=== Test: "
            << testing::UnitTest::GetInstance()->current_test_info()->name()
            << " ===\n";
  std::cout << "--- INPUT: WriteRequest ------------------------------------\n";
  std::cout << gutil::PrintTextProto(ir_request);
  std::cout << "--- OUTPUT: WriteResponse ----------------------------------\n";
  absl::Status response =
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), pi_request);
  std::cout << gutil::StableStatusToString(response);
  return absl::OkStatus();
}

TEST_F(P4ConstraintsTest,
       AclIngressRequiresIPMatchFieldWhenUsingEcnMatchField) {
  EXPECT_OK(SendIrWriteRequestAndPrintGoldenOutput(R"pb(
    updates {
      type: INSERT
      entity {
        table_entry {
          table_name: "acl_ingress_table"
          matches {
            name: "dst_mac"
            ternary {
              value { mac: "02:02:02:02:02:02" }
              mask { mac: "ff:ff:ff:ff:ff:ff" }
            }
          }
          matches {
            name: "ecn"
            ternary {
              value { hex_str: "0x3" }
              mask { hex_str: "0x3" }
            }
          }
          priority: 1
          action {
            name: "acl_copy"
            params {
              name: "qos_queue"
              value { str: "2" }
            }
          }
        }
      }
    })pb"));
}

TEST_F(P4ConstraintsTest, MulticastGroupIdZeroIsRejected) {
  EXPECT_OK(SendIrWriteRequestAndPrintGoldenOutput(R"pb(
    updates {
      type: INSERT
      entity {
        table_entry {
          table_name: "ipv4_multicast_table"
          priority: 0
          matches {
            name: "ipv4_dst"
            exact { ipv4: "225.10.20.32" }
          }
          matches {
            name: "vrf_id"
            exact { str: "vrf-80" }
          }
          action {
            name: "set_multicast_group_id"
            params {
              name: "multicast_group_id"
              value { hex_str: "0x0000" }
            }
          }
        }
      }
    }
  )pb"));
}

TEST_F(P4ConstraintsTest, AclEgressTableDisallowsIpEtherTypeMatches) {
  // Configure P4RT port id "518", so P4RT app allows us to match on it.
  ASSERT_OK(
      p4rt_service_.GetP4rtServer().AddPortTranslation("Ethernet4", "518"));

  // Incorrect table entry, matching on IPv4 EtherType.
  EXPECT_OK(SendIrWriteRequestAndPrintGoldenOutput(R"pb(
    updates {
      type: INSERT
      entity {
        table_entry {
          table_name: "acl_egress_table"
          matches {
            name: "ether_type"
            ternary {
              value { hex_str: "0x0800" }
              mask { hex_str: "0xffff" }
            }
          }
          matches {
            name: "ip_protocol"
            ternary {
              value { hex_str: "0x11" }
              mask { hex_str: "0xff" }
            }
          }
          matches {
            name: "l4_dst_port"
            ternary {
              value { hex_str: "0x03ea" }
              mask { hex_str: "0xffff" }
            }
          }
          matches {
            name: "out_port"
            optional { value { str: "518" } }
          }
          priority: 3100
          action { name: "acl_drop" }
        }
      }
    })pb"));

  // Corrected table entry, matching on is_ipv4 = 1 instead.
  EXPECT_OK(SendIrWriteRequestAndPrintGoldenOutput(R"pb(
    updates {
      type: INSERT
      entity {
        table_entry {
          table_name: "acl_egress_table"
          matches {
            name: "is_ipv4"
            optional { value { hex_str: "0x1" } }
          }
          matches {
            name: "ip_protocol"
            ternary {
              value { hex_str: "0x11" }
              mask { hex_str: "0xff" }
            }
          }
          matches {
            name: "l4_dst_port"
            ternary {
              value { hex_str: "0x03ea" }
              mask { hex_str: "0xffff" }
            }
          }
          matches {
            name: "out_port"
            optional { value { str: "518" } }
          }
          priority: 3100
          action { name: "acl_drop" }
        }
      }
    })pb"));
}

}  // namespace
}  // namespace p4rt_app
