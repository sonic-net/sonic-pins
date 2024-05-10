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
#include "gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4rt_app/tests/lib/p4runtime_component_test_fixture.h"
#include "p4rt_app/tests/lib/p4runtime_request_helpers.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"

namespace p4rt_app {
namespace {

class P4ConstraintsTest : public test_lib::P4RuntimeComponentTestFixture {
 protected:
  P4ConstraintsTest()
      : test_lib::P4RuntimeComponentTestFixture(
            sai::Instantiation::kMiddleblock) {}
};

TEST_F(P4ConstraintsTest,
       AclIngressRequiresIPMatchFieldWhenUsingEcnMatchField) {
  pdpi::IrWriteRequest ir_request =
      gutil::ParseProtoOrDie<pdpi::IrWriteRequest>(
          R"pb(updates {
                 type: INSERT
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
               })pb");

  // P4 write request.
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest pi_request,
      test_lib::IrWriteRequestToPi(ir_request.DebugString(), ir_p4_info_));

  // Used to strip unnecessary lines for golden testing.
  std::cout << "### REMOVE UP TO HERE ######################################\n";

  std::cout << "=== Test: "
            << testing::UnitTest::GetInstance()->current_test_info()->name()
            << " ===\n";
  std::cout << "--- INPUT: WriteRequest ------------------------------------\n";
  std::cout << gutil::PrintTextProto(ir_request);
  std::cout << "--- OUTPUT: WriteResponse ----------------------------------\n";
  absl::Status response =
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), pi_request);
  std::cout << gutil::StableStatusToString(response);
}

}  // namespace
}  // namespace p4rt_app
