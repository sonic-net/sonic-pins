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
#include <string>
#include <utility>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "grpcpp/security/credentials.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4rt_app/tests/lib/p4runtime_component_test_fixture.h"
#include "p4rt_app/tests/lib/p4runtime_grpc_service.h"
#include "p4rt_app/tests/lib/p4runtime_request_helpers.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "swss/component_state_helper_interface.h"
#include "swss/fakes/fake_component_state_helper.h"

namespace p4rt_app {
namespace {

using ::gutil::StatusIs;
using ::testing::HasSubstr;

// Testing end-to-end features relating to how we handle critical state.
class CriticalStateTest : public test_lib::P4RuntimeComponentTestFixture {
 protected:
  CriticalStateTest()
      : test_lib::P4RuntimeComponentTestFixture(
            sai::Instantiation::kMiddleblock) {}
};

TEST_F(CriticalStateTest, PipelineConfgIsRejectedWhenCritical) {
  p4rt_service_.GetComponentStateHelper().ReportComponentState(
      swss::ComponentState::kInactive, "some reason");
  EXPECT_THAT(
      pdpi::SetMetadataAndSetForwardingPipelineConfig(
          p4rt_session_.get(),
          p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
          p4_info_),
      StatusIs(absl::StatusCode::kInternal, HasSubstr("some reason")));
}

TEST_F(CriticalStateTest, WriteRequestIsRejectedWhenCritical) {
  // Verify we can send a write while NOT in a critical state.
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest request,
      test_lib::PdWriteRequestToPi(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                ipv4_table_entry {
                  match {
                    vrf_id: "50"
                    ipv4_dst { value: "10.81.8.0" prefix_length: 23 }
                  }
                  action { set_nexthop_id { nexthop_id: "8" } }
                }
              }
            }
          )pb",
          ir_p4_info_));
  ASSERT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));

  // Set the switch into critical state.
  p4rt_service_.GetComponentStateHelper().ReportComponentState(
      swss::ComponentState::kInactive, "some reason");

  // Try writing again. We should fail with an INTERNAL error.
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kInternal, HasSubstr("some reason")));
}

TEST_F(CriticalStateTest, CanReadWhileCritical) {
  // Write an entry which we can read back out.
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest request,
      test_lib::PdWriteRequestToPi(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                ipv4_table_entry {
                  match {
                    vrf_id: "50"
                    ipv4_dst { value: "10.81.8.0" prefix_length: 23 }
                  }
                  action { set_nexthop_id { nexthop_id: "8" } }
                }
              }
            }
          )pb",
          ir_p4_info_));
  ASSERT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));

  // Set the switch into critical state.
  p4rt_service_.GetComponentStateHelper().ReportComponentState(
      swss::ComponentState::kInactive, "some reason");

  // Read should still work and return the table entry.
  p4::v1::ReadRequest read_request;
  read_request.add_entities()->mutable_table_entry();
  ASSERT_OK_AND_ASSIGN(
      p4::v1::ReadResponse read_response,
      pdpi::SetMetadataAndSendPiReadRequest(p4rt_session_.get(), read_request));
  EXPECT_EQ(read_response.entities_size(), 1);
}

TEST_F(CriticalStateTest, UnexpectedOrchAgentResponseCausesCritical) {
  ASSERT_OK_AND_ASSIGN(
      p4::v1::WriteRequest request,
      test_lib::PdWriteRequestToPi(
          R"pb(
            updates {
              type: INSERT
              table_entry {
                ipv4_table_entry {
                  match {
                    vrf_id: "50"
                    ipv4_dst { value: "10.81.8.0" prefix_length: 23 }
                  }
                  action { set_nexthop_id { nexthop_id: "8" } }
                }
              }
            }
          )pb",
          ir_p4_info_));

  // Force the response path to return an unexpected notification key.
  p4rt_service_.GetP4rtAppDbTable().PushNotification(/*key=*/"out_of_order");

  // The P4RT App should be the only writer to the P4RT table. Seeing an
  // unexpected response means the layers have gotten out of sync, and we should
  // go critical.
  EXPECT_THAT(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request),
      StatusIs(absl::StatusCode::kInternal));
}

}  // namespace
}  // namespace p4rt_app
