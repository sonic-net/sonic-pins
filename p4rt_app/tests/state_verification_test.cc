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
// limitations under the License."
#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "p4rt_app/tests/lib/app_db_entry_builder.h"
#include "p4rt_app/tests/lib/p4runtime_component_test_fixture.h"
#include "p4rt_app/tests/lib/p4runtime_request_helpers.h"
#include "sai_p4/instantiations/google/instantiations.h"

namespace p4rt_app {
namespace {

using ::gutil::StatusIs;
using ::testing::HasSubstr;

class StateVerificationTest : public test_lib::P4RuntimeComponentTestFixture {
 protected:
  StateVerificationTest()
      : test_lib::P4RuntimeComponentTestFixture(
            sai::Instantiation::kMiddleblock) {}
};

TEST_F(StateVerificationTest, VerifyEntriesInAppDbAndAppStateDbTables) {
  // Add VRF entries.
  p4rt_service_.GetVrfAppStateDbTable().InsertTableEntry(
      /*key=*/"vrf_match",
      /*values=*/{{"action", "action0"}});
  p4rt_service_.GetVrfAppDbTable().InsertTableEntry(
      /*key=*/"vrf_match",
      /*values=*/{{"action", "action0"}});

  // Add HASH entries.
  p4rt_service_.GetHashAppStateDbTable().InsertTableEntry(
      /*key=*/"hash_match",
      /*values=*/{{"action", "action0"}});
  p4rt_service_.GetHashAppDbTable().InsertTableEntry(
      /*key=*/"hash_match",
      /*values=*/{{"action", "action0"}});

  // Add SWITCH entries.
  p4rt_service_.GetSwitchAppStateDbTable().InsertTableEntry(
      /*key=*/"switch_match",
      /*values=*/{{"action", "action0"}});
  p4rt_service_.GetSwitchAppDbTable().InsertTableEntry(
      /*key=*/"switch_match",
      /*values=*/{{"action", "action0"}});

  EXPECT_OK(p4rt_service_.GetP4rtServer().VerifyState());

}

TEST_F(StateVerificationTest, EntryDoesNotExistInAppDbFails) {
  p4rt_service_.GetP4rtAppDbTable().InsertTableEntry(/*key=*/"foo",
                                                     /*values=*/{});
  p4rt_service_.GetVrfAppStateDbTable().InsertTableEntry(/*key=*/"bar",
                                                         /*values=*/{});
  EXPECT_THAT(
      p4rt_service_.GetP4rtServer().VerifyState(),
      StatusIs(absl::StatusCode::kUnknown, HasSubstr("AppDb is missing key")));
}

TEST_F(StateVerificationTest, EntryDoesNotExistInAppStateDbFails) {
  p4rt_service_.GetHashAppDbTable().InsertTableEntry(/*key=*/"foo",
                                                     /*values=*/{});
  p4rt_service_.GetSwitchAppDbTable().InsertTableEntry(/*key=*/"bar",
                                                       /*values=*/{});
  EXPECT_THAT(p4rt_service_.GetP4rtServer().VerifyState(),
              StatusIs(absl::StatusCode::kUnknown,
                       HasSubstr("AppStateDb is missing key")));
}

TEST_F(StateVerificationTest, EntryValuesAreDifferentFails) {
  p4rt_service_.GetHashAppStateDbTable().InsertTableEntry(
      /*key=*/"hash_match",
      /*values=*/{{"action", "state_action"}});
  p4rt_service_.GetHashAppDbTable().InsertTableEntry(
      /*key=*/"hash_match",
      /*values=*/{{"action", "different_action"}});

  EXPECT_THAT(p4rt_service_.GetP4rtServer().VerifyState(),
              StatusIs(absl::StatusCode::kUnknown, HasSubstr("do not match")));
}

TEST_F(StateVerificationTest, StateVerificationFailureRaisesAlarm) {
  p4rt_service_.GetP4rtAppDbTable().InsertTableEntry(/*key=*/"foo",
                                                     /*values=*/{});
  p4rt_service_.GetVrfAppStateDbTable().InsertTableEntry(/*key=*/"bar",
                                                         /*values=*/{});
  EXPECT_THAT(
      p4rt_service_.GetP4rtServer().VerifyState(),
      StatusIs(absl::StatusCode::kUnknown, HasSubstr("AppDb is missing key")));
}

TEST_F(StateVerificationTest, StateVerificationFailureNoAlarm) {
  p4rt_service_.GetP4rtAppDbTable().InsertTableEntry(/*key=*/"foo",
                                                     /*values=*/{});
  p4rt_service_.GetVrfAppStateDbTable().InsertTableEntry(/*key=*/"bar",
                                                         /*values=*/{});
  EXPECT_THAT(
      p4rt_service_.GetP4rtServer().VerifyState(),
      StatusIs(absl::StatusCode::kUnknown, HasSubstr("AppDb is missing key")));
}

TEST_F(StateVerificationTest, VerifyAppDbAndP4rtCacheEntries) {
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
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));

  // When state verification passes P4RT App should report being healthy.
  EXPECT_OK(p4rt_service_.GetP4rtServer().VerifyState());
//TODO(PINS): To handle Component State later.
//      /*update_component_state=*/true));
//  EXPECT_EQ(p4rt_service_.GetComponentStateHelper().StateInfo().state,
//            swss::ComponentState::kUp);
}

TEST_F(StateVerificationTest, VerifyFailsWhenAppDbDoesNotMatchP4rtCache) {
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
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));

  // Remove the entry from the AppDb.
  auto app_db_entry =
      test_lib::AppDbEntryBuilder{}
          .SetTableName("FIXED_NEIGHBOR_TABLE")
          .AddMatchField("neighbor_id", "fe80::21a:11ff:fe17:5f80")
          .AddMatchField("router_interface_id", "1");
  p4rt_service_.GetP4rtAppDbTable().DeleteTableEntry(app_db_entry.GetKey());

  // When state verification fails P4RT App should report a failure.
  EXPECT_THAT(
      p4rt_service_.GetP4rtServer().VerifyState(),
      StatusIs(absl::StatusCode::kUnknown, HasSubstr("is missing key")));
//TODO(PINS): To handle Component State later.
//          /*update_component_state=*/true),
//      StatusIs(absl::StatusCode::kUnknown, HasSubstr("is missing key")));
//  EXPECT_EQ(p4rt_service_.GetComponentStateHelper().StateInfo().state,
//            swss::ComponentState::kMinor);
}

TEST_F(StateVerificationTest, VerifyVrfEntriesAreIgnoredFromWriteRequests) {
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
            updates {
              type: INSERT
              table_entry {
                vrf_table_entry {
                  match { vrf_id: "vrf-0" }
                  action { no_action {} }
                }
              }
            }
          )pb",
          ir_p4_info_));
  EXPECT_OK(
      pdpi::SetMetadataAndSendPiWriteRequest(p4rt_session_.get(), request));

  // When state verification passes P4RT App should report being healthy.
  EXPECT_OK(p4rt_service_.GetP4rtServer().VerifyState());
// TODO(PINS): To handle Component State later.
//      /*update_component_state=*/true));
//  EXPECT_EQ(p4rt_service_.GetComponentStateHelper().StateInfo().state,
//            swss::ComponentState::kUp);
}

}  // namespace
}  // namespace p4rt_app
