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
#include "gutil/status_matchers.h"
#include "p4rt_app/tests/lib/p4runtime_component_test_fixture.h"
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

TEST_F(StateVerificationTest, VerifyEntriesInP4rtAndVrfTables) {
  // Add P4RT entries.
  p4rt_service_.GetP4rtAppStateDbTable().InsertTableEntry(
      /*key=*/"p4rt_match",
      /*values=*/{{"action", "action0"}});
  p4rt_service_.GetP4rtAppDbTable().InsertTableEntry(
      /*key=*/"p4rt_match",
      /*values=*/{{"action", "action0"}});

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

  EXPECT_OK(p4rt_service_.VerifyState());

}

TEST_F(StateVerificationTest, EntryDoesNotExistInAppDbFails) {
  p4rt_service_.GetP4rtAppStateDbTable().InsertTableEntry(/*key=*/"foo",
                                                          /*values=*/{});
  p4rt_service_.GetVrfAppStateDbTable().InsertTableEntry(/*key=*/"bar",
                                                         /*values=*/{});
  EXPECT_THAT(
      p4rt_service_.VerifyState(),
      StatusIs(absl::StatusCode::kUnknown, HasSubstr("AppDb is missing key")));
}

TEST_F(StateVerificationTest, EntryDoesNotExistInAppStateDbFails) {
  p4rt_service_.GetHashAppDbTable().InsertTableEntry(/*key=*/"foo",
                                                     /*values=*/{});
  p4rt_service_.GetSwitchAppDbTable().InsertTableEntry(/*key=*/"bar",
                                                       /*values=*/{});
  EXPECT_THAT(p4rt_service_.VerifyState(),
              StatusIs(absl::StatusCode::kUnknown,
                       HasSubstr("AppStateDb is missing key")));
}

TEST_F(StateVerificationTest, EntryValuesAreDifferentFails) {
  p4rt_service_.GetP4rtAppStateDbTable().InsertTableEntry(
      /*key=*/"p4rt_match",
      /*values=*/{{"action", "state_action"}});
  p4rt_service_.GetP4rtAppDbTable().InsertTableEntry(
      /*key=*/"p4rt_match",
      /*values=*/{{"action", "different_action"}});

  EXPECT_THAT(p4rt_service_.VerifyState(),
              StatusIs(absl::StatusCode::kUnknown, HasSubstr("do not match")));
}

TEST_F(StateVerificationTest, StateVerificationFailureRaisesAlarm) {
  p4rt_service_.GetP4rtAppStateDbTable().InsertTableEntry(/*key=*/"foo",
                                                          /*values=*/{});
  p4rt_service_.GetVrfAppStateDbTable().InsertTableEntry(/*key=*/"bar",
                                                         /*values=*/{});
  EXPECT_THAT(
      p4rt_service_.VerifyState(),
      StatusIs(absl::StatusCode::kUnknown, HasSubstr("AppDb is missing key")));
}

}  // namespace
}  // namespace p4rt_app
