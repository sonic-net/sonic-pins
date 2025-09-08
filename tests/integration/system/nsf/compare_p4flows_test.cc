// Copyright 2025 Google LLC
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

#include "tests/integration/system/nsf/compare_p4flows.h"

#include <string_view>

#include "absl/status/status.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4/v1/p4runtime.pb.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace pins_test {
namespace {

using ::gutil::IsOk;
using ::gutil::StatusIs;
using ::p4::v1::ReadResponse;
using ::testing::HasSubstr;

constexpr std::string_view kVrfTableEntryWithSfeMetadata =
    R"pb(entities {
           table_entry {
             table_id: 33554506
             match {
               field_id: 1
               exact { value: "vrf-81" }
             }
             action { action { action_id: 24742814 } }
             metadata: "orion_type: SFE_VRF_SAIONLYENTRY"
           }
         })pb";

constexpr std::string_view kVrfTableEntryWithoutMetadata =
    R"pb(entities {
           table_entry {
             table_id: 33554506
             match {
               field_id: 1
               exact { value: "vrf-81" }
             }
             action { action { action_id: 24742814 } }
           }
         })pb";

constexpr std::string_view kVrfTableEntryWithSfeMetadata2 =
    R"pb(entities {
           table_entry {
             table_id: 33554506
             match {
               field_id: 1
               exact { value: "vrf-81" }
             }
             action { action { action_id: 24742815 } }
             metadata: "orion_type: SFE_VRF_SAIONLYENTRY"
           }
         })pb";

constexpr std::string_view kNonVrfTableEntryWithSfeMetadata =
    R"pb(entities {
           table_entry {
             table_id: 33554500
             match {
               field_id: 1
               exact { value: "vrf-81" }
             }
             action { action { action_id: 24742814 } }
             metadata: "orion_type: SFE_VRF_SAIONLYENTRY"
           }
         })pb";

constexpr std::string_view kNonVrfTableEntryWithSfeMetadata2 =
    R"pb(entities {
           table_entry {
             table_id: 33554500
             match {
               field_id: 1
               exact { value: "vrf-81" }
             }
             action { action { action_id: 24742814 } }
             metadata: "orion_type: SFE_VRF_SAIONLYENTRY"
           }
         })pb";

} // namespace
} // namespace pins_test
