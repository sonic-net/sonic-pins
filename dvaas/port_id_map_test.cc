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

#include "dvaas/port_id_map.h"

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "lib/p4rt/p4rt_port.h"

namespace dvaas {
namespace {

using gutil::IsOkAndHolds;
using gutil::StatusIs;
using pins_test::P4rtPortId;
using testing::Eq;

TEST(MirrorTestbedP4rtPortIdMap,
     ReturnsErrorWhenPortNotFoundGivenControlToSutMapping) {
  ASSERT_OK_AND_ASSIGN(const auto port_1,
                       P4rtPortId::MakeFromP4rtEncoding("1"));
  ASSERT_OK_AND_ASSIGN(const auto port_2,
                       P4rtPortId::MakeFromP4rtEncoding("2"));
  ASSERT_OK_AND_ASSIGN(const auto port_3,
                       P4rtPortId::MakeFromP4rtEncoding("3"));

  ASSERT_OK_AND_ASSIGN(
      const auto port_id_map,
      MirrorTestbedP4rtPortIdMap::CreateFromControlSwitchToSutPortMap(
          {{port_1, port_2}}));

  // Control -> SUT.
  ASSERT_THAT(port_id_map.GetSutPortConnectedToControlSwitchPort(port_2),
              StatusIs(absl::StatusCode::kNotFound));
  ASSERT_THAT(port_id_map.GetSutPortConnectedToControlSwitchPort(port_3),
              StatusIs(absl::StatusCode::kNotFound));

  // SUT -> Control.
  ASSERT_THAT(port_id_map.GetControlSwitchPortConnectedToSutPort(port_1),
              StatusIs(absl::StatusCode::kNotFound));
  ASSERT_THAT(port_id_map.GetControlSwitchPortConnectedToSutPort(port_3),
              StatusIs(absl::StatusCode::kNotFound));
}

TEST(MirrorTestbedP4rtPortIdMap,
     ReturnsErrorWhenGivenControlToSutMappingIsNotBijective) {
  ASSERT_OK_AND_ASSIGN(const auto port_1,
                       P4rtPortId::MakeFromP4rtEncoding("1"));
  ASSERT_OK_AND_ASSIGN(const auto port_2,
                       P4rtPortId::MakeFromP4rtEncoding("2"));
  ASSERT_OK_AND_ASSIGN(const auto port_3,
                       P4rtPortId::MakeFromP4rtEncoding("3"));

  ASSERT_THAT(MirrorTestbedP4rtPortIdMap::CreateFromControlSwitchToSutPortMap({
                  {port_1, port_3},
                  {port_2, port_3},
              }),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(MirrorTestbedP4rtPortIdMap,
     ReturnsErrorWhenPortNotFoundGivenSutToControlMapping) {
  ASSERT_OK_AND_ASSIGN(const auto port_1,
                       P4rtPortId::MakeFromP4rtEncoding("1"));
  ASSERT_OK_AND_ASSIGN(const auto port_2,
                       P4rtPortId::MakeFromP4rtEncoding("2"));
  ASSERT_OK_AND_ASSIGN(const auto port_3,
                       P4rtPortId::MakeFromP4rtEncoding("3"));

  ASSERT_OK_AND_ASSIGN(
      const auto port_id_map,
      MirrorTestbedP4rtPortIdMap::CreateFromSutToControlSwitchPortMap(
          {{port_1, port_2}}));

  // Control -> SUT.
  ASSERT_THAT(port_id_map.GetSutPortConnectedToControlSwitchPort(port_1),
              StatusIs(absl::StatusCode::kNotFound));
  ASSERT_THAT(port_id_map.GetSutPortConnectedToControlSwitchPort(port_3),
              StatusIs(absl::StatusCode::kNotFound));

  // SUT -> Control.
  ASSERT_THAT(port_id_map.GetControlSwitchPortConnectedToSutPort(port_2),
              StatusIs(absl::StatusCode::kNotFound));
  ASSERT_THAT(port_id_map.GetControlSwitchPortConnectedToSutPort(port_3),
              StatusIs(absl::StatusCode::kNotFound));
}

TEST(MirrorTestbedP4rtPortIdMap,
     ReturnsErrorWhenGivenSutToControlMappingIsNotBijective) {
  ASSERT_OK_AND_ASSIGN(const auto port_1,
                       P4rtPortId::MakeFromP4rtEncoding("1"));
  ASSERT_OK_AND_ASSIGN(const auto port_2,
                       P4rtPortId::MakeFromP4rtEncoding("2"));
  ASSERT_OK_AND_ASSIGN(const auto port_3,
                       P4rtPortId::MakeFromP4rtEncoding("3"));

  ASSERT_THAT(MirrorTestbedP4rtPortIdMap::CreateFromSutToControlSwitchPortMap({
                  {port_1, port_3},
                  {port_2, port_3},
              }),
              StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST(MirrorTestbedP4rtPortIdMap, ReturnsCorrectPortGivenSutToControlMapping) {
  ASSERT_OK_AND_ASSIGN(const auto port_1,
                       P4rtPortId::MakeFromP4rtEncoding("1"));
  ASSERT_OK_AND_ASSIGN(const auto port_2,
                       P4rtPortId::MakeFromP4rtEncoding("2"));
  ASSERT_OK_AND_ASSIGN(const auto port_3,
                       P4rtPortId::MakeFromP4rtEncoding("3"));
  ASSERT_OK_AND_ASSIGN(const auto port_4,
                       P4rtPortId::MakeFromP4rtEncoding("4"));

  ASSERT_OK_AND_ASSIGN(
      const auto port_id_map,
      MirrorTestbedP4rtPortIdMap::CreateFromSutToControlSwitchPortMap({
          {port_1, port_2},
          {port_3, port_4},
      }));

  // Control -> SUT.
  ASSERT_THAT(port_id_map.GetSutPortConnectedToControlSwitchPort(port_2),
              IsOkAndHolds(Eq(port_1)));
  ASSERT_THAT(port_id_map.GetSutPortConnectedToControlSwitchPort(port_4),
              IsOkAndHolds(Eq(port_3)));

  // SUT -> Control.
  ASSERT_THAT(port_id_map.GetControlSwitchPortConnectedToSutPort(port_1),
              IsOkAndHolds(Eq(port_2)));
  ASSERT_THAT(port_id_map.GetControlSwitchPortConnectedToSutPort(port_3),
              IsOkAndHolds(Eq(port_4)));
}

TEST(MirrorTestbedP4rtPortIdMap, ReturnsCorrectPortWithImplicitIdentityMap) {
  const auto port_id_map = MirrorTestbedP4rtPortIdMap::CreateIdentityMap();
  ASSERT_OK_AND_ASSIGN(const auto port_1,
                       P4rtPortId::MakeFromP4rtEncoding("1"));
  ASSERT_OK_AND_ASSIGN(const auto port_2,
                       P4rtPortId::MakeFromP4rtEncoding("2"));

  // Control -> SUT.
  ASSERT_THAT(port_id_map.GetSutPortConnectedToControlSwitchPort(port_1),
              IsOkAndHolds(Eq(port_1)));
  ASSERT_THAT(port_id_map.GetSutPortConnectedToControlSwitchPort(port_2),
              IsOkAndHolds(Eq(port_2)));

  // SUT -> Control.
  ASSERT_THAT(port_id_map.GetControlSwitchPortConnectedToSutPort(port_1),
              IsOkAndHolds(Eq(port_1)));
  ASSERT_THAT(port_id_map.GetControlSwitchPortConnectedToSutPort(port_2),
              IsOkAndHolds(Eq(port_2)));
}

TEST(MirrorTestbedP4rtPortIdMap, IsImplicitIdentityMapReturnsCorrectValue) {
  {
    const auto identity_map = MirrorTestbedP4rtPortIdMap::CreateIdentityMap();
    ASSERT_TRUE(identity_map.IsImplicitIdentityMap());
  }

  {
    ASSERT_OK_AND_ASSIGN(const auto port_1,
                         P4rtPortId::MakeFromP4rtEncoding("1"));
    ASSERT_OK_AND_ASSIGN(const auto port_2,
                         P4rtPortId::MakeFromP4rtEncoding("2"));
    ASSERT_OK_AND_ASSIGN(
        const auto port_id_map,
        MirrorTestbedP4rtPortIdMap::CreateFromSutToControlSwitchPortMap({
            {port_1, port_2},
        }));
    ASSERT_FALSE(port_id_map.IsImplicitIdentityMap());
  }
}

TEST(MirrorTestbedP4rtPortIdMap, GetMappedSutPortsReturnsErrorForImplicitMap) {
  const auto identity_map = MirrorTestbedP4rtPortIdMap::CreateIdentityMap();
  ASSERT_THAT(identity_map.GetMappedSutPorts(),
              StatusIs(absl::StatusCode::kFailedPrecondition));
}

TEST(MirrorTestbedP4rtPortIdMap, GetMappedSutPortsReturnsCorrectValue) {
  ASSERT_OK_AND_ASSIGN(const auto port_1,
                       P4rtPortId::MakeFromP4rtEncoding("1"));
  ASSERT_OK_AND_ASSIGN(const auto port_2,
                       P4rtPortId::MakeFromP4rtEncoding("2"));
  ASSERT_OK_AND_ASSIGN(const auto port_3,
                       P4rtPortId::MakeFromP4rtEncoding("3"));
  ASSERT_OK_AND_ASSIGN(const auto port_4,
                       P4rtPortId::MakeFromP4rtEncoding("4"));

  ASSERT_OK_AND_ASSIGN(
      const auto port_id_map,
      MirrorTestbedP4rtPortIdMap::CreateFromSutToControlSwitchPortMap({
          {port_1, port_2},
          {port_3, port_4},
      }));
  ASSERT_THAT(port_id_map.GetMappedSutPorts(),
              IsOkAndHolds(testing::UnorderedElementsAre(port_1, port_3)));
}

}  // namespace
}  // namespace dvaas
