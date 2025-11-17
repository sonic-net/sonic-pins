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

#include <string>
#include <vector>

#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto_matchers.h"
#include "gutil/gutil/status_matchers.h"  // IWYU pragma: keep
#include "gutil/gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/config/v1/p4types.pb.h"
#include "p4_infra/p4_pdpi/p4info_union_lib.h"

namespace pdpi {
namespace {

using ::gutil::EqualsProto;
using ::gutil::Partially;
using ::testing::SizeIs;

// Test that all new_types in each P4Info are included in the unioned P4Info,
// whether they are unique among all P4Infos or shared by some/all P4Infos.
TEST(P4InfoUnionTest, UnionTypeInfo) {
  constexpr int kNumberOfInfos = 50;
  constexpr absl::string_view kSharedNewTypeKey = "type_shared_by_all_p4infos";
  constexpr absl::string_view kSharedNewType = R"pb(
    translated_type { sdn_string {} }
    annotations: "shared_by_all_p4infos"
  )pb";

  std::vector<p4::config::v1::P4Info> infos;

  for (int i = 0; i < kNumberOfInfos; ++i) {
    infos.push_back(gutil::ParseProtoOrDie<p4::config::v1::P4Info>(
        absl::Substitute(R"pb(
                           type_info {
                             new_types {
                               key: "type_$0_t"
                               value { translated_type { sdn_string {} } }
                             }
                             new_types { key: "$1" value { $2 } }
                           }
                         )pb",
                         i, kSharedNewTypeKey, kSharedNewType)));
  }

  ASSERT_OK_AND_ASSIGN(p4::config::v1::P4Info unioned_p4info,
                       UnionP4info(infos));
  // Unioned P4Info should contain all kNumberOfInfo unique new_types plus
  // the one shared type.
  ASSERT_THAT(unioned_p4info.type_info().new_types(),
              SizeIs(kNumberOfInfos + 1));

  for (int i = 0; i < kNumberOfInfos; ++i) {
    std::string type_name = absl::Substitute("type_$0_t", i);
    ASSERT_TRUE(unioned_p4info.type_info().new_types().contains(type_name));
    EXPECT_THAT(unioned_p4info.type_info().new_types().at(type_name),
                EqualsProto(
                    R"pb(
                      translated_type { sdn_string {} }
                    )pb"));
  }
  ASSERT_TRUE(
      unioned_p4info.type_info().new_types().contains(kSharedNewTypeKey));
  EXPECT_THAT(unioned_p4info.type_info().new_types().at(kSharedNewTypeKey),
              EqualsProto(kSharedNewType));
}

TEST(P4InfoUnionTest, PlatformPropertiesUseMax) {
  // Any values work here as long as kMaxSize > kSmallerSize.
  constexpr int kMaxSize = 500;
  constexpr int kSmallerSize = 100;

  std::vector<p4::config::v1::P4Info> infos;

  p4::config::v1::PlatformProperties& platform_properties1 =
      *infos.emplace_back().mutable_pkg_info()->mutable_platform_properties();
  // multicast_group_table_size is unset.
  platform_properties1.set_multicast_group_table_total_replicas(kSmallerSize);
  platform_properties1.set_multicast_group_table_max_replicas_per_entry(
      kMaxSize);

  p4::config::v1::PlatformProperties& platform_properties2 =
      *infos.emplace_back().mutable_pkg_info()->mutable_platform_properties();
  platform_properties2.set_multicast_group_table_size(kMaxSize);
  // multicast_group_table_total_replicas is unset.
  platform_properties2.set_multicast_group_table_max_replicas_per_entry(
      kSmallerSize);

  p4::config::v1::PlatformProperties& platform_properties3 =
      *infos.emplace_back().mutable_pkg_info()->mutable_platform_properties();
  platform_properties3.set_multicast_group_table_size(kSmallerSize);
  platform_properties3.set_multicast_group_table_total_replicas(kMaxSize);
  // multicast_group_table_max_replicas_per_entry is unset.

  p4::config::v1::P4Info expected_p4info;
  p4::config::v1::PlatformProperties& expected_platform_properties =
      *expected_p4info.mutable_pkg_info()->mutable_platform_properties();
  expected_platform_properties.set_multicast_group_table_size(kMaxSize);
  expected_platform_properties.set_multicast_group_table_total_replicas(
      kMaxSize);
  expected_platform_properties.set_multicast_group_table_max_replicas_per_entry(
      kMaxSize);

  ASSERT_OK_AND_ASSIGN(p4::config::v1::P4Info unioned_p4info,
                       UnionP4info(infos));

  EXPECT_THAT(unioned_p4info, Partially(EqualsProto(expected_p4info)));
}

}  // namespace
}  // namespace pdpi
