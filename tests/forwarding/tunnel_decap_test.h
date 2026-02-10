// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#ifndef PINS_TESTS_FORWARDING_TUNNEL_DECAP_TEST_H_
#define PINS_TESTS_FORWARDING_TUNNEL_DECAP_TEST_H_

#include <memory>
#include <optional>
#include <string>

#include "dvaas/dataplane_validation.h"
#include "dvaas/test_vector.pb.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_infra/p4_pdpi/netaddr/ipv4_address.h"
#include "p4_infra/p4_pdpi/netaddr/ipv6_address.h"
#include "p4_infra/p4_pdpi/netaddr/mac_address.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"
#include "thinkit/mirror_testbed_fixture.h"
#include "gtest/gtest.h"

namespace pins_test {

enum class TunnelMatchType {
  kExactMatch,         // exact match on src-ip and dst-ip
  kTernaryMatchSrcIp,  // ternary match on src-ip and exact match on dst-ip
  kTernaryMatchDstIp,  // ternary match on dst-ip and exact match on src-ip
};

struct TunnelDecapTestParams {
  // Using a shared_ptr because parameterized tests require objects to be
  // copyable.
  std::shared_ptr<thinkit::MirrorTestbedInterface> mirror_testbed;
  // Pushed to the SUT if given, otherwise assumes the correct one is already
  // configured.
  std::optional<p4::config::v1::P4Info> sut_p4info;
  TunnelMatchType tunnel_type;
  dvaas::DataplaneValidationParams dvaas_params;
  std::shared_ptr<dvaas::DataplaneValidator> dvaas;
};

struct TunnelDecapTestVectorParams {
  std::string in_port;
  std::string out_port;
  netaddr::MacAddress dst_mac;
  netaddr::Ipv4Address inner_dst_ipv4;
  netaddr::Ipv6Address inner_dst_ipv6;
  netaddr::Ipv6Address dst_ipv6;
};

class TunnelDecapTestFixture
    : public testing::TestWithParam<TunnelDecapTestParams> {
public:
  void SetUp() override { GetParam().mirror_testbed->SetUp(); }

  void TearDown() override { GetParam().mirror_testbed->TearDown(); }
};

} // namespace pins_test

#endif // PINS_TESTS_FORWARDING_TUNNEL_DECAP_TEST_H_
