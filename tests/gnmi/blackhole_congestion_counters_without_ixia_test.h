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
#ifndef PINS_TEST_GNMI_BLACKHOLE_CONGESTION_COUNTERS_WITHOUT_IXIA_TEST_H_
#define PINS_TEST_GNMI_BLACKHOLE_CONGESTION_COUNTERS_WITHOUT_IXIA_TEST_H_

#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "absl/memory/memory.h"
#include "absl/status/statusor.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/utils/generic_testbed_utils.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/generic_testbed_fixture.h"
#include "thinkit/ssh_client.h"

namespace pins_test {

struct LpmMissCounters {
  uint64_t port_in_packets;
  uint64_t port_in_discards;
  uint64_t switch_blackhole_lpm_miss_events;
  uint64_t switch_blackhole_in_discard_events;
  uint64_t switch_blackhole_events;
};

struct OutDiscardCounters {
  uint64_t port_out_packets;
  uint64_t port_out_discard_packets;
  uint64_t port_blackhole_out_discard_events;
  uint64_t switch_blackhole_out_discard_events;
  uint64_t switch_blackhole_events;
};

struct BlackholeCongestionCountersWithoutIxiaTestFixtureParams {
  thinkit::GenericTestbedInterface* testbed_interface;
  std::string gnmi_config;
  p4::config::v1::P4Info p4_info;
  thinkit::SSHClient* ssh_client;
};

class BlackholeCongestionCountersWithoutIxiaTestFixture
    : public thinkit::GenericTestbedFixture<
          BlackholeCongestionCountersWithoutIxiaTestFixtureParams> {
 protected:
  void SetUp() override;
  void TearDown() override;
  absl::StatusOr<LpmMissCounters> TriggerLpmMisses(
      sai::IpVersion ip_version, uint32_t lpm_miss_packets_count,
      uint32_t lpm_hit_packets_count);
  absl::StatusOr<OutDiscardCounters> TriggerOutDiscards(
      uint32_t out_discards_count, uint32_t out_packets_count);
  std::unique_ptr<thinkit::GenericTestbed> generic_testbed_;
  std::unique_ptr<gnmi::gNMI::StubInterface> gnmi_stub_;
  std::vector<InterfaceLink> control_links_;
  std::unique_ptr<pdpi::P4RuntimeSession> sut_p4_session_;
  // Takes ownership of the SSHClient parameter.
  std::unique_ptr<thinkit::SSHClient> ssh_client_ =
      absl::WrapUnique<thinkit::SSHClient>(this->GetParam().ssh_client);
};

}  // namespace pins_test

#endif  // PINS_TEST_GNMI_BLACKHOLE_CONGESTION_COUNTERS_WITHOUT_IXIA_TEST_H_
