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

#include "tests/qos/cpu_qos_test.h"

#include <cstdint>
#include <string>
#include <vector>

#include "absl/cleanup/cleanup.h"
#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/strings/escaping.h"
#include "absl/strings/match.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/time.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "include/nlohmann/json.hpp"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/ixia_helper.h"
#include "lib/p4rt/packet_listener.h"
#include "lib/validator/validator_lib.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/netaddr/mac_address.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_pdpi/pd.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/proto/generic_testbed.pb.h"
#include "thinkit/switch.h"

namespace pins_test {
namespace {

struct QueueInfo {
  std::string gnmi_queue_name;      // Openconfig queue name.
  std::string p4_queue_name;        // P4 queue name.
  int rate_packets_per_second = 0;  // Rate of packets in packets per second.
};

absl::StatusOr<absl::flat_hash_map<std::string, QueueInfo>>
GetDefaultQueueInfo() {
  return absl::flat_hash_map<std::string, QueueInfo>{
      {"BE1", QueueInfo{"BE1", "0x2", 120}},
      {"AF1", QueueInfo{"AF1", "0x3", 120}},
      {"AF2", QueueInfo{"AF2", "0x4", 800}},
      {"AF3", QueueInfo{"AF3", "0x5", 120}},
      {"AF4", QueueInfo{"AF4", "0x6", 4000}},
      {"LLQ1", QueueInfo{"LLQ1", "0x0", 800}},
      {"LLQ2", QueueInfo{"LLQ2", "0x1", 800}},
      {"NC1", QueueInfo{"NC1", "0x7", 16000}},
  };
}

// Set up the switch to punt packets to CPU.
absl::Status SetUpPuntToCPU(const netaddr::MacAddress &dmac,
                            const netaddr::Ipv4Address &src_ip,
                            const netaddr::Ipv4Address &dst_ip,
                            absl::string_view p4_queue,
                            const p4::config::v1::P4Info &p4info,
                            pdpi::P4RuntimeSession &p4_session) {
  ASSIGN_OR_RETURN(auto ir_p4info, pdpi::CreateIrP4Info(p4info));
  RETURN_IF_ERROR(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      &p4_session,
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT, p4info))
      << "SetForwardingPipelineConfig: Failed to push P4Info: ";

  RETURN_IF_ERROR(pdpi::ClearTableEntries(&p4_session));
  auto acl_entry = gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
      R"pb(
        acl_ingress_table_entry {
          match {
            dst_mac { value: "$0" mask: "ff:ff:ff:ff:ff:ff" }
            is_ipv4 { value: "0x1" }
            src_ip { value: "$1" mask: "255.255.255.255" }
            dst_ip { value: "$2" mask: "255.255.255.255" }
          }
          action { trap { qos_queue: "$3" } }
          priority: 1
        }
      )pb",
      dmac.ToString(), src_ip.ToString(), dst_ip.ToString(), p4_queue));
  std::vector<p4::v1::TableEntry> pi_entries;
  ASSIGN_OR_RETURN(
      pi_entries.emplace_back(), pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, acl_entry),
      _.SetPrepend() << "Failed in PD table conversion to PI, entry: "
                     << acl_entry.DebugString() << " error: ");

  LOG(INFO) << "InstallPiTableEntries";
  return pdpi::InstallPiTableEntries(&p4_session, ir_p4info, pi_entries);
}

// These are the counters we track in these tests.
struct QueueCounters {
  int64_t num_packets_transmitted = 0;
  int64_t num_packet_dropped = 0;
};

// TODO: Move this to a helper library.
absl::StatusOr<QueueCounters> GetGnmiQueueStat(
    absl::string_view port, absl::string_view queue,
    gnmi::gNMI::StubInterface &gnmi_stub) {
  QueueCounters counters;
  const std::string openconfig_transmit_count_state_path = absl::Substitute(
      "qos/interfaces/interface[interface-id=$0]"
      "/output/queues/queue[name=$1]/state/transmit-pkts",
      port, queue);

  ASSIGN_OR_RETURN(
      std::string transmit_counter_response,
      GetGnmiStatePathInfo(&gnmi_stub, openconfig_transmit_count_state_path,
                           "openconfig-qos:transmit-pkts"));

  if (!absl::SimpleAtoi(StripQuotes(transmit_counter_response),
                        &counters.num_packets_transmitted)) {
    return absl::InternalError(absl::StrCat("Unable to parse counter from ",
                                            transmit_counter_response));
  }

  const std::string openconfig_drop_count_state_path = absl::Substitute(
      "qos/interfaces/interface[interface-id=$0]"
      "/output/queues/queue[name=$1]/state/dropped-pkts",
      port, queue);

  ASSIGN_OR_RETURN(
      std::string drop_counter_response,
      GetGnmiStatePathInfo(&gnmi_stub, openconfig_drop_count_state_path,
                           "openconfig-qos:dropped-pkts"));

  if (!absl::SimpleAtoi(StripQuotes(drop_counter_response),
                        &counters.num_packet_dropped)) {
    return absl::InternalError(
        absl::StrCat("Unable to parse counter from ", drop_counter_response));
  }

  return counters;
}

absl::Status SetPortSpeed(const std::string &port_speed,
                          const std::string &iface,
                          gnmi::gNMI::StubInterface &gnmi_stub) {
  std::string ops_config_path = absl::StrCat(
      "interfaces/interface[name=", iface, "]/ethernet/config/port-speed");
  std::string ops_val =
      absl::StrCat("{\"openconfig-if-ethernet:port-speed\":", port_speed, "}");
  RETURN_IF_ERROR(pins_test::SetGnmiConfigPath(&gnmi_stub, ops_config_path,
                                               GnmiSetType::kUpdate, ops_val));
  return absl::OkStatus();
}

absl::StatusOr<bool> CheckLinkUp(const std::string &iface,
                                 gnmi::gNMI::StubInterface &gnmi_stub) {
  std::string oper_status_state_path =
      absl::StrCat("interfaces/interface[name=", iface, "]/state/oper-status");
  std::string parse_str = "openconfig-interfaces:oper-status";
  ASSIGN_OR_RETURN(
      std::string ops_response,
      GetGnmiStatePathInfo(&gnmi_stub, oper_status_state_path, parse_str));
  return ops_response == "\"UP\"";
}

TEST_P(CpuQosIxiaTestFixture, TestCPUQueueRateLimit) {
  // Pick a testbed with an Ixia Traffic Generator.
  auto requirements =
      gutil::ParseProtoOrDie<thinkit::TestRequirements>(
          R"pb(interface_requirements {
                 count: 1
                 interface_mode: TRAFFIC_GENERATOR
               })pb");

  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<thinkit::GenericTestbed> generic_testbed,
      GetParam().testbed_interface->GetTestbedWithRequirements(requirements));

  ASSERT_OK(generic_testbed->Environment().StoreTestArtifact(
      "gnmi_config.txt", GetParam().gnmi_config));

  thinkit::Switch& sut = generic_testbed->Sut();

  // Connect to TestTracker for test status.
  if (auto &id = GetParam().test_case_id; id.has_value()) {
    generic_testbed->Environment().SetTestCaseID(*id);
  }

  // Push GNMI config.
  ASSERT_OK(pins_test::PushGnmiConfig(sut, GetParam().gnmi_config));

  // Hook up to GNMI.
  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, sut.CreateGnmiStub());

  // Get Queues
  // TODO: Extract Queue info from config instead of hardcoded
  // default.
  ASSERT_OK_AND_ASSIGN(auto queues, GetDefaultQueueInfo());

  // Set up P4Runtime session.
  // TODO: Use `CreateWithP4InfoAndClearTables` cl/397193959 when
  // its available.
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<pdpi::P4RuntimeSession> sut_p4_session,
                       pdpi::P4RuntimeSession::Create(generic_testbed->Sut()));
  auto clear_table_entries = absl::Cleanup(
      [&]() { ASSERT_OK(pdpi::ClearTableEntries(sut_p4_session.get())); });

  // Flow details.
  const auto dest_mac = netaddr::MacAddress(02, 02, 02, 02, 02, 02);
  const auto source_mac = netaddr::MacAddress(00, 01, 02, 03, 04, 05);
  const auto source_ip = netaddr::Ipv4Address(192, 168, 10, 1);
  const auto dest_ip = netaddr::Ipv4Address(172, 0, 0, 1);

  // BE1 is guaranteed to exist in the map which is currently hardocoded
  // and we will test for BE1 queue.
  // TODO: When we replace hardcoding with extraction of members
  // from the config, we need to add iteration logic to go over the configured
  // queues.
  QueueInfo queue_under_test = queues["BE1"];

  ASSERT_OK(SetUpPuntToCPU(dest_mac, source_ip, dest_ip,
                           queue_under_test.p4_queue_name, GetParam().p4info,
                           *sut_p4_session));

  static constexpr absl::Duration kPollInterval = absl::Seconds(5);
  static constexpr absl::Duration kTotalTime = absl::Seconds(30);
  static const int kIterations = kTotalTime / kPollInterval;

  QueueCounters final_counters;
  QueueCounters delta_counters;
  // Check for counters every 5 seconds upto 30 seconds till they match.
  for (int gnmi_counters_check = 0; gnmi_counters_check < kIterations;
       gnmi_counters_check++) {
    absl::SleepFor(kPollInterval);

    ASSERT_OK_AND_ASSIGN(
        final_counters,
        GetGnmiQueueStat("CPU", queue_under_test.gnmi_queue_name, *gnmi_stub));
  }
}

}  // namespace
}  // namespace pins_test
