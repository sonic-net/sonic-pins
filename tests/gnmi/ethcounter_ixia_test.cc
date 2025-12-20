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
//
// To run this test:
// /google/data/ro/teams/biglab/biglab sandman -p pins -t ${TESTBED}.gcl
// --skip_confirmation --lock_priority 2 then from google3 directory run:
// platforms/networking/pins/testing/integration/system:ethcounter_ixia_test
// (this file)
//
// TODO: Resolve whole save/restore thing wrt speed?

#include "tests/gnmi/ethcounter_ixia_test.h"

#include <cstdint>
#include <cwchar>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/cleanup/cleanup.h"
#include "absl/container/flat_hash_map.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/optional.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "include/nlohmann/json.hpp"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/ixia_helper.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/netaddr/mac_address.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_pdpi/pd.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "tests/forwarding/util.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/proto/generic_testbed.pb.h"
#include "thinkit/switch.h"

namespace pins_test {

using ::nlohmann::json;

namespace {
constexpr char kOpsDown[] = "\"DOWN\"";  // NOLINT
constexpr char kOpsUp[] = "\"UP\"";

constexpr char kSpeed100GB[] = "\"openconfig-if-ethernet:SPEED_100GB\"";
constexpr char kSpeed200GB[] = "\"openconfig-if-ethernet:SPEED_200GB\"";

constexpr uint32_t kMtu = 1514;
}  // namespace

// TrapToCPU - Set up the switch to punt ingress packets to the CPU
//
// The rules will punt all matching packets to the CPU.
//
absl::Status TrapToCPU(thinkit::Switch &sut,
                       const p4::config::v1::P4Info &p4info) {
  auto acl_entry = gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
      R"pb(
        acl_ingress_table_entry {
          match {
            dst_mac { value: "02:02:02:02:02:02" mask: "ff:ff:ff:ff:ff:ff" }
          }
          action { trap { qos_queue: "0x2" } }
          priority: 1
        }
      )pb"));

  LOG(INFO) << "p4_stub";
  ASSIGN_OR_RETURN(std::unique_ptr<p4::v1::P4Runtime::StubInterface> p4_stub,
                   sut.CreateP4RuntimeStub());

  LOG(INFO) << "p4_session";
  ASSIGN_OR_RETURN(
      std::unique_ptr<pdpi::P4RuntimeSession> p4_session,
      pdpi::P4RuntimeSession::Create(std::move(p4_stub), sut.DeviceId()));

  LOG(INFO) << "CreateIrP4Info";
  ASSIGN_OR_RETURN(auto ir_p4info, pdpi::CreateIrP4Info(p4info));

  LOG(INFO) << "SetForwardingPipelineConfig";
  RETURN_IF_ERROR(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      p4_session.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT, p4info))
      << "SetForwardingPipelineConfig: Failed to push P4Info: ";

  LOG(INFO) << "ClearTableEntries";
  RETURN_IF_ERROR(pdpi::ClearTableEntries(p4_session.get()));
  // Check that switch is in a clean state.
  ASSIGN_OR_RETURN(auto read_back_entries,
                   pdpi::ReadPiTableEntries(p4_session.get()));
  EXPECT_EQ(read_back_entries.size(), 0);

  LOG(INFO) << "for loop";
  std::vector<p4::v1::TableEntry> pi_entries;
  for (const auto &pd_entry : {acl_entry}) {
    LOG(INFO) << "loop";
    ASSIGN_OR_RETURN(
        p4::v1::TableEntry pi_entry,
        pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, pd_entry),
        _.SetPrepend() << "Failed in PD table conversion to PI, entry: "
                       << pd_entry.DebugString() << " error: ");
    pi_entries.push_back(pi_entry);
  }

  LOG(INFO) << "InstallPiTableEntries";
  return (pdpi::InstallPiTableEntries(p4_session.get(), ir_p4info, pi_entries));
}

// Set up the switch to forward inbound packets to the egress port
//
// The rules will forward all matching packets matching src to the egress port
// specified. Set is_ipv6 to true to get the IPv6 version. Otherwise it will
// use IPv4.
//
absl::Status ForwardToEgress(uint32_t in_port, uint32_t out_port, bool is_ipv6,
		             const absl::string_view dest_mac,
	                     thinkit::Switch &sut,
                             const p4::config::v1::P4Info &p4info) {
  constexpr absl::string_view kVrfId = "vrf-80";
  constexpr absl::string_view kRifOutId = "router-interface-1";
  constexpr absl::string_view kNhopId = "nexthop-1";

  const std::string nborid =
      netaddr::MacAddress(2, 2, 2, 2, 2, 2).ToLinkLocalIpv6Address().ToString();

  auto vrf_entry = gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
      R"pb(
        vrf_table_entry {
          match { vrf_id: "$0" }
          action { no_action {} }
        })pb",
      kVrfId));

  auto rif_out_entry = gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
      R"pb(
        router_interface_table_entry {
          match { router_interface_id: "$0" }
          action {
            unicast_set_port_and_src_mac {
              port: "$1"
              src_mac: "66:55:44:33:22:11"
            }
          }
        }
      )pb",
      kRifOutId, out_port));

  auto nbor_entry = gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
      R"pb(
        neighbor_table_entry {
          match { router_interface_id: "$0" neighbor_id: "$1" }
          action { set_dst_mac { dst_mac: "02:02:02:02:02:02" } }
        }
      )pb",
      kRifOutId, nborid));

  auto nhop_entry = gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
      R"pb(
        nexthop_table_entry {
          match { nexthop_id: "$2" }
          action { set_nexthop { router_interface_id: "$0" neighbor_id: "$1" } }
        }
      )pb",
      kRifOutId, nborid, kNhopId));

  auto ipv4_entry = gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
      R"pb(
        ipv4_table_entry {
          match { vrf_id: "$0" }
          action { set_nexthop_id { nexthop_id: "$1" } }
        }
      )pb",
      kVrfId, kNhopId));

  auto ipv6_entry = gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
      R"pb(
        ipv6_table_entry {
          match { vrf_id: "$0" }
          action { set_nexthop_id { nexthop_id: "$1" } }
        }
      )pb",
      kVrfId, kNhopId));

  auto acl_entry = gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
      R"pb(
        acl_pre_ingress_table_entry {
          match {
            src_mac { value: "00:01:02:03:04:05" mask: "ff:ff:ff:ff:ff:ff" }
          }
          action { set_vrf { vrf_id: "$0" } }
          priority: 1
        }
      )pb",
      kVrfId));

  auto l3_admit_entry =
      gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
          R"pb(
            l3_admit_table_entry {
              match { dst_mac { value: "$0" mask: "FF:FF:FF:FF:FF:FF" } }
              action { admit_to_l3 {} }
              priority: 1
            }
          )pb",
          dest_mac));

  LOG(INFO) << "p4_stub";
  ASSIGN_OR_RETURN(std::unique_ptr<p4::v1::P4Runtime::StubInterface> p4_stub,
                   sut.CreateP4RuntimeStub());

  LOG(INFO) << "p4_session";
  ASSIGN_OR_RETURN(
      std::unique_ptr<pdpi::P4RuntimeSession> p4_session,
      pdpi::P4RuntimeSession::Create(std::move(p4_stub), sut.DeviceId()));

  LOG(INFO) << "CreateIrP4Info";
  ASSIGN_OR_RETURN(auto ir_p4info, pdpi::CreateIrP4Info(p4info));

  LOG(INFO) << "SetForwardingPipelineConfig";
  RETURN_IF_ERROR(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      p4_session.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT, p4info))
      << "SetForwardingPipelineConfig: Failed to push P4Info: ";

  LOG(INFO) << "ClearTableEntries";
  RETURN_IF_ERROR(pdpi::ClearTableEntries(p4_session.get()));
  // Check that switch is in a clean state.
  ASSIGN_OR_RETURN(auto read_back_entries,
                   pdpi::ReadPiTableEntries(p4_session.get()));
  EXPECT_EQ(read_back_entries.size(), 0);

  LOG(INFO) << "for loop";
  std::vector<p4::v1::TableEntry> pi_entries;
  for (const auto &pd_entry :
       {vrf_entry, rif_out_entry, nbor_entry, nhop_entry,
        is_ipv6 ? ipv6_entry : ipv4_entry, acl_entry, l3_admit_entry}) {
    LOG(INFO) << "loop";
    ASSIGN_OR_RETURN(
        p4::v1::TableEntry pi_entry,
        pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, pd_entry),
        _.SetPrepend() << "Failed in PD table conversion to PI, entry: "
                       << pd_entry.DebugString() << " error: ");
    pi_entries.push_back(pi_entry);
  }

  LOG(INFO) << "InstallPiTableEntries";
  return (pdpi::InstallPiTableEntries(p4_session.get(), ir_p4info, pi_entries));
}

// Tear down any forwarding rules set up
absl::Status ForwardTeardown(thinkit::Switch &sut) {
  ASSIGN_OR_RETURN(std::unique_ptr<p4::v1::P4Runtime::StubInterface> p4_stub,
                   sut.CreateP4RuntimeStub());

  ASSIGN_OR_RETURN(
      std::unique_ptr<pdpi::P4RuntimeSession> p4_session,
      pdpi::P4RuntimeSession::Create(std::move(p4_stub), sut.DeviceId()));

  RETURN_IF_ERROR(pdpi::ClearTableEntries(p4_session.get()));
  // Check that switch is in a clean state.
  ASSIGN_OR_RETURN(auto read_back_entries,
                   pdpi::ReadPiTableEntries(p4_session.get()));
  EXPECT_EQ(read_back_entries.size(), 0);

  return absl::OkStatus();
}

absl::StatusOr<bool> CheckLinkUp(absl::string_view iface,
                                 gnmi::gNMI::StubInterface *gnmi_stub) {
  std::string ops_state_path =
      absl::StrCat("interfaces/interface[name=", iface, "]/state/oper-status");

  ASSIGN_OR_RETURN(std::string ops_response,
                   GetGnmiStatePathInfo(gnmi_stub, ops_state_path,
                                        "openconfig-interfaces:oper-status"));

  return (ops_response == kOpsUp);
}

// Structure represents a link between SUT and Ixia.
// This is represented by Ixia interface name and the SUT's gNMI interface
// name.
struct IxiaLink {
  std::string ixia_interface;
  std::string sut_interface;
};

// Go over the connections and return vector of connections
// whose links are up.
absl::StatusOr<std::vector<IxiaLink>> GetReadyIxiaLinks(
    thinkit::GenericTestbed &generic_testbed,
    gnmi::gNMI::StubInterface &gnmi_stub) {
  std::vector<IxiaLink> links;
  
  absl::flat_hash_map<std::string, thinkit::InterfaceInfo> interface_info =
      generic_testbed.GetSutInterfaceInfo();
  // Loop through the interface_info looking for Ixia/SUT interface pairs,
  // checking if the link is up.  Add the pair to connections.
  for (const auto &[interface, info] : interface_info) {
    bool sut_link_up = false;
    if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR)) {
      ASSIGN_OR_RETURN(sut_link_up, CheckLinkUp(interface, &gnmi_stub));
      if (sut_link_up) {
        links.push_back({
            .ixia_interface = info.peer_interface_name,
            .sut_interface = interface,
        });
      }
    }
  }

  return links;
}

absl::StatusOr<std::string> CheckLoopback(
    absl::string_view iface, gnmi::gNMI::StubInterface *gnmi_stub) {
  std::string ops_state_path = absl::StrCat("interfaces/interface[name=", iface,
                                            "]/state/loopback-mode");

  ASSIGN_OR_RETURN(std::string ops_response,
                   GetGnmiStatePathInfo(gnmi_stub, ops_state_path,
                                        "openconfig-interfaces:loopback-mode"));

  if (absl::StrContains(ops_response, "FACILITY")) {
    return "FACILITY";
  } else if (absl::StrContains(ops_response, "TERMINAL")) {
    return "TERMINAL";
  }
  return "NONE";
}

absl::Status SetLoopback(std::string port_loopback, absl::string_view iface,
                         gnmi::gNMI::StubInterface *gnmi_stub) {
  std::string ops_config_path = absl::StrCat(
      "interfaces/interface[name=", iface, "]/config/loopback-mode");

  std::string ops_val = ConstructGnmiConfigSetString(
      "openconfig-interfaces:loopback-mode", port_loopback);

  RETURN_IF_ERROR(pins_test::SetGnmiConfigPath(gnmi_stub, ops_config_path,
                                               GnmiSetType::kUpdate, ops_val));

  return absl::OkStatus();
}

absl::StatusOr<std::string> CheckPortSpeed(
    absl::string_view iface, gnmi::gNMI::StubInterface *gnmi_stub) {
  std::string ops_state_path = absl::StrCat("interfaces/interface[name=", iface,
                                            "]/ethernet/state/port-speed");

  std::string ops_parse_str = "openconfig-if-ethernet:port-speed";
  return GetGnmiStatePathInfo(gnmi_stub, ops_state_path, ops_parse_str);
}

absl::Status SetPortSpeed(absl::string_view port_speed, absl::string_view iface,
                          gnmi::gNMI::StubInterface *gnmi_stub) {
  std::string ops_config_path = absl::StrCat(
      "interfaces/interface[name=", iface, "]/ethernet/config/port-speed");
  std::string ops_val =
      absl::StrCat("{\"openconfig-if-ethernet:port-speed\":", port_speed, "}");

  RETURN_IF_ERROR(pins_test::SetGnmiConfigPath(gnmi_stub, ops_config_path,
                                               GnmiSetType::kUpdate, ops_val));

  return absl::OkStatus();
}

// TODO: Refactor to use gnmi_helper for stats.

absl::StatusOr<uint64_t> GetGnmiStat(std::string stat_name,
                                     absl::string_view iface,
                                     gnmi::gNMI::StubInterface *gnmi_stub) {
  std::string ops_state_path;
  std::string ops_parse_str;

  if (absl::StartsWith(stat_name, "ipv4-")) {
    std::string name = stat_name.substr(5);
    ops_state_path = absl::StrCat(
        "interfaces/interface[name=", iface,
        "]subinterfaces/subinterface[index=0]/ipv4/state/counters/", name);
    ops_parse_str = "openconfig-if-ip:" + name;
  } else if (absl::StartsWith(stat_name, "ipv6-")) {
    std::string name = stat_name.substr(5);
    ops_state_path = absl::StrCat(
        "interfaces/interface[name=", iface,
        "]subinterfaces/subinterface[index=0]/ipv6/state/counters/", name);
    ops_parse_str = "openconfig-if-ip:" + name;
  } else {
    ops_state_path = absl::StrCat("interfaces/interface[name=", iface,
                                  "]/state/counters/", stat_name);
    ops_parse_str = "openconfig-interfaces:" + stat_name;
  }

  ASSIGN_OR_RETURN(
      std::string ops_response,
      GetGnmiStatePathInfo(gnmi_stub, ops_state_path, ops_parse_str));

  uint64_t stat;
  // skip over the initial quote '"'
  (void)absl::SimpleAtoi(ops_response.substr(1), &stat);
  return stat;
}

absl::StatusOr<Counters> ReadCounters(std::string iface,
                                      gnmi::gNMI::StubInterface *gnmi_stub) {
  Counters cnt = {};

  ASSIGN_OR_RETURN(cnt.in_pkts, GetGnmiStat("in-pkts", iface, gnmi_stub));
  ASSIGN_OR_RETURN(cnt.out_pkts, GetGnmiStat("out-pkts", iface, gnmi_stub));
  ASSIGN_OR_RETURN(cnt.in_octets, GetGnmiStat("in-octets", iface, gnmi_stub));
  ASSIGN_OR_RETURN(cnt.out_octets, GetGnmiStat("out-octets", iface, gnmi_stub));
  ASSIGN_OR_RETURN(cnt.in_unicast_pkts,
                   GetGnmiStat("in-unicast-pkts", iface, gnmi_stub));
  ASSIGN_OR_RETURN(cnt.out_unicast_pkts,
                   GetGnmiStat("out-unicast-pkts", iface, gnmi_stub));
  ASSIGN_OR_RETURN(cnt.in_multicast_pkts,
                   GetGnmiStat("in-multicast-pkts", iface, gnmi_stub));
  ASSIGN_OR_RETURN(cnt.out_multicast_pkts,
                   GetGnmiStat("out-multicast-pkts", iface, gnmi_stub));
  ASSIGN_OR_RETURN(cnt.in_broadcast_pkts,
                   GetGnmiStat("in-broadcast-pkts", iface, gnmi_stub));
  ASSIGN_OR_RETURN(cnt.out_broadcast_pkts,
                   GetGnmiStat("out-broadcast-pkts", iface, gnmi_stub));
  ASSIGN_OR_RETURN(cnt.in_errors, GetGnmiStat("in-errors", iface, gnmi_stub));
  ASSIGN_OR_RETURN(cnt.out_errors, GetGnmiStat("out-errors", iface, gnmi_stub));
  ASSIGN_OR_RETURN(cnt.in_discards,
                   GetGnmiStat("in-discards", iface, gnmi_stub));
  ASSIGN_OR_RETURN(cnt.out_discards,
                   GetGnmiStat("out-discards", iface, gnmi_stub));
  ASSIGN_OR_RETURN(cnt.in_fcs_errors,
                   GetGnmiStat("in-fcs-errors", iface, gnmi_stub));
  ASSIGN_OR_RETURN(cnt.in_ipv4_pkts,
                   GetGnmiStat("ipv4-in-pkts", iface, gnmi_stub));
  ASSIGN_OR_RETURN(cnt.out_ipv4_pkts,
                   GetGnmiStat("ipv4-out-pkts", iface, gnmi_stub));
  ASSIGN_OR_RETURN(cnt.in_ipv6_pkts,
                   GetGnmiStat("ipv6-in-pkts", iface, gnmi_stub));
  ASSIGN_OR_RETURN(cnt.out_ipv6_pkts,
                   GetGnmiStat("ipv6-out-pkts", iface, gnmi_stub));
  ASSIGN_OR_RETURN(cnt.in_ipv6_discarded_pkts,
                   GetGnmiStat("ipv6-in-discarded-pkts", iface, gnmi_stub));
  ASSIGN_OR_RETURN(cnt.out_ipv6_discarded_pkts,
                   GetGnmiStat("ipv6-out-discarded-pkts", iface, gnmi_stub));

  return cnt;
}

void ShowCounters(const Counters &cnt) {
  LOG(INFO) << "in-pkts " << cnt.in_pkts;
  LOG(INFO) << "out-pkts " << cnt.out_pkts;
  LOG(INFO) << "in-octets " << cnt.in_octets;
  LOG(INFO) << "out-octets " << cnt.out_octets;
  LOG(INFO) << "in-unicast-pkts " << cnt.in_unicast_pkts;
  LOG(INFO) << "out-unicast-pkts " << cnt.out_unicast_pkts;
  LOG(INFO) << "in-multicast-pkts " << cnt.in_multicast_pkts;
  LOG(INFO) << "out-multicast-pkts " << cnt.out_multicast_pkts;
  LOG(INFO) << "in-broadcast-pkts " << cnt.in_broadcast_pkts;
  LOG(INFO) << "out-broadcast-pkts " << cnt.out_broadcast_pkts;
  LOG(INFO) << "in-errors " << cnt.in_errors;
  LOG(INFO) << "out-errors " << cnt.out_errors;
  LOG(INFO) << "in-discards " << cnt.in_discards;
  LOG(INFO) << "out-discards " << cnt.out_discards;
  LOG(INFO) << "in-fcs-errors " << cnt.in_fcs_errors;
  LOG(INFO) << "in-ipv4-pkts " << cnt.in_ipv4_pkts;
  LOG(INFO) << "out-ipv4-pkts " << cnt.out_ipv4_pkts;
  LOG(INFO) << "in-ipv6-pkts " << cnt.in_ipv6_pkts;
  LOG(INFO) << "out-ipv6-pkts " << cnt.out_ipv6_pkts;
  LOG(INFO) << "in-ipv6-discarded-pkts " << cnt.in_ipv6_discarded_pkts;
  LOG(INFO) << "out-ipv6-discarded-pkts " << cnt.out_ipv6_discarded_pkts;
}

// DeltaCounters - computer delta as change from initial to final counters
Counters DeltaCounters(const Counters &initial, const Counters &final) {
  Counters delta = {};

  delta.in_pkts = final.in_pkts - initial.in_pkts;
  delta.out_pkts = final.out_pkts - initial.out_pkts;
  delta.in_octets = final.in_octets - initial.in_octets;
  delta.out_octets = final.out_octets - initial.out_octets;
  delta.in_unicast_pkts = final.in_unicast_pkts - initial.in_unicast_pkts;
  delta.out_unicast_pkts = final.out_unicast_pkts - initial.out_unicast_pkts;
  delta.in_multicast_pkts = final.in_multicast_pkts - initial.in_multicast_pkts;
  delta.out_multicast_pkts =
      final.out_multicast_pkts - initial.out_multicast_pkts;
  delta.in_broadcast_pkts = final.in_broadcast_pkts - initial.in_broadcast_pkts;
  delta.out_broadcast_pkts =
      final.out_broadcast_pkts - initial.out_broadcast_pkts;
  delta.in_errors = final.in_errors - initial.in_errors;
  delta.out_errors = final.out_errors - initial.out_errors;
  delta.in_discards = final.in_discards - initial.in_discards;
  delta.out_discards = final.out_discards - initial.out_discards;
  delta.in_fcs_errors = final.in_fcs_errors - initial.in_fcs_errors;
  delta.in_ipv4_pkts = final.in_ipv4_pkts - initial.in_ipv4_pkts;
  delta.out_ipv4_pkts = final.out_ipv4_pkts - initial.out_ipv4_pkts;
  delta.in_ipv6_pkts = final.in_ipv6_pkts - initial.in_ipv6_pkts;
  delta.out_ipv6_pkts = final.out_ipv6_pkts - initial.out_ipv6_pkts;
  delta.in_ipv6_discarded_pkts =
      final.in_ipv6_discarded_pkts - initial.in_ipv6_discarded_pkts;
  delta.out_ipv6_discarded_pkts =
      final.out_ipv6_discarded_pkts - initial.out_ipv6_discarded_pkts;

  return delta;
}

TEST_P(CountersTestFixture, TestInFcsErrors) {
  LOG(INFO) << "\n\n\n\n\n\n\n\n\n\n---------- Starting TestInFcsErrors "
               "----------\n\n\n\n\n";

  // Pick a testbed with an Ixia Traffic Generator. A SUT is assumed.
  thinkit::TestRequirements requirements =
      gutil::ParseProtoOrDie<thinkit::TestRequirements>(
          R"pb(interface_requirements {
                 count: 1
                 interface_mode: TRAFFIC_GENERATOR
               })pb");

  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<thinkit::GenericTestbed> generic_testbed,
      GetParam().testbed_interface->GetTestbedWithRequirements(requirements));

  absl::flat_hash_map<std::string, thinkit::InterfaceInfo> interface_info =
      generic_testbed->GetSutInterfaceInfo();

  // Hook up to GNMI
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<gnmi::gNMI::StubInterface> gnmi_stub,
                       generic_testbed->Sut().CreateGnmiStub());

  // Loop through the interface_info looking for Ixia/SUT interface pairs,
  // checking if the link is up. We need one pair with link up for the
  // ingress interface/IXIA traffic generation.
  ASSERT_OK_AND_ASSIGN(std::vector<IxiaLink> ready_links,
                       GetReadyIxiaLinks(*generic_testbed, *gnmi_stub));

  ASSERT_GE(ready_links.size(), 1) << "Ixia link is not ready";

  std::string ixia_interface = ready_links[0].ixia_interface;
  std::string sut_interface = ready_links[0].sut_interface;
  
  LOG(INFO) << "\n\nChose Ixia interface " << ixia_interface
            << " and SUT interface " << sut_interface << "\n\n";

  std::vector<absl::string_view> v = absl::StrSplit(ixia_interface, '/');
  absl::string_view ixia_ip = v[0];
  absl::string_view ixia_card = v[1];
  absl::string_view ixia_port = v[2];
  ASSERT_FALSE(ixia_ip.empty());
  ASSERT_FALSE(ixia_card.empty());
  ASSERT_FALSE(ixia_port.empty());
  LOG(INFO) << "Ixia IP is " << ixia_ip;
  LOG(INFO) << "Ixia card is " << ixia_card;
  LOG(INFO) << "Ixia port is " << ixia_port;
  LOG(INFO) << "SUT is " << generic_testbed->Sut().ChassisName();

  // Read some initial counters via GNMI from the SUT
  ASSERT_OK_AND_ASSIGN(auto initial_counters,
                       ReadCounters(sut_interface, gnmi_stub.get()));

  LOG(INFO) << "\n\nInitial Counters (" << sut_interface << "):\n";
  ShowCounters(initial_counters);
  LOG(INFO) << "\n\n";

  // Connect to the Ixia
  ASSERT_OK_AND_ASSIGN(std::string href,
                       ixia::IxiaConnect(ixia_ip, *generic_testbed));
  LOG(INFO) << "href " << href;

  std::size_t ixpos = href.find("/ixnetwork");
  ASSERT_NE(ixpos, std::string::npos);
  std::string ixref = href.substr(0, ixpos + 10);
  LOG(INFO) << "ixref " << ixref;

  // Connect to the Ixia card/port
  ASSERT_OK_AND_ASSIGN(
      std::string vref,
      ixia::IxiaVport(href, ixia_card, ixia_port, *generic_testbed));

  // Start a session
  ASSERT_OK_AND_ASSIGN(std::string tref,
                       ixia::IxiaSession(vref, *generic_testbed));
  LOG(INFO) << "gwc tref = " << tref;

  // Set the frame rate to 100 fps
  ASSERT_OK(ixia::SetFrameRate(tref, 100, *generic_testbed));

  // Set the frame count to 950
  ASSERT_OK(ixia::SetFrameCount(tref, 950, *generic_testbed));

  // Set the destination MAC address to LLDP multicast
  ASSERT_OK(ixia::SetDestMac(tref, "01:80:c2:00:00:0e", *generic_testbed));

  // Set the source MAC address
  ASSERT_OK(ixia::SetSrcMac(tref, "00:01:02:03:04:05", *generic_testbed));

  // PATCH to /ixnetwork/traffic/trafficItem/1/configElement/1
  // with {"crc":"badCrc"}
  std::string badcrc_path = tref + "/configElement/1";
  std::string badcrc_json = "{\"crc\":\"badCrc\"}";
  LOG(INFO) << "path " << badcrc_path;
  LOG(INFO) << "json " << badcrc_json;
  ASSERT_OK_AND_ASSIGN(
      thinkit::HttpResponse badcrc_response,
      generic_testbed->SendRestRequestToIxia(thinkit::RequestType::kPatch,
                                             badcrc_path, badcrc_json));
  EXPECT_EQ(badcrc_response.response_code, 200) << badcrc_response.response;
  LOG(INFO) << "gwc: Returns " << badcrc_response.response_code;

  ASSERT_OK(ixia::StartTraffic(tref, ixref, *generic_testbed));

  // Wait until 10 (traffic) + 25 (stats update) seconds after
  // the traffic started.
  absl::SleepFor(absl::Seconds(35));

  // Re-read the same counters via GNMI from the SUT
  ASSERT_OK_AND_ASSIGN(auto final_counters,
                       ReadCounters(sut_interface, gnmi_stub.get()));

  // Display the final counters
  ShowCounters(final_counters);

  // Compute the change for each counter
  auto delta = DeltaCounters(initial_counters, final_counters);

  // Display the difference in the counters for now (during test dev)
  LOG(INFO) << "\n\nDeltas:";
  ShowCounters(delta);

  // Check the changes are as expected.
  // Note that i'm seeing an occasional multicast packet (probably LLDP)
  // going out so I'm allowing some minimal change in the output counters
  // during the test to account for this.
  EXPECT_EQ(delta.in_pkts, 0);
  EXPECT_LE(delta.out_pkts, 10);
  EXPECT_LE(delta.out_octets, 1000);
  EXPECT_EQ(delta.in_unicast_pkts, 0);
  EXPECT_EQ(delta.out_unicast_pkts, 0);
  EXPECT_EQ(delta.in_multicast_pkts, 0);
  EXPECT_LE(delta.out_multicast_pkts, 10);
  EXPECT_EQ(delta.in_broadcast_pkts, 0);
  EXPECT_EQ(delta.out_broadcast_pkts, 0);
  EXPECT_EQ(delta.out_errors, 0);
  EXPECT_EQ(delta.in_discards, 0);
  EXPECT_EQ(delta.out_discards, 0);
  EXPECT_EQ(delta.in_fcs_errors, 950);
  EXPECT_EQ(delta.in_errors, delta.in_fcs_errors);
  EXPECT_EQ(delta.in_octets, delta.in_fcs_errors * 64);
  EXPECT_EQ(delta.in_ipv4_pkts, 0);
  EXPECT_EQ(delta.out_ipv4_pkts, 0);
  EXPECT_EQ(delta.in_ipv6_pkts, 0);
  EXPECT_EQ(delta.out_ipv6_pkts, 0);
  EXPECT_EQ(delta.in_ipv6_discarded_pkts, 0);
  EXPECT_EQ(delta.out_ipv6_discarded_pkts, 0);

  LOG(INFO) << "\n\n\n\n\n---------- Finished TestInFcsErrors "
               "----------\n\n\n\n\n\n\n\n\n\n";
}

TEST_P(CountersTestFixture, TestIPv4Pkts) {
  LOG(INFO) << "\n\n\n\n\n\n\n\n\n\n---------- Starting TestIPv4Pkts "
               "----------\n\n\n\n\n";
  // TODO: Remove after PINs release includes loopback-mode changes
  GTEST_SKIP() << "loopback-mode tests temporarily skipped until "
                  "next PINs release";

  // Pick a testbed with an Ixia Traffic Generator. A SUT is assumed.
  thinkit::TestRequirements requirements =
      gutil::ParseProtoOrDie<thinkit::TestRequirements>(
          R"pb(interface_requirements {
                 count: 1
                 interface_mode: TRAFFIC_GENERATOR
               })pb");

  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<thinkit::GenericTestbed> generic_testbed,
      GetParam().testbed_interface->GetTestbedWithRequirements(requirements));

  absl::flat_hash_map<std::string, thinkit::InterfaceInfo> interface_info =
      generic_testbed->GetSutInterfaceInfo();

  // Hook up to GNMI
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<gnmi::gNMI::StubInterface> gnmi_stub,
                       generic_testbed->Sut().CreateGnmiStub());

  // Loop through the interface_info looking for Ixia/SUT interface pairs,
  // checking if the link is up.  we need one pair with link up for the
  // ingress interface/IXIA traffic generation
  ASSERT_OK_AND_ASSIGN(std::vector<IxiaLink> ready_links,
                       GetReadyIxiaLinks(*generic_testbed, *gnmi_stub));

  ASSERT_GE(ready_links.size(), 1) << "Ixia link is not ready";

  std::string ixia_interface = ready_links[0].ixia_interface;
  std::string sut_in_interface = ready_links[0].sut_interface;

  ASSERT_FALSE(ixia_interface.empty());
  ASSERT_FALSE(sut_in_interface.empty());

  // Now loop through again and pick an egress interface. This one doesn't
  // have to be up, just a different interface.
  std::string sut_out_interface = "";

  for (const auto &[interface, info] : interface_info) {
    if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR)) {
      if (interface != sut_in_interface) {
        sut_out_interface = interface;
        break;
      }
    }
  }

  absl::flat_hash_map<std::string, std::string> port_id_by_interface;
  ASSERT_OK_AND_ASSIGN(port_id_by_interface,
                       GetAllInterfaceNameToPortId(*gnmi_stub));

  ASSERT_OK_AND_ASSIGN(
      const std::string in_id,
      gutil::FindOrStatus(port_id_by_interface, sut_in_interface));
  ASSERT_OK_AND_ASSIGN(
      const std::string out_id,
      gutil::FindOrStatus(port_id_by_interface, sut_out_interface));

  LOG(INFO) << "\n\nTestIPv4Pkts:\n"
            << "Chose Ixia interface " << ixia_interface << "\n"
            << "and SUT ingress interface " << sut_in_interface << " (id "
            << in_id << ")\n"
            << "and SUT egress interface " << sut_out_interface << " (id "
            << out_id << ")\n\n";

  std::vector<absl::string_view> v = absl::StrSplit(ixia_interface, '/');
  absl::string_view ixia_ip = v[0];
  absl::string_view ixia_in_card = v[1];
  absl::string_view ixia_in_port = v[2];
  ASSERT_FALSE(ixia_ip.empty());
  ASSERT_FALSE(ixia_in_card.empty());
  ASSERT_FALSE(ixia_in_port.empty());
  LOG(INFO) << "Ixia IP is " << ixia_ip;
  LOG(INFO) << "Ixia ingress card is " << ixia_in_card;
  LOG(INFO) << "Ixia ingress port is " << ixia_in_port;
  LOG(INFO) << "SUT is " << generic_testbed->Sut().ChassisName();

  // Fetch the initial conditions for the egress interface.
  // Note: Not currently fetching the FEC mode since the gNMI get on that
  // fails even if I populate redis first.  See b/197778604.  As a result
  // the link will not come up at the end of the test after I switch it
  // back to 100GB.  TBD.
  ASSERT_OK_AND_ASSIGN(auto out_initial_loopback,
                       CheckLoopback(sut_out_interface, gnmi_stub.get()));
  ASSERT_OK_AND_ASSIGN(auto out_initial_speed,
                       CheckPortSpeed(sut_out_interface, gnmi_stub.get()));

  // Output the initial conditions
  LOG(INFO) << "sut out_initial_speed is " << out_initial_speed;
  LOG(INFO) << "sut out_initial_loopback is " << out_initial_loopback;
  LOG(INFO) << "\n\n";

  // Set the egress port to loopback mode
  EXPECT_OK(SetLoopback("ASIC_MAC_LOCAL", sut_out_interface, gnmi_stub.get()));

  // Restore loopback configuration after test.
  const auto kRestoreLoopbackConfig = absl::Cleanup([&] {
    EXPECT_OK(
        SetLoopback(out_initial_loopback, sut_out_interface, gnmi_stub.get()))
        << "failed to restore initial loopback config.";
  });

  // Set up the switch to forward inbound IPv4 packets to the egress port
  LOG(INFO) << "\n\n----- TestIPv4Pkts: ForwardToEgress -----\n";
  constexpr absl::string_view kDestMac = "02:02:02:02:02:02";
  EXPECT_OK(ForwardToEgress(std::stoul(in_id), std::stoul(out_id), false,
                            kDestMac, generic_testbed->Sut(),
                            GetParam().p4_info));

  LOG(INFO) << "\n\n----- ForwardToEgress Done -----\n";

  // Read some initial counters via GNMI from the SUT
  ASSERT_OK_AND_ASSIGN(auto initial_in_counters,
                       ReadCounters(sut_in_interface, gnmi_stub.get()));
  ASSERT_OK_AND_ASSIGN(auto initial_out_counters,
                       ReadCounters(sut_out_interface, gnmi_stub.get()));

  LOG(INFO) << "\n\nTestIPv4Pkts:\n\n"
            << "\n\nInitial Ingress Counters (" << sut_in_interface << "):\n";
  ShowCounters(initial_in_counters);
  LOG(INFO) << "\n\nInitial Egress Counters (" << sut_out_interface << "):\n";
  ShowCounters(initial_out_counters);
  LOG(INFO) << "\n\n";

  // Connect to the Ixia
  LOG(INFO) << "\n\nTestIPv4Pkts: IxiaConnect\n\n";
  
  ASSERT_OK_AND_ASSIGN(std::string href,
                       ixia::IxiaConnect(ixia_ip, *generic_testbed));

  std::size_t ixpos = href.find("/ixnetwork");
  ASSERT_NE(ixpos, std::string::npos);
  std::string ixref = href.substr(0, ixpos + 10);
  LOG(INFO) << "ixref " << ixref;

  // Connect to the Ixia card/port
  ASSERT_OK_AND_ASSIGN(
      std::string vref,
      ixia::IxiaVport(href, ixia_in_card, ixia_in_port, *generic_testbed));

  // Start a session
  ASSERT_OK_AND_ASSIGN(std::string full_tref,
                       ixia::IxiaSession(vref, *generic_testbed));

  LOG(INFO) << "full_tref = " << full_tref;
  ixpos = full_tref.find("/ixnetwork");
  ASSERT_NE(ixpos, std::string::npos);
  std::string tref = full_tref.substr(ixpos);
  LOG(INFO) << "tref " << tref;

  // Set the line rate to 100 percent
  ASSERT_OK(ixia::SetLineRate(tref, 100, *generic_testbed));

  // Set the frame count to 90M
  ASSERT_OK(ixia::SetFrameCount(tref, 90000000, *generic_testbed));

  // Set the destination MAC address
   ASSERT_OK(ixia::SetDestMac(tref, kDestMac, *generic_testbed));

  // Set the source MAC address
  ASSERT_OK(ixia::SetSrcMac(tref, "00:01:02:03:04:05", *generic_testbed));

  // Append an IPv4 header
  ASSERT_OK(ixia::AppendIPv4(full_tref, *generic_testbed));

  // Set up the source and destination IP addresses
  ASSERT_OK(ixia::SetSrcIPv4(tref, "192.168.0.1", *generic_testbed));
  ASSERT_OK(ixia::SetDestIPv4(tref, "192.168.0.2", *generic_testbed));

  // Set the frame size to 1514 bytes
  ASSERT_OK(ixia::SetFrameSize(tref, kMtu, *generic_testbed));

  // LOG(INFO) << "\n\n*** 2 minutes till START ***\n\n";
  // absl::SleepFor(absl::Seconds(120));
  ASSERT_OK(ixia::StartTraffic(full_tref, ixref, *generic_testbed));

  // Wait until 10 (traffic) + 25 (stats update) seconds after
  // the traffic started.
  absl::Time t1;
  t1 = absl::Now();

  absl::SleepFor(absl::Seconds(35));

  // Re-read the same counters via GNMI from the SUT
  ASSERT_OK_AND_ASSIGN(auto final_in_counters,
                       ReadCounters(sut_in_interface, gnmi_stub.get()));
  ASSERT_OK_AND_ASSIGN(auto final_out_counters,
                       ReadCounters(sut_out_interface, gnmi_stub.get()));

  // Check the time again
  absl::Time t2 = absl::Now();
  LOG(INFO) << "Time after statistics read is " << t2;
  LOG(INFO) << "Delta is " << t2 - t1;
  uint64_t seconds = absl::ToInt64Seconds(t2 - t1);
  
  // Display the final counters
  LOG(INFO) << "\n\nTestIPv4Pkts:\n\n"
            << "\n\nFinal Ingress Counters (" << sut_in_interface << "):\n";
  ShowCounters(final_in_counters);
  LOG(INFO) << "\n\nFinal Egress Counters (" << sut_out_interface << "):\n";
  ShowCounters(final_out_counters);
  LOG(INFO) << "\n\n";

  // Compute the change for each counter
  auto delta_in = DeltaCounters(initial_in_counters, final_in_counters);
  auto delta_out = DeltaCounters(initial_out_counters, final_out_counters);

  // Display the difference in the counters for now (during test dev)
  LOG(INFO) << "\n\nTestIPv4Pkts:\n\n"
            << "\n\nIngress Deltas (" << sut_in_interface << ") in " << seconds
            << " seconds:";
  ShowCounters(delta_in);
  LOG(INFO) << "\n\nEgress Deltas (" << sut_out_interface << ") in " << seconds
            << " seconds:";
  ShowCounters(delta_out);

  // Check the changes are as expected.  Test should run about 10sec, maybe
  // a little more (time to stop). Ixia is sending 100GB line rate unicast
  // IPv4 traffic. ACL/Route is forwarding all of it to the egress but it
  // is running at 40GB so only about 40% can fit.
  // note that i'm seeing an occasional multicast packet (probably LLDP)
  // going out so I'm allowing some minimal change in some counters
  // during the test to account for this.
  EXPECT_GE(delta_out.out_pkts, 90000000);
  EXPECT_LE(delta_out.out_pkts, delta_out.out_pkts + 10);
  EXPECT_GE(delta_out.out_octets, delta_out.out_pkts * kMtu - 15000);
  EXPECT_LE(delta_out.out_octets, delta_out.out_pkts * kMtu + 15000);
  EXPECT_LE(delta_out.out_unicast_pkts, delta_out.out_pkts + 10);
  EXPECT_LE(delta_out.out_multicast_pkts, 10);
  EXPECT_EQ(delta_out.out_broadcast_pkts, 0);
  EXPECT_EQ(delta_out.out_errors, 0);
  EXPECT_EQ(delta_out.out_discards, 0);
  
  EXPECT_GE(delta_out.out_ipv4_pkts, delta_out.out_pkts - 10);
  EXPECT_LE(delta_out.out_ipv4_pkts, delta_out.out_pkts + 10);
  
  EXPECT_EQ(delta_out.out_ipv6_pkts, 0);
  EXPECT_EQ(delta_out.out_ipv6_discarded_pkts, 0);

  // Tear down any forwarding rules set up
  EXPECT_OK(ForwardTeardown(generic_testbed->Sut()));

  LOG(INFO) << "\n\n\n\n\n---------- Finished TestIPv4Pkts "
               "----------\n\n\n\n\n\n\n\n\n\n";
}

TEST_P(CountersTestFixture, TestIPv6Pkts) {
  LOG(INFO) << "\n\n\n\n\n\n\n\n\n\n---------- Starting TestIPv6Pkts "
               "----------\n\n\n\n\n";
  // TODO: Remove after PINs release includes loopback-mode changes
  GTEST_SKIP() << "loopback-mode tests temporarily skipped until "
                  "next PINs release";

  // Pick a testbed with an Ixia Traffic Generator. A SUT is assumed.
  thinkit::TestRequirements requirements =
      gutil::ParseProtoOrDie<thinkit::TestRequirements>(
          R"pb(interface_requirements {
                 count: 1
                 interface_mode: TRAFFIC_GENERATOR
               })pb");

  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<thinkit::GenericTestbed> generic_testbed,
      GetParam().testbed_interface->GetTestbedWithRequirements(requirements));

  absl::flat_hash_map<std::string, thinkit::InterfaceInfo> interface_info =
      generic_testbed->GetSutInterfaceInfo();

  // Hook up to GNMI
  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, generic_testbed->Sut().CreateGnmiStub());

  // Loop through the interface_info looking for Ixia/SUT interface pairs,
  // checking if the link is up.  we need one pair with link up for the
  // ingress interface/IXIA traffic generation
  ASSERT_OK_AND_ASSIGN(std::vector<IxiaLink> ready_links,
                       GetReadyIxiaLinks(*generic_testbed, *gnmi_stub));

  ASSERT_GE(ready_links.size(), 1) << "Ixia link is not ready";
  
  std::string ixia_interface = ready_links[0].ixia_interface;
  std::string sut_in_interface = ready_links[0].sut_interface;
  
  ASSERT_FALSE(ixia_interface.empty());
  ASSERT_FALSE(sut_in_interface.empty());
  
  // Now loop through again and pick an egress interface.  This one doesn't
  // have to be up, just a different interface.
  std::string sut_out_interface = "";

  for (const auto &[interface, info] : interface_info) {
    if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR)) {
      if (interface != sut_in_interface) {
        sut_out_interface = interface;
        break;
      }
    }
  }

  // Look up the port number for the egress interface
  absl::flat_hash_map<std::string, std::string> port_id_by_interface;
  ASSERT_OK_AND_ASSIGN(port_id_by_interface,
                       GetAllInterfaceNameToPortId(*gnmi_stub));

  ASSERT_OK_AND_ASSIGN(
      const std::string in_id,
      gutil::FindOrStatus(port_id_by_interface, sut_in_interface));

  ASSERT_OK_AND_ASSIGN(
      const std::string out_id,
      gutil::FindOrStatus(port_id_by_interface, sut_out_interface));

  LOG(INFO) << "\n\nTestIPv6Pkts:\n\n"
            << "\n\nChose Ixia interface " << ixia_interface << "\n"
            << "and SUT ingress interface " << sut_in_interface << " (id "
            << in_id << ")\n"
            << "and SUT egress interface " << sut_out_interface << " (id "
            << out_id << ")\n\n";

  std::vector<absl::string_view> v = absl::StrSplit(ixia_interface, '/');
  absl::string_view ixia_ip = v[0];
  absl::string_view ixia_in_card = v[1];
  absl::string_view ixia_in_port = v[2];
  ASSERT_FALSE(ixia_ip.empty());
  ASSERT_FALSE(ixia_in_card.empty());
  ASSERT_FALSE(ixia_in_port.empty());
  LOG(INFO) << "Ixia IP is " << ixia_ip;
  LOG(INFO) << "Ixia ingress card is " << ixia_in_card;
  LOG(INFO) << "Ixia ingress port is " << ixia_in_port;
  LOG(INFO) << "SUT is " << generic_testbed->Sut().ChassisName();

  // Fetch the initial conditions for the egress interface.
  // Note: Not currently fetching the FEC mode since the gNMI get on that
  // fails even if I populate redis first. As a result
  // the link will not come up at the end of the test after I switch it
  // back to 100GB.  TBD.
  ASSERT_OK_AND_ASSIGN(auto out_initial_loopback,
                       CheckLoopback(sut_out_interface, gnmi_stub.get()));
  ASSERT_OK_AND_ASSIGN(auto out_initial_speed,
                       CheckPortSpeed(sut_out_interface, gnmi_stub.get()));

  // Output the initial conditions
  LOG(INFO) << "sut out_initial_speed is " << out_initial_speed;
  LOG(INFO) << "sut out_initial_loopback is " << out_initial_loopback;
  LOG(INFO) << "\n\n";

  // Set the egress port to loopback mode
  EXPECT_OK(SetLoopback("ASIC_MAC_LOCAL", sut_out_interface, gnmi_stub.get()));

  // Restore loopback configuration after test.
  const auto kRestoreLoopbackConfig = absl::Cleanup([&] {
    EXPECT_OK(
        SetLoopback(out_initial_loopback, sut_out_interface, gnmi_stub.get()))
        << "failed to restore initial loopback config.";
  });

  // Set up the switch to forward inbound packets to the egress port
  constexpr absl::string_view kDestMac = "02:02:02:02:02:02";
  EXPECT_OK(ForwardToEgress(std::stoul(in_id), std::stoul(out_id), true,
                            kDestMac, generic_testbed->Sut(),
                            GetParam().p4_info));

  // Read some initial counters via GNMI from the SUT
  ASSERT_OK_AND_ASSIGN(auto initial_in_counters,
                       ReadCounters(sut_in_interface, gnmi_stub.get()));
  ASSERT_OK_AND_ASSIGN(auto initial_out_counters,
                       ReadCounters(sut_out_interface, gnmi_stub.get()));

  LOG(INFO) << "\n\nInitial Ingress Counters (" << sut_in_interface << "):\n";
  ShowCounters(initial_in_counters);
  
  LOG(INFO) << "\n\nInitial Egress Counters (" << sut_out_interface << "):\n";
  ShowCounters(initial_out_counters);
  LOG(INFO) << "\n\n";

  // Connect to the Ixia
  ASSERT_OK_AND_ASSIGN(std::string href,
                       ixia::IxiaConnect(ixia_ip, *generic_testbed));

  std::size_t ixpos = href.find("/ixnetwork");
  ASSERT_NE(ixpos, std::string::npos);
  std::string ixref = href.substr(0, ixpos + 10);
  LOG(INFO) << "ixref " << ixref;

  // Connect to the Ixia card/port
  ASSERT_OK_AND_ASSIGN(
      std::string vref,
      ixia::IxiaVport(href, ixia_in_card, ixia_in_port, *generic_testbed));

  // Start a session
  ASSERT_OK_AND_ASSIGN(std::string full_tref,
                       ixia::IxiaSession(vref, *generic_testbed));

  LOG(INFO) << "full_tref = " << full_tref;
  ixpos = full_tref.find("/ixnetwork");
  ASSERT_NE(ixpos, std::string::npos);
  std::string tref = full_tref.substr(ixpos);
  LOG(INFO) << "tref " << tref;

  // Set the line rate to 100 percent
  ASSERT_OK(ixia::SetLineRate(tref, 100, *generic_testbed));

  // Set the frame count to 90M
  ASSERT_OK(ixia::SetFrameCount(tref, 90000000, *generic_testbed));

  // Set the source and destination MAC addresses
  ASSERT_OK(ixia::SetSrcMac(tref, "00:01:02:03:04:05", *generic_testbed));
  ASSERT_OK(ixia::SetDestMac(tref, kDestMac, *generic_testbed));

  // Add an IPv6 header
  ASSERT_OK(ixia::AppendIPv6(tref, *generic_testbed));

  // Set the source and destination IPv6 addresses
  ASSERT_OK(
      ixia::SetSrcIPv6(tref, "fe80::201:02ff:fe03:0405", *generic_testbed));
  ASSERT_OK(
      ixia::SetDestIPv6(tref, "fe80::002:02ff:fe02:0202", *generic_testbed));

  // Set the frame size to 1514 bytes
  ASSERT_OK(ixia::SetFrameSize(tref, kMtu, *generic_testbed));

  // LOG(INFO) << "\n\n\n\n\nAbout to sleep";
  // absl::SleepFor(absl::Seconds(15));
  ASSERT_OK(ixia::StartTraffic(full_tref, ixref, *generic_testbed));

  // Wait until 10 (traffic) + 25 (stats update) seconds after
  // the traffic started.
  absl::Time t1;
  t1 = absl::Now();
  absl::SleepFor(absl::Seconds(35));

  // Re-read the same counters via GNMI from the SUT
  ASSERT_OK_AND_ASSIGN(auto final_in_counters,
                       ReadCounters(sut_in_interface, gnmi_stub.get()));
  ASSERT_OK_AND_ASSIGN(auto final_out_counters,
                       ReadCounters(sut_out_interface, gnmi_stub.get()));

  // Check the time again
  absl::Time t2 = absl::Now();
  LOG(INFO) << "Time after statistics read is " << t2;
  LOG(INFO) << "Delta is " << t2 - t1;
  uint64_t seconds = absl::ToInt64Seconds(t2 - t1);

  // Display the final counters
  LOG(INFO) << "\n\nTestIPv6Pkts:\n\n"
            << "\n\nFinal Ingress Counters (" << sut_in_interface << "):\n";
  ShowCounters(final_in_counters);
  LOG(INFO) << "\n\nFinal Egress Counters (" << sut_out_interface << "):\n";
  ShowCounters(final_out_counters);
  LOG(INFO) << "\n\n";

  // Compute the change for each counter
  auto delta_in = DeltaCounters(initial_in_counters, final_in_counters);
  auto delta_out = DeltaCounters(initial_out_counters, final_out_counters);

  // Display the difference in the counters for now (during test dev)
  LOG(INFO) << "\n\nTestIPv6Pkts:\n\n"
            << "\n\nIngress Deltas (" << sut_in_interface << ") in " << seconds
            << " seconds:";
  ShowCounters(delta_in);
  LOG(INFO) << "\n\nEgress Deltas (" << sut_out_interface << ") in " << seconds
            << " seconds:";
  ShowCounters(delta_out);

  // Check the changes are as expected.  Test should run about 10sec, maybe
  // a little more (time to stop). Ixia is sending 100GB line rate unicast
  // IPv6 traffic, stopping at 90,000,000 packets at 1514 bytes. ACL/Route
  // is forwarding all of it to the egress.
  // note that i'm seeing an occasional multicast packet (probably LLDP)
  // going out so I'm allowing some minimal change in some counters
  // during the test to account for this.
  EXPECT_GE(delta_out.out_pkts, 90000000);
  EXPECT_LE(delta_out.out_pkts, 90000000 + 10);
  EXPECT_LE(delta_out.out_octets, delta_out.out_pkts * kMtu + 15000);
  EXPECT_GE(delta_out.out_octets, delta_out.out_pkts * kMtu - 15000);
  EXPECT_LE(delta_out.out_unicast_pkts, delta_out.out_pkts + 10);
  EXPECT_GE(delta_out.out_unicast_pkts, delta_out.out_pkts - 10);
  EXPECT_LE(delta_out.out_multicast_pkts, 10);
  EXPECT_EQ(delta_out.out_broadcast_pkts, 0);
  EXPECT_EQ(delta_out.out_errors, 0);
  EXPECT_EQ(delta_out.out_discards, 0);
  EXPECT_EQ(delta_out.out_ipv4_pkts, 0);
  EXPECT_GE(delta_out.in_ipv6_pkts, delta_out.out_pkts - 10);
  EXPECT_LE(delta_out.in_ipv6_pkts, delta_out.out_pkts + 10);

  EXPECT_LE(delta_out.out_ipv6_pkts, delta_out.out_pkts + 10);
  EXPECT_GE(delta_out.out_ipv6_pkts, delta_out.out_pkts - 10);
  EXPECT_LE(delta_in.in_ipv6_pkts, delta_out.out_pkts + 10);
  EXPECT_GE(delta_in.in_ipv6_pkts, delta_out.out_pkts - 10);

  EXPECT_EQ(delta_out.out_ipv6_discarded_pkts, 0);
  
  // Tear down any forwarding rules set up
  EXPECT_OK(ForwardTeardown(generic_testbed->Sut()));

  LOG(INFO) << "\n\n\n\n\n---------- Finished TestIPv6Pkts "
               "----------\n\n\n\n\n\n\n\n\n\n";
}

// Set up the switch to punt packets to CPU.
absl::Status SetUpPuntToCPU(const netaddr::MacAddress &dmac,
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
            dst_ip { value: "$1" mask: "255.255.255.255" }
          }
          action { acl_trap { qos_queue: "$2" } }
          dst_ip { value: "$2" mask: "255.255.255.255" }
          priority: 1
        }
      )pb",
      dmac.ToString(), dst_ip.ToString(), p4_queue));
  std::vector<p4::v1::TableEntry> pi_entries;
  ASSIGN_OR_RETURN(
      pi_entries.emplace_back(), pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, acl_entry),
      _.SetPrepend() << "Failed in PD table conversion to PI, entry: "
                     << acl_entry.DebugString() << " error: ");

  LOG(INFO) << "InstallPiTableEntries";
  return pdpi::InstallPiTableEntries(&p4_session, ir_p4info, pi_entries);
}

// Ixia configurations:
// 1. Frames sent per second by Ixia.
// 2. Total frames sent by Ixia.
// 3. Default framesize.
// 4. Maximum framesize.
// 5. Minimum framesize.
constexpr int kFramesPerSecond = 1000000;
constexpr int kTotalFrames = 10000000;
constexpr int kDefaultFrameSize = 1514;

TEST_P(CountersTestFixture, TestCPUOutDiscards) {
  LOG(INFO) << "\n\n\n\n\n\n\n\n\n\n---------- Starting TestCPUOutDiscards "
               "----------\n\n\n\n\n";

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

  thinkit::Switch &sut = generic_testbed->Sut();

  // Configure SUT.
  EXPECT_OK(generic_testbed->Environment().StoreTestArtifact(
      "p4info.textproto", GetParam().p4_info));
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<pdpi::P4RuntimeSession> sut_p4_session,
                       pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
                           sut, absl::nullopt, GetParam().p4_info));
  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, sut.CreateGnmiStub());

  ASSERT_OK_AND_ASSIGN(std::string sut_gnmi_config,
                       pins_test::GetGnmiConfig(*gnmi_stub));
  EXPECT_OK(generic_testbed->Environment().StoreTestArtifact("gnmi_config.json",
                                                             sut_gnmi_config));

  // Flow details.
  const auto dest_mac = netaddr::MacAddress(02, 02, 02, 02, 02, 02);
  const auto source_mac = netaddr::MacAddress(00, 01, 02, 03, 04, 05);
  const auto source_ip = netaddr::Ipv4Address(192, 168, 10, 1);
  const auto dest_ip = netaddr::Ipv4Address(172, 0, 0, 1);

  ASSERT_OK_AND_ASSIGN(std::vector<IxiaLink> ready_links,
                       GetReadyIxiaLinks(*generic_testbed, *gnmi_stub));

  ASSERT_FALSE(ready_links.empty()) << "Ixia links are not ready";

  std::string ixia_interface = ready_links[0].ixia_interface;
  std::string sut_interface = ready_links[0].sut_interface;
  
  // Set up Ixia traffic.
  // Send Ixia traffic.
  // Stop Ixia traffic.
  
  ASSERT_OK_AND_ASSIGN(ixia::IxiaPortInfo ixia_port,
                       ixia::ExtractPortInfo(ixia_interface));

  ASSERT_OK_AND_ASSIGN(
      std::string topology_ref,
      pins_test::ixia::IxiaConnect(ixia_port.hostname, *generic_testbed));

  ASSERT_OK_AND_ASSIGN(
      std::string vport_ref,
      pins_test::ixia::IxiaVport(topology_ref, ixia_port.card, ixia_port.port,
                                 *generic_testbed));
  
  ASSERT_OK_AND_ASSIGN(
      std::string traffic_ref,
      pins_test::ixia::IxiaSession(vport_ref, *generic_testbed));

  ASSERT_OK(pins_test::ixia::SetFrameRate(traffic_ref, kFramesPerSecond,
                                          *generic_testbed));

  ASSERT_OK(pins_test::ixia::SetFrameCount(traffic_ref, kTotalFrames,
                                           *generic_testbed));

  ASSERT_OK(pins_test::ixia::SetFrameSize(traffic_ref, kDefaultFrameSize,
                                          *generic_testbed));
  
  ASSERT_OK(pins_test::ixia::SetSrcMac(traffic_ref, source_mac.ToString(),
                                       *generic_testbed));
  
  ASSERT_OK(pins_test::ixia::SetDestMac(traffic_ref, dest_mac.ToString(),
                                        *generic_testbed));
  
  ASSERT_OK(pins_test::ixia::AppendIPv4(traffic_ref, *generic_testbed));
  
  ASSERT_OK(pins_test::ixia::SetSrcIPv4(traffic_ref, source_ip.ToString(),
                                        *generic_testbed));
  
  ASSERT_OK(pins_test::ixia::SetDestIPv4(traffic_ref, dest_ip.ToString(),
                                         *generic_testbed));
  
  LOG(INFO) << "\n\n\nTesting CPU Out discards : "
            << "\n===================\n\n\n";
  
  ASSERT_OK(pins_test::ixia::SetFrameSize(traffic_ref, kDefaultFrameSize,
                                          *generic_testbed));

  ASSERT_OK(SetUpPuntToCPU(dest_mac, dest_ip, GetParam().cpu_queue_to_use,
                           GetParam().p4_info, *sut_p4_session));

  ASSERT_OK_AND_ASSIGN(auto initial_cpu_out_discards,
		       GetGnmiStat("out-discards", "CPU", gnmi_stub.get()));
  ASSERT_OK(pins_test::ixia::StartTraffic(traffic_ref, topology_ref,
                                          *generic_testbed));

  absl::SleepFor(absl::Seconds(5));

  ASSERT_OK(ixia::StopTraffic(traffic_ref, *generic_testbed));

  ASSERT_OK_AND_ASSIGN(auto final_cpu_out_discards,
                       GetGnmiStat("out-discards", "CPU", gnmi_stub.get()));
  auto delta_cpu_out_discards =
      final_cpu_out_discards - initial_cpu_out_discards;
  EXPECT_GT(delta_cpu_out_discards, 0);
}

// Set up the switch to forward inbound packets to the egress port using
// default route in VRF. The rules will forward all matching packets matching
// source MAC address to the egress port specified.
//
// Also set up a Copy rule to CPU to punt egress packets to test for
// any inspection.
//
absl::Status SetUpForwarding(absl::string_view out_port,
                             absl::string_view source_mac,
                             absl::string_view dest_mac,
                             const p4::config::v1::P4Info &p4info,
                             pdpi::P4RuntimeSession &p4_session) {
  constexpr absl::string_view kVrfId = "vrf-80";
  constexpr absl::string_view kRifOutId = "router-interface";
  constexpr absl::string_view kNextHopId = "nexthop-1";
  constexpr absl::string_view kNeighborIdv6 = "fe80::002:02ff:fe02:0202";
  const absl::string_view kNeighborId = kNeighborIdv6;

  std::vector<sai::TableEntry> pd_entries;
  ASSIGN_OR_RETURN(pd_entries.emplace_back(),
                   gutil::ParseTextProto<sai::TableEntry>(absl::Substitute(
                       R"pb(
                         vrf_table_entry {
                           match { vrf_id: "$0" }
                           action { no_action {} }
                         })pb",
                       kVrfId)));
  
  ASSIGN_OR_RETURN(pd_entries.emplace_back(),
                   gutil::ParseTextProto<sai::TableEntry>(absl::Substitute(
                       R"pb(
                         router_interface_table_entry {
                           match { router_interface_id: "$0" }
                           action {
                             unicast_set_port_and_src_mac {
                               port: "$1"
                               src_mac: "66:55:44:33:22:11"
                             }
                           }
                         }
                       )pb",
                       kRifOutId, out_port)));

  ASSIGN_OR_RETURN(
      pd_entries.emplace_back(),
      gutil::ParseTextProto<sai::TableEntry>(absl::Substitute(
          R"pb(
            neighbor_table_entry {
              match { router_interface_id: "$0" neighbor_id: "$1" }
              action { set_dst_mac { dst_mac: "02:02:02:02:02:02" } }
            }
          )pb",
          kRifOutId, kNeighborId)));

  ASSIGN_OR_RETURN(
      pd_entries.emplace_back(),
      gutil::ParseTextProto<sai::TableEntry>(absl::Substitute(
          R"pb(
            nexthop_table_entry {
              match { nexthop_id: "$2" }
              action {
                set_ip_nexthop { router_interface_id: "$0" neighbor_id: "$1" }
              }
            }
          )pb",
          kRifOutId, kNeighborId, kNextHopId)));

  ASSIGN_OR_RETURN(pd_entries.emplace_back(),
                   gutil::ParseTextProto<sai::TableEntry>(absl::Substitute(
                       R"pb(
                         ipv4_table_entry {
                           match { vrf_id: "$0" }
                           action { set_nexthop_id { nexthop_id: "$1" } }
                         }
                       )pb",
                       kVrfId, kNextHopId)));

   ASSIGN_OR_RETURN(pd_entries.emplace_back(),
                   gutil::ParseTextProto<sai::TableEntry>(absl::Substitute(
                       R"pb(
                         ipv6_table_entry {
                           match { vrf_id: "$0" }
                           action { set_nexthop_id { nexthop_id: "$1" } }
                         }
                       )pb",
                       kVrfId, kNextHopId)));

   ASSIGN_OR_RETURN(
      pd_entries.emplace_back(),
      gutil::ParseTextProto<sai::TableEntry>(absl::Substitute(
          R"pb(
            acl_pre_ingress_table_entry {
              match { src_mac { value: "$0" mask: "ff:ff:ff:ff:ff:ff" } }
              action { set_vrf { vrf_id: "$1" } }
              priority: 1
            }
          )pb",
          source_mac, kVrfId)));

   ASSIGN_OR_RETURN(
      pd_entries.emplace_back(),
      gutil::ParseTextProto<sai::TableEntry>(absl::Substitute(
          R"pb(
            l3_admit_table_entry {
              match { dst_mac { value: "$0" mask: "FF:FF:FF:FF:FF:FF" } }
              action { admit_to_l3 {} }
              priority: 1
            }
          )pb",
          dest_mac)));

   // Clear table entries
  RETURN_IF_ERROR(pdpi::ClearTableEntries(&p4_session));

  ASSIGN_OR_RETURN(auto ir_p4info, pdpi::CreateIrP4Info(p4info));
  std::vector<p4::v1::TableEntry> pi_entries;
  for (const auto &pd_entry : pd_entries) {
    ASSIGN_OR_RETURN(p4::v1::TableEntry pi_entry,
                     pdpi::PartialPdTableEntryToPiTableEntry(ir_p4info, pd_entry),
                     _.SetPrepend()
                         << "Failed in PD table conversion to PI, entry: "
                         << pd_entry.DebugString() << " error: ");
    pi_entries.push_back(pi_entry);
  }

  return (pdpi::InstallPiTableEntries(&p4_session, ir_p4info, pi_entries));
}

struct DiscardTestIxiaSetUpResult {
  // Ixia reference URLs to topology.
  std::string topology_ref;
  // Ixia reference URLs to traffic.
  std::vector<std::string> traffic_refs;
};

absl::StatusOr<DiscardTestIxiaSetUpResult> SetUpIxiaForDiscardTest(
    const std::string kIxiaTxPort1, const std::string kIxiaTxPort2,
    const std::string kIxiaRxPort, thinkit::GenericTestbed &testbed) {
  // Extract Ixia chassis, card and port information from the Ixia interface
  // info.
  ASSIGN_OR_RETURN(ixia::IxiaPortInfo ixia_port1,
                   ixia::ExtractPortInfo(kIxiaTxPort1));

  ASSIGN_OR_RETURN(ixia::IxiaPortInfo ixia_port2,
                   ixia::ExtractPortInfo(kIxiaTxPort2));

  ASSIGN_OR_RETURN(ixia::IxiaPortInfo ixia_port3,
                   ixia::ExtractPortInfo(kIxiaRxPort));
  
  // Connect to Ixia.
  ASSIGN_OR_RETURN(std::string topology_ref,
                   pins_test::ixia::IxiaConnect(ixia_port1.hostname, testbed));
  
  // Get Ixia reference to Ixia ports.
  ASSIGN_OR_RETURN(std::string vport1_ref,
                   pins_test::ixia::IxiaVport(topology_ref, ixia_port1.card,
                                              ixia_port1.port, testbed));
  
  ASSIGN_OR_RETURN(std::string vport2_ref,
                   pins_test::ixia::IxiaVport(topology_ref, ixia_port2.card,
                                              ixia_port2.port, testbed));
  
  ASSIGN_OR_RETURN(std::string vport3_ref,
                   pins_test::ixia::IxiaVport(topology_ref, ixia_port3.card,
                                              ixia_port3.port, testbed));

  std::vector<std::string> traffic_refs;
  // Set up traffic items with source and destination ports.
  ASSIGN_OR_RETURN(
      traffic_refs.emplace_back(),
      pins_test::ixia::SetUpTrafficItem(vport1_ref, vport3_ref, testbed));

   ASSIGN_OR_RETURN(
      traffic_refs.emplace_back(),
      pins_test::ixia::SetUpTrafficItem(vport2_ref, vport3_ref, testbed));
  
   return DiscardTestIxiaSetUpResult{
      .topology_ref = topology_ref,
      .traffic_refs = traffic_refs,
  };
}

TEST_P(CountersTestFixture, TestFrontPanelOutDiscards) {
  LOG(INFO)
      << "\n\n\n\n\n\n\n\n\n\n---------- Starting TestFrontPanelOutDiscards "
         "----------\n\n\n\n\n";
  // Pick a testbed with an Ixia Traffic Generator.
  auto requirements =
      gutil::ParseProtoOrDie<thinkit::TestRequirements>(
          R"pb(interface_requirements {
                 count: 3
                 interface_mode: TRAFFIC_GENERATOR
               })pb");
  
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<thinkit::GenericTestbed> testbed,
      GetParam().testbed_interface->GetTestbedWithRequirements(requirements));

  // Set up P4Runtime session.
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<pdpi::P4RuntimeSession> sut_p4_session,
      pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
          testbed->Sut(), /*gnmi_config=*/absl::nullopt, GetParam().p4_info));

  // Hook up to GNMI.
  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, testbed->Sut().CreateGnmiStub());

  // Get Ixia connected links.
  const absl::flat_hash_map<std::string, thinkit::InterfaceInfo>
      interface_info = testbed->GetSutInterfaceInfo();
  ASSERT_OK_AND_ASSIGN(std::vector<ixia::IxiaLink> ready_links,
                       ixia::GetReadyIxiaLinks(*testbed, *gnmi_stub));
  ASSERT_GE(ready_links.size(), 3)
      << "Test requires at least 3 SUT ports connected to an Ixia";

  const std::string kIxiaTxPort1 = ready_links[0].ixia_interface;
  const std::string kSutInPort1 = ready_links[0].sut_interface;

  const std::string kIxiaTxPort2 = ready_links[1].ixia_interface;
  const std::string kSutInPort2 = ready_links[1].sut_interface;

  const std::string kIxiaRxPort = ready_links[2].ixia_interface;
  const std::string kSutOutPort = ready_links[2].sut_interface;

  // Look up the port IDs used by P4RT for the SUT interfaces
  absl::flat_hash_map<std::string, std::string> port_id_by_interface;
  ASSERT_OK_AND_ASSIGN(port_id_by_interface,
                       GetAllInterfaceNameToPortId(*gnmi_stub));
  
  ASSERT_OK_AND_ASSIGN(const std::string kSutInPort1Id,
                       gutil::FindOrStatus(port_id_by_interface, kSutInPort1)); 

  ASSERT_OK_AND_ASSIGN(const std::string kSutInPort2Id,
                       gutil::FindOrStatus(port_id_by_interface, kSutInPort2));

  ASSERT_OK_AND_ASSIGN(std::string kSutOutPortId,
                       gutil::FindOrStatus(port_id_by_interface, kSutOutPort));

  // We will perform the following base steps with Ixia:
  // Set up 2 Ixia traffic items.
  // Set up source mac and destination mac address.
  // Set initial frame rates for the 2 items.

  // Flow details.
  const auto kSourceMac =
      netaddr::MacAddress(0x00, 0x01, 0x02, 0x03, 0x04, 0x05);
  const auto kDestMac = netaddr::MacAddress(0x02, 0x02, 0x02, 0x02, 0x02, 0x01);
  const auto kSourceIpv4 = netaddr::Ipv4Address(192, 168, 0, 1);
  const auto kDestIpv4 = netaddr::Ipv4Address(172, 0, 0, 1);
  const auto kSourceIpv6 =
      netaddr::Ipv6Address(0x1000, 0, 0, 0, 0, 0, 0, 0x1);  // 1000::1
  const auto kDestIpv6 =
      netaddr::Ipv6Address(0x2000, 0, 0, 0, 0, 0, 0, 0x1);  // 2000::1

  ASSERT_OK_AND_ASSIGN(DiscardTestIxiaSetUpResult ixia_setup_result,
                       SetUpIxiaForDiscardTest(kIxiaTxPort1, kIxiaTxPort2,
                                               kIxiaRxPort, *testbed));

  ASSERT_EQ(ixia_setup_result.traffic_refs.size(), 2)
      << "Test requires 2 traffic streams";

  // Set up flow for Traffic 1. 

  // Get port speed in bits per second.
  ASSERT_OK_AND_ASSIGN(int64_t in_port1_speed_bps,
                       GetPortSpeedInBitsPerSecond(kSutInPort1, *gnmi_stub));

  constexpr int kDefaultFrameSizeinBytes = 1514;

  double frame_rate_at_line_speed_of_in_port1 =
      in_port1_speed_bps / (kDefaultFrameSizeinBytes * 8);

  absl::string_view traffic_ref1 = ixia_setup_result.traffic_refs[0];
  absl::string_view traffic_ref2 = ixia_setup_result.traffic_refs[1];

  ASSERT_OK(pins_test::ixia::SetFrameSize(traffic_ref1,
                                          kDefaultFrameSizeinBytes, *testbed));
  
  ASSERT_OK(pins_test::ixia::SetSrcMac(traffic_ref1, kSourceMac.ToString(),
                                       *testbed));
  ASSERT_OK(
      pins_test::ixia::SetDestMac(traffic_ref1, kDestMac.ToString(), *testbed));
  
  ASSERT_OK(pins_test::ixia::AppendIPv4(traffic_ref1, *testbed));
  
  ASSERT_OK(pins_test::ixia::SetSrcIPv4(traffic_ref1, kSourceIpv4.ToString(),
                                        *testbed));
  
  ASSERT_OK(pins_test::ixia::SetDestIPv4(traffic_ref1, kDestIpv4.ToString(),
                                         *testbed));
  
  ASSERT_OK(pins_test::ixia::SetFrameRate(
      traffic_ref1, frame_rate_at_line_speed_of_in_port1 + 1, *testbed));
  
  // Set up flow for Traffic 2.
  // Get port speed in bits per second.
  ASSERT_OK_AND_ASSIGN(auto in_port2_speed,
                       GetPortSpeedInBitsPerSecond(kSutInPort2, *gnmi_stub));
  
  uint64_t frame_rate_at_line_speed_of_in_port2 =
      in_port2_speed / (kDefaultFrameSizeinBytes * 8);
  ASSERT_OK(pins_test::ixia::SetFrameRate(
      traffic_ref2, frame_rate_at_line_speed_of_in_port2, *testbed));
  ASSERT_OK(pins_test::ixia::SetFrameSize(traffic_ref2,
                                          kDefaultFrameSizeinBytes, *testbed));
  
  ASSERT_OK(pins_test::ixia::SetSrcMac(traffic_ref2, kSourceMac.ToString(),
                                       *testbed));

  ASSERT_OK(
      pins_test::ixia::SetDestMac(traffic_ref2, kDestMac.ToString(), *testbed));

  ASSERT_OK(pins_test::ixia::AppendIPv6(traffic_ref2, *testbed));
  ASSERT_OK(pins_test::ixia::SetSrcIPv6(traffic_ref2, kSourceIpv6.ToString(),
                                        *testbed));
  ASSERT_OK(pins_test::ixia::SetDestIPv6(traffic_ref2, kDestIpv6.ToString(),
                                         *testbed));

  ASSERT_OK(pins_test::ixia::SetFrameRate(
      traffic_ref2, frame_rate_at_line_speed_of_in_port2 + 1, *testbed));

  // Set up the switch to forward inbound packets to the egress port
  ASSERT_OK(SetUpForwarding(kSutOutPortId, kSourceMac.ToString(),
                            kDestMac.ToString(), GetParam().p4_info,
                            *sut_p4_session));

  ASSERT_OK_AND_ASSIGN(
      auto initial_port_out_discards,
      GetGnmiStat("out-discards", kSutOutPort, gnmi_stub.get()));

  ASSERT_OK(pins::TryUpToNTimes(3, /*delay=*/absl::Seconds(1), [&] {
    return pins_test::ixia::StartTraffic(ixia_setup_result.traffic_refs,
                                         ixia_setup_result.topology_ref,
                                         *testbed);
  }));

  absl::SleepFor(absl::Seconds(5));

  ASSERT_OK(
      pins_test::ixia::StopTraffic(ixia_setup_result.traffic_refs, *testbed));

  ASSERT_OK_AND_ASSIGN(
      auto final_port_out_discards,
      GetGnmiStat("out-discards", kSutOutPort, gnmi_stub.get()));

  auto delta_port_out_discards =
      final_port_out_discards - initial_port_out_discards;
  EXPECT_GT(delta_port_out_discards, 0);
}

}  // namespace pins_test
