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
//
#include "tests/gnmi/ethcounter_ixia_test.h"

#include <string>

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/strings/escaping.h"
#include "absl/strings/match.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
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
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_pdpi/pd.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "thinkit/generic_testbed.h"
#include "thinkit/proto/generic_testbed.pb.h"
#include "thinkit/switch.h"

namespace pins_test {

using ::nlohmann::json;

namespace {
constexpr char kOpsDown[] = "\"DOWN\"";  // NOLINT
constexpr char kOpsUp[] = "\"UP\"";

constexpr char kSpeed100GB[] = "\"openconfig-if-ethernet:SPEED_100GB\"";

constexpr char kLoopbackFalse[] = "false";  // NOLINT
constexpr char kLoopbackTrue[] = "true";

constexpr uint32_t kMtu = 1514;
}  // namespace

// TrapToCPU - Set up the switch to punt ingress packets to the CPU
//
// The rules will punt all matching packets to the CPU.
//
absl::Status TrapToCPU(thinkit::Switch &sut) {
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

  LOG(INFO) << "GetP4Info";
  p4::config::v1::P4Info p4info =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  LOG(INFO) << "CreateIrP4Info";
  ASSIGN_OR_RETURN(auto ir_p4info, pdpi::CreateIrP4Info(p4info));

  LOG(INFO) << "SetForwardingPipelineConfig";
  RETURN_IF_ERROR(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      p4_session.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      sai::GetP4Info(sai::Instantiation::kMiddleblock)))
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
// Note: after seeing occasional problems with forwarding not working
// and following b/190736007 and chats with @kishanps I have added
// a RIF to the ingress port as well as one for the egress port jic.
//
absl::Status ForwardToEgress(uint32_t in_port, uint32_t out_port, bool is_ipv6,
                             thinkit::Switch &sut) {
  constexpr absl::string_view kVrfId = "vrf-80";
  constexpr absl::string_view kRifOutId = "router-interface-1";
  constexpr absl::string_view kRifInId = "router-interface-2";
  constexpr absl::string_view kNhopId = "nexthop-1";
  constexpr absl::string_view kNborIdv4 = "1.1.1.2";
  constexpr absl::string_view kNborIdv6 = "fe80::002:02ff:fe02:0202";
  absl::string_view nborid = kNborIdv4;

  if (is_ipv6) nborid = kNborIdv6;

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
            set_port_and_src_mac { port: "$1" src_mac: "66:55:44:33:22:11" }
          }
        }
      )pb",
      kRifOutId, out_port));

  auto rif_in_entry = gutil::ParseProtoOrDie<sai::TableEntry>(absl::Substitute(
      R"pb(
        router_interface_table_entry {
          match { router_interface_id: "$0" }
          action {
            set_port_and_src_mac { port: "$1" src_mac: "88:55:44:33:22:11" }
          }
        }
      )pb",
      kRifInId, in_port));

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

  LOG(INFO) << "p4_stub";
  ASSIGN_OR_RETURN(std::unique_ptr<p4::v1::P4Runtime::StubInterface> p4_stub,
                   sut.CreateP4RuntimeStub());

  LOG(INFO) << "p4_session";
  ASSIGN_OR_RETURN(
      std::unique_ptr<pdpi::P4RuntimeSession> p4_session,
      pdpi::P4RuntimeSession::Create(std::move(p4_stub), sut.DeviceId()));

  LOG(INFO) << "GetP4Info";
  p4::config::v1::P4Info p4info =
      sai::GetP4Info(sai::Instantiation::kMiddleblock);

  LOG(INFO) << "CreateIrP4Info";
  ASSIGN_OR_RETURN(auto ir_p4info, pdpi::CreateIrP4Info(p4info));

  LOG(INFO) << "SetForwardingPipelineConfig";
  RETURN_IF_ERROR(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      p4_session.get(),
      p4::v1::SetForwardingPipelineConfigRequest::RECONCILE_AND_COMMIT,
      sai::GetP4Info(sai::Instantiation::kMiddleblock)))
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
       {vrf_entry, rif_out_entry, rif_in_entry, nbor_entry, nhop_entry,
        is_ipv6 ? ipv6_entry : ipv4_entry, acl_entry}) {
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

absl::StatusOr<bool> CheckLoopback(absl::string_view iface,
                                   gnmi::gNMI::StubInterface *gnmi_stub) {
  std::string ops_state_path = absl::StrCat("interfaces/interface[name=", iface,
                                            "]/state/loopback-mode");

  ASSIGN_OR_RETURN(std::string ops_response,
                   GetGnmiStatePathInfo(gnmi_stub, ops_state_path,
                                        "openconfig-interfaces:loopback-mode"));

  return (ops_response == kLoopbackTrue);
}

absl::Status SetLoopback(bool port_loopback, absl::string_view iface,
                         gnmi::gNMI::StubInterface *gnmi_stub) {
  std::string ops_config_path = absl::StrCat(
      "interfaces/interface[name=", iface, "]/config/loopback-mode");

  // Originally I wrote:
  // ops_val =
  // ConstructGnmiConfigSetString("openconfig-interfaces:loopback-mode",
  // port_loopback); but that gets converted to 0 or 1 and that gets rejected as
  // a "float". so the API needs an upgrade for bool.

  std::string ops_val;
  if (port_loopback) {
    ops_val = "{\"openconfig-interfaces:loopback-mode\":true}";
  } else {
    ops_val = "{\"openconfig-interfaces:loopback-mode\":false}";
  }

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

// NameToP4Id - Map an interface name to the P4 ID for it
//
// Fetch the state for the interface then parse out the P4 ID.  The format is:
// \"openconfig-p4rt:id\":8,
// which in this case would be for ID 8.
//
// FYI, the formula for computing the port ID used by P4 is:
// orion_port_id = channel_index * 512 + port_index + 1
//
absl::StatusOr<uint32_t> NameToP4Id(std::string iface,
                                    gnmi::gNMI::StubInterface *gnmi_stub) {
  // fetch all the information for the interface from gNMI
  std::string state_path =
      absl::StrCat("interfaces/interface[name=", iface, "]/state");
  ASSIGN_OR_RETURN(gnmi::GetRequest request,
                   BuildGnmiGetRequest(state_path, gnmi::GetRequest::STATE));
  gnmi::GetResponse response;
  grpc::ClientContext context;
  auto status = gnmi_stub->Get(&context, request, &response);
  if (!status.ok()) return absl::InternalError("bad status");
  std::string resp_str = response.DebugString();
  std::size_t idix = resp_str.find("openconfig-p4rt:id");
  if (idix == std::string::npos) return absl::InvalidArgumentError("no id");
  std::string id_str = resp_str.substr(idix + 21, 3);
  return std::stoul(id_str);
}

#if 0
TEST_P(ExampleIxiaTestFixture, TestInFcsErrors) {
  LOG(INFO) << "\n\n\n\n\n\n\n\n\n\n---------- Starting TestInFcsErrors "
               "----------\n\n\n\n\n";

  // Pick a testbed with an Ixia Traffic Generator. A SUT is assumed.
  thinkit::TestRequirements requirements =
      gutil::ParseProtoOrDie<thinkit::TestRequirements>(
          R"pb(interface_requirements {
                 count: 1
                 interface_mode: TRAFFIC_GENERATOR
               })pb");

  ASSERT_OK_AND_ASSIGN(std::unique_ptr<thinkit::GenericTestbed> generic_testbed,
                       GetTestbedWithRequirements(requirements));

  absl::flat_hash_map<std::string, thinkit::InterfaceInfo> interface_info =
      generic_testbed->GetSutInterfaceInfo();

  // Connect to TestTracker for test status
  generic_testbed->Environment().SetTestCaseID(
      "3da5c6f0-c85e-465f-9221-1e07523092d6");

  // Hook up to GNMI
  ASSERT_OK_AND_ASSIGN(
      std::unique_ptr<gnmi::gNMI::StubInterface> gnmi_stub,
      generic_testbed->Sut().CreateGnmiStub());

  // go through all the ports that interface to the Ixia and set them
  // to 100GB since the Ixia ports are all 100GB.
  for (const auto &[interface, info] : interface_info) {
    if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR)) {
      LOG(INFO) << "gwc: Host Interface " << interface;
      EXPECT_OK(SetPortSpeed(kSpeed100GB, interface, gnmi_stub.get()));
    }
  }

  // Wait to let the links come up
  absl::SleepFor(absl::Seconds(20));

  // Loop through the interface_info looking for Ixia/SUT interface pairs,
  // checking if the link is up. we need one pair with link up for the
  // ingress interface/IXIA bad fcs traffic generation
  std::string ixia_interface = "";
  std::string sut_interface = "";

  for (const auto &[interface, info] : interface_info) {
    if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR)) {
      auto sut_link_up = CheckLinkUp(interface, gnmi_stub.get());
      EXPECT_TRUE(sut_link_up.ok());
      if (sut_link_up.ok() && sut_link_up.value()) {
        ixia_interface = info.peer_interface_name;
        sut_interface = interface;
        break;
      }
    }
  }

  ASSERT_FALSE(ixia_interface.empty());
  ASSERT_FALSE(sut_interface.empty());
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

  // Wait until 10 seconds after the traffic started
  absl::Time t1;
  t1 = absl::Now();

  absl::Time t2;
  while (1) {
    t2 = absl::Now();
    if (t2 >= t1 + absl::Seconds(10)) break;
    absl::SleepFor(absl::Milliseconds(100));
  }

  ASSERT_OK(ixia::StopTraffic(tref, *generic_testbed));

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
#endif

#if 1
TEST_P(ExampleIxiaTestFixture, TestIPv4Pkts) {
  LOG(INFO) << "\n\n\n\n\n\n\n\n\n\n---------- Starting TestIPv4Pkts "
               "----------\n\n\n\n\n";

  // Pick a testbed with an Ixia Traffic Generator. A SUT is assumed.
  thinkit::TestRequirements requirements =
      gutil::ParseProtoOrDie<thinkit::TestRequirements>(
          R"pb(interface_requirements {
                 count: 1
                 interface_mode: TRAFFIC_GENERATOR
               })pb");

  ASSERT_OK_AND_ASSIGN(std::unique_ptr<thinkit::GenericTestbed> generic_testbed,
                       GetTestbedWithRequirements(requirements));

  absl::flat_hash_map<std::string, thinkit::InterfaceInfo> interface_info =
      generic_testbed->GetSutInterfaceInfo();

  // Connect to TestTracker for test status
  generic_testbed->Environment().SetTestCaseID(
      "2fac23ff-6794-4a31-8fce-a1aa76afe72e");

  // Hook up to GNMI
  ASSERT_OK_AND_ASSIGN(std::unique_ptr<gnmi::gNMI::StubInterface> gnmi_stub,
                       generic_testbed->Sut().CreateGnmiStub());

  // go through all the ports that interface to the Ixia and set them
  // to 100GB since the Ixia ports are all 100GB.
  for (const auto &[interface, info] : interface_info) {
    if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR)) {
      LOG(INFO) << "Host Interface " << interface;
      EXPECT_OK(SetPortSpeed(kSpeed100GB, interface, gnmi_stub.get()));
    }
  }

  // Wait to let the links come up
  absl::SleepFor(absl::Seconds(20));

  // Loop through the interface_info looking for Ixia/SUT interface pairs,
  // checking if the link is up.  we need one pair with link up for the
  // ingress interface/IXIA traffic generation
  std::string ixia_interface = "";
  std::string sut_in_interface = "";

  for (const auto &[interface, info] : interface_info) {
    if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR)) {
      auto sut_link_up = CheckLinkUp(interface, gnmi_stub.get());
      EXPECT_TRUE(sut_link_up.ok());
      if (sut_link_up.ok() && sut_link_up.value()) {
        ixia_interface = info.peer_interface_name;
        sut_in_interface = interface;
        break;
      }
    }
  }

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

  ASSERT_FALSE(ixia_interface.empty());
  ASSERT_FALSE(sut_in_interface.empty());
  ASSERT_FALSE(sut_out_interface.empty());

  // Look up the port numbers for the ingress and egress interfaces
  ASSERT_OK_AND_ASSIGN(uint32_t in_id,
                       NameToP4Id(sut_in_interface, gnmi_stub.get()));
  ASSERT_OK_AND_ASSIGN(uint32_t out_id,
                       NameToP4Id(sut_out_interface, gnmi_stub.get()));

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
  EXPECT_OK(SetLoopback(true, sut_out_interface, gnmi_stub.get()));

  // Set up the switch to forward inbound IPv4 packets to the egress port
  LOG(INFO) << "\n\n----- TestIPv4Pkts: ForwardToEgress -----\n";
  EXPECT_OK(ForwardToEgress(in_id, out_id, false, generic_testbed->Sut()));
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
  ASSERT_OK(ixia::SetDestMac(tref, "02:02:02:02:02:02", *generic_testbed));

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

  // Wait until 10 seconds after the traffic started
  absl::Time t1;
  t1 = absl::Now();

  absl::Time t2;
  while (1) {
    t2 = absl::Now();
    if (t2 >= t1 + absl::Seconds(10)) break;
    absl::SleepFor(absl::Milliseconds(100));
  }

  LOG(INFO) << "Time at stop is " << t2;
  LOG(INFO) << "Delta is " << t2 - t1;

  ASSERT_OK(ixia::StopTraffic(full_tref, *generic_testbed));

  // Re-read the same counters via GNMI from the SUT
  ASSERT_OK_AND_ASSIGN(auto final_in_counters,
                       ReadCounters(sut_in_interface, gnmi_stub.get()));
  ASSERT_OK_AND_ASSIGN(auto final_out_counters,
                       ReadCounters(sut_out_interface, gnmi_stub.get()));

  // Check the time again
  absl::Time t3 = absl::Now();
  LOG(INFO) << "Time after statistics read is " << t3;
  LOG(INFO) << "Delta is " << t3 - t1;
  uint64_t seconds = ((t3 - t1) / absl::Seconds(1)) + 1;

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
  EXPECT_GE(delta_out.out_octets, delta_out.out_pkts * kMtu - 10000);
  EXPECT_LE(delta_out.out_octets, delta_out.out_pkts * kMtu + 10000);
  EXPECT_LE(delta_out.out_unicast_pkts, delta_out.out_pkts + 10);
  EXPECT_LE(delta_out.out_multicast_pkts, 5);
  EXPECT_EQ(delta_out.out_broadcast_pkts, 0);
  EXPECT_EQ(delta_out.out_errors, 0);
  EXPECT_EQ(delta_out.out_discards, 0);
  EXPECT_GE(delta_out.out_ipv4_pkts, delta_out.out_pkts - 10);
  EXPECT_LE(delta_out.out_ipv4_pkts, delta_out.out_pkts + 10);
  EXPECT_EQ(delta_out.out_ipv6_pkts, 0);
  EXPECT_EQ(delta_out.out_ipv6_discarded_pkts, 0);
  EXPECT_LE(delta_in.in_ipv4_pkts, delta_out.out_pkts + 10);
  EXPECT_LE(delta_in.in_ipv4_pkts, delta_out.out_pkts - 10);

  LOG(INFO) << "\n\n\n\n\n---------- Restore ----------\n\n\n\n\n";

  // go through all the ports that interface to the Ixia and set them
  // back to 100GB whether their link is up or not.
  for (const auto &[interface, info] : interface_info) {
    if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR)) {
      LOG(INFO) << "Host Interface " << interface;
      EXPECT_OK(SetPortSpeed(kSpeed100GB, interface, gnmi_stub.get()));
      EXPECT_OK(SetLoopback(false, interface, gnmi_stub.get()));
    }
  }

  // Tear down any forwarding rules set up
  EXPECT_OK(ForwardTeardown(generic_testbed->Sut()));

  LOG(INFO) << "\n\n\n\n\n---------- Finished TestIPv4Pkts "
               "----------\n\n\n\n\n\n\n\n\n\n";
}
#endif

#if 0
TEST_P(ExampleIxiaTestFixture, TestOutDiscards) {
  LOG(INFO) << "\n\n\n\n\n\n\n\n\n\n---------- Starting TestOutDiscards "
               "----------\n\n\n\n\n";

  // Pick a testbed with an Ixia Traffic Generator. A SUT is assumed.
  thinkit::TestRequirements requirements =
      gutil::ParseProtoOrDie<thinkit::TestRequirements>(
          R"pb(interface_requirements {
                 count: 1
                 interface_mode: TRAFFIC_GENERATOR
               })pb");

  ASSERT_OK_AND_ASSIGN(std::unique_ptr<thinkit::GenericTestbed> generic_testbed,
                       GetTestbedWithRequirements(requirements));

  absl::flat_hash_map<std::string, thinkit::InterfaceInfo> interface_info =
      generic_testbed->GetSutInterfaceInfo();

  // Connect to TestTracker for test status
  generic_testbed->Environment().SetTestCaseID(
      "0539b74c-656f-4a0c-aa8f-39d7721520ad");

  // Hook up to GNMI
  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, generic_testbed->Sut().CreateGnmiStub());

  // go through all the ports that interface to the Ixia and set them
  // to 100GB since the Ixia ports are all 100GB.
  for (const auto &[interface, info] : interface_info) {
    if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR)) {
      LOG(INFO) << "Host Interface " << interface;
      EXPECT_OK(SetPortSpeed(kSpeed100GB, interface, gnmi_stub.get()));
    }
  }

  // Wait to let the links come up
  absl::SleepFor(absl::Seconds(20));

  // Loop through the interface_info looking for Ixia/SUT interface pairs,
  // checking if the link is up.  we need one pair with link up for the
  // ingress interface/IXIA traffic generation
  std::string ixia_interface = "";
  std::string sut_in_interface = "";

  for (const auto &[interface, info] : interface_info) {
    if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR)) {
      auto sut_link_up = CheckLinkUp(interface, gnmi_stub.get());
      EXPECT_TRUE(sut_link_up.ok());
      if (sut_link_up.ok() && sut_link_up.value()) {
        ixia_interface = info.peer_interface_name;
        sut_in_interface = interface;
        break;
      }
    }
  }

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

  ASSERT_FALSE(ixia_interface.empty());
  ASSERT_FALSE(sut_in_interface.empty());
  ASSERT_FALSE(sut_out_interface.empty());

  // Look up the port number for the egress interface
  ASSERT_OK_AND_ASSIGN(uint32_t in_id,
                       NameToP4Id(sut_in_interface, gnmi_stub.get()));
  ASSERT_OK_AND_ASSIGN(uint32_t out_id,
                       NameToP4Id(sut_out_interface, gnmi_stub.get()));

  LOG(INFO) << "\n\nTestOutDiscards:\n"
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
  EXPECT_OK(SetLoopback(true, sut_out_interface, gnmi_stub.get()));

  // Set the egress port speed to 40GB
  EXPECT_OK(SetPortSpeed(kSpeed40GB, sut_out_interface, gnmi_stub.get()));
  absl::SleepFor(absl::Seconds(15));

  auto out_status_speed = CheckPortSpeed(sut_out_interface, gnmi_stub.get());
  EXPECT_THAT(out_status_speed, IsOkAndHolds(kSpeed40GB));

  // Set up the switch to forward inbound packets to the egress port
  LOG(INFO) << "\n\n----- ForwardToEgress: TestOutDiscards -----\n";
  EXPECT_OK(ForwardToEgress(in_id, out_id, false, generic_testbed->Sut()));
  LOG(INFO) << "\n\n----- ForwardToEgress Done -----\n";

  // Read some initial counters via GNMI from the SUT
  ASSERT_OK_AND_ASSIGN(auto initial_in_counters,
                       ReadCounters(sut_in_interface, gnmi_stub.get()));
  ASSERT_OK_AND_ASSIGN(auto initial_out_counters,
                       ReadCounters(sut_out_interface, gnmi_stub.get()));

  LOG(INFO) << "\n\nTestOutDiscards:\n\n"
            << "\n\nInitial Ingress Counters (" << sut_in_interface << "):\n";
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
  LOG(INFO) << "\n\nTestOutDiscards: IxiaConnect\n\n";
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
  ASSERT_OK(ixia::SetDestMac(tref, "02:02:02:02:02:02", *generic_testbed));

  // Append an IPv4 header
  ASSERT_OK(ixia::AppendIPv4(full_tref, *generic_testbed));

  // Set up the source and destination IP addresses
  ASSERT_OK(ixia::SetSrcIPv4(tref, "192.168.0.1", *generic_testbed));
  ASSERT_OK(ixia::SetDestIPv4(tref, "192.168.0.2", *generic_testbed));

  // Set the frame size to 1514 bytes
  ASSERT_OK(ixia::SetFrameSize(tref, kMtu, *generic_testbed));

  // Start Traffic
  ASSERT_OK(ixia::StartTraffic(full_tref, ixref, *generic_testbed));

  // Wait until 10 seconds after the traffic started
  absl::Time t1;
  t1 = absl::Now();

  absl::Time t2;
  while (1) {
    t2 = absl::Now();
    if (t2 >= t1 + absl::Seconds(10)) break;
    absl::SleepFor(absl::Milliseconds(100));
  }

  LOG(INFO) << "Time at stop is " << t2;
  LOG(INFO) << "Delta is " << t2 - t1;

  ASSERT_OK(ixia::StopTraffic(full_tref, *generic_testbed));

  // Re-read the same counters via GNMI from the SUT
  ASSERT_OK_AND_ASSIGN(auto final_in_counters,
                       ReadCounters(sut_in_interface, gnmi_stub.get()));
  ASSERT_OK_AND_ASSIGN(auto final_out_counters,
                       ReadCounters(sut_out_interface, gnmi_stub.get()));

  // Check the time again
  absl::Time t3 = absl::Now();
  LOG(INFO) << "Time after statistics read is " << t3;
  LOG(INFO) << "Delta is " << t3 - t1;
  uint64_t seconds = ((t3 - t1) / absl::Seconds(1)) + 1;

  // Display the final counters
  LOG(INFO) << "\n\nTestOutDiscards:\n\n"
            << "\n\nFinal Ingress Counters (" << sut_in_interface << "):\n";
  ShowCounters(final_in_counters);
  LOG(INFO) << "\n\nFinal Egress Counters (" << sut_out_interface << "):\n";
  ShowCounters(final_out_counters);
  LOG(INFO) << "\n\n";

  // Compute the change for each counter
  auto delta_in = DeltaCounters(initial_in_counters, final_in_counters);
  auto delta_out = DeltaCounters(initial_out_counters, final_out_counters);

  // Display the difference in the counters for now (during test dev)
  LOG(INFO) << "\n\nTestOutDiscards:\n\n"
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
  uint64_t expect = 90000000;
  EXPECT_GT(delta_out.out_pkts, ((expect * 35) / 100));
  EXPECT_LT(delta_out.out_pkts, ((expect * 45) / 100));
  EXPECT_LE(delta_out.out_octets, delta_out.out_pkts * kMtu + 10000);
  EXPECT_GE(delta_out.out_octets, delta_out.out_pkts * kMtu - 10000);
  EXPECT_LE(delta_out.out_unicast_pkts, delta_out.out_pkts + 10);
  EXPECT_GE(delta_out.out_unicast_pkts, delta_out.out_pkts - 10);
  EXPECT_LE(delta_out.out_multicast_pkts, 5);
  EXPECT_EQ(delta_out.out_broadcast_pkts, 0);
  EXPECT_EQ(delta_out.out_errors, 0);
  EXPECT_GE(delta_out.out_discards, ((55 * expect) / 100));
  EXPECT_LE(delta_out.out_discards, ((65 * expect) / 100));
  EXPECT_LE(delta_out.out_ipv4_pkts, delta_out.out_pkts + 10);
  EXPECT_GE(delta_out.out_ipv4_pkts, delta_out.out_pkts - 10);
  EXPECT_EQ(delta_out.out_ipv6_pkts, 0);
  EXPECT_EQ(delta_out.out_ipv6_discarded_pkts, 0);

  LOG(INFO) << "\n\n\n\n\n---------- Restore ----------\n\n\n\n\n";

  // go through all the ports that interface to the Ixia and set them
  // back to 100GB whether their link is up or not.
  for (const auto &[interface, info] : interface_info) {
    if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR)) {
      LOG(INFO) << "Host Interface " << interface;
      EXPECT_OK(SetPortSpeed(kSpeed100GB, interface, gnmi_stub.get()));
      EXPECT_OK(SetLoopback(false, interface, gnmi_stub.get()));
    }
  }

  // Tear down any forwarding rules set up
  EXPECT_OK(ForwardTeardown(generic_testbed->Sut()));

  LOG(INFO) << "\n\n\n\n\n---------- Finished TestOutDiscards "
               "----------\n\n\n\n\n\n\n\n\n\n";
}
#endif

#if 0
TEST_P(ExampleIxiaTestFixture, TestIPv6Pkts) {
  LOG(INFO) << "\n\n\n\n\n\n\n\n\n\n---------- Starting TestIPv6Pkts "
               "----------\n\n\n\n\n";

  // Pick a testbed with an Ixia Traffic Generator. A SUT is assumed.
  thinkit::TestRequirements requirements =
      gutil::ParseProtoOrDie<thinkit::TestRequirements>(
          R"pb(interface_requirements {
                 count: 1
                 interface_mode: TRAFFIC_GENERATOR
               })pb");

  ASSERT_OK_AND_ASSIGN(std::unique_ptr<thinkit::GenericTestbed> generic_testbed,
                       GetTestbedWithRequirements(requirements));

  absl::flat_hash_map<std::string, thinkit::InterfaceInfo> interface_info =
      generic_testbed->GetSutInterfaceInfo();

  // Connect to TestTracker for test status
  generic_testbed->Environment().SetTestCaseID(
      "3f3859b8-7602-479c-a2ad-ab964ded694b");

  // Hook up to GNMI
  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, generic_testbed->Sut().CreateGnmiStub());

  // go through all the ports that interface to the Ixia and set them
  // to 100GB since the Ixia ports are all 100GB.
  for (const auto &[interface, info] : interface_info) {
    if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR)) {
      LOG(INFO) << "Host Interface " << interface;
      EXPECT_OK(SetPortSpeed(kSpeed100GB, interface, gnmi_stub.get()));
    }
  }

  // Wait to let the links come up
  absl::SleepFor(absl::Seconds(20));

  // Loop through the interface_info looking for Ixia/SUT interface pairs,
  // checking if the link is up.  we need one pair with link up for the
  // ingress interface/IXIA traffic generation
  std::string ixia_interface = "";
  std::string sut_in_interface = "";

  for (const auto &[interface, info] : interface_info) {
    if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR)) {
      auto sut_link_up = CheckLinkUp(interface, gnmi_stub.get());
      EXPECT_TRUE(sut_link_up.ok());
      if (sut_link_up.ok() && sut_link_up.value()) {
        ixia_interface = info.peer_interface_name;
        sut_in_interface = interface;
        break;
      }
    }
  }

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

  ASSERT_FALSE(ixia_interface.empty());
  ASSERT_FALSE(sut_in_interface.empty());
  ASSERT_FALSE(sut_out_interface.empty());

  // Look up the port number for the egress interface
  ASSERT_OK_AND_ASSIGN(uint32_t in_id,
                       NameToP4Id(sut_in_interface, gnmi_stub.get()));
  ASSERT_OK_AND_ASSIGN(uint32_t out_id,
                       NameToP4Id(sut_out_interface, gnmi_stub.get()));

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
  EXPECT_OK(SetLoopback(true, sut_out_interface, gnmi_stub.get()));

  // Set up the switch to forward inbound packets to the egress port
  EXPECT_OK(ForwardToEgress(in_id, out_id, true, generic_testbed->Sut()));

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
  ASSERT_OK(ixia::SetDestMac(tref, "02:02:02:02:02:02", *generic_testbed));

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

  // Wait until 10 seconds after the traffic started
  absl::Time t1;
  t1 = absl::Now();

  absl::Time t2;
  while (1) {
    t2 = absl::Now();
    if (t2 >= t1 + absl::Seconds(10)) break;
    absl::SleepFor(absl::Milliseconds(100));
  }

  LOG(INFO) << "Time at stop is " << t2;
  LOG(INFO) << "Delta is " << t2 - t1;

  ASSERT_OK(ixia::StopTraffic(full_tref, *generic_testbed));

  // Re-read the same counters via GNMI from the SUT
  ASSERT_OK_AND_ASSIGN(auto final_in_counters,
                       ReadCounters(sut_in_interface, gnmi_stub.get()));
  ASSERT_OK_AND_ASSIGN(auto final_out_counters,
                       ReadCounters(sut_out_interface, gnmi_stub.get()));

  // Check the time again
  absl::Time t3 = absl::Now();
  LOG(INFO) << "Time after statistics read is " << t3;
  LOG(INFO) << "Delta is " << t3 - t1;
  uint64_t seconds = ((t3 - t1) / absl::Seconds(1)) + 1;

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
  EXPECT_LE(delta_out.out_octets, delta_out.out_pkts * kMtu + 10000);
  EXPECT_GE(delta_out.out_octets, delta_out.out_pkts * kMtu - 10000);
  EXPECT_LE(delta_out.out_unicast_pkts, delta_out.out_pkts + 10);
  EXPECT_GE(delta_out.out_unicast_pkts, delta_out.out_pkts - 10);
  EXPECT_LE(delta_out.out_multicast_pkts, 5);
  EXPECT_EQ(delta_out.out_broadcast_pkts, 0);
  EXPECT_EQ(delta_out.out_errors, 0);
  EXPECT_EQ(delta_out.out_discards, 0);
  EXPECT_EQ(delta_out.out_ipv4_pkts, 0);
  EXPECT_GE(delta_out.in_ipv6_pkts, delta_out.out_pkts - 10);
  EXPECT_LE(delta_out.in_ipv6_pkts, delta_out.out_pkts + 10);
  EXPECT_LE(delta_out.out_ipv6_pkts, delta_out.out_pkts + 10);
  EXPECT_GE(delta_out.out_ipv6_pkts, delta_out.out_pkts - 10);
  EXPECT_EQ(delta_out.out_ipv6_discarded_pkts, 0);
  EXPECT_LE(delta_in.in_ipv6_pkts, delta_out.out_pkts + 10);
  EXPECT_GE(delta_in.in_ipv6_pkts, delta_out.out_pkts - 10);

  LOG(INFO) << "\n\n\n\n\n---------- Restore ----------\n\n\n\n\n";

  // go through all the ports that interface to the Ixia and set them
  // back to 100GB whether their link is up or not.
  for (const auto &[interface, info] : interface_info) {
    if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR)) {
      LOG(INFO) << "Host Interface " << interface;
      EXPECT_OK(SetPortSpeed(kSpeed100GB, interface, gnmi_stub.get()));
      EXPECT_OK(SetLoopback(false, interface, gnmi_stub.get()));
    }
  }

  // Tear down any forwarding rules set up
  EXPECT_OK(ForwardTeardown(generic_testbed->Sut()));

  LOG(INFO) << "\n\n\n\n\n---------- Finished TestIPv6Pkts "
               "----------\n\n\n\n\n\n\n\n\n\n";
}
#endif

#if 0
TEST_P(ExampleIxiaTestFixture, TestCPUOutDiscards) {
  LOG(INFO) << "\n\n\n\n\n\n\n\n\n\n---------- Starting TestCPUOutDiscards "
               "----------\n\n\n\n\n";

  // Pick a testbed with an Ixia Traffic Generator. A SUT is assumed.
  thinkit::TestRequirements requirements =
      gutil::ParseProtoOrDie<thinkit::TestRequirements>(
          R"pb(interface_requirements {
                 count: 1
                 interface_mode: TRAFFIC_GENERATOR
               })pb");

  ASSERT_OK_AND_ASSIGN(std::unique_ptr<thinkit::GenericTestbed> generic_testbed,
                       GetTestbedWithRequirements(requirements));

  absl::flat_hash_map<std::string, thinkit::InterfaceInfo> interface_info =
      generic_testbed->GetSutInterfaceInfo();

  // Connect to TestTracker for test status
  generic_testbed->Environment().SetTestCaseID(
      "3c8823ab-1aba-48a5-8af6-90d2f268c699");

  // Hook up to GNMI
  ASSERT_OK_AND_ASSIGN(auto gnmi_stub, generic_testbed->Sut().CreateGnmiStub());

  // go through all the ports that interface to the Ixia and set them
  // to 100GB since the Ixia ports are all 100GB.
  for (const auto &[interface, info] : interface_info) {
    if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR)) {
      LOG(INFO) << "Host Interface " << interface;
      EXPECT_OK(SetPortSpeed(kSpeed100GB, interface, gnmi_stub.get()));
    }
  }

  // Wait to let the links come up
  absl::SleepFor(absl::Seconds(20));

  // Loop through the interface_info looking for Ixia/SUT interface pairs,
  // checking if the link is up.  we need one pair with link up for the
  // ingress interface/IXIA traffic generation
  std::string ixia_interface = "";
  std::string sut_in_interface = "";

  for (const auto &[interface, info] : interface_info) {
    if (info.interface_modes.contains(thinkit::TRAFFIC_GENERATOR)) {
      auto sut_link_up = CheckLinkUp(interface, gnmi_stub.get());
      EXPECT_TRUE(sut_link_up.ok());
      if (sut_link_up.ok() && sut_link_up.value()) {
        ixia_interface = info.peer_interface_name;
        sut_in_interface = interface;
        break;
      }
    }
  }

  ASSERT_FALSE(ixia_interface.empty());
  ASSERT_FALSE(sut_in_interface.empty());

  // Look up the port numbers for the ingress and interface
  ASSERT_OK_AND_ASSIGN(uint32_t in_id,
                       NameToP4Id(sut_in_interface, gnmi_stub.get()));

  LOG(INFO) << "\n\nTestCPUOutDiscards:\n"
            << "Chose Ixia interface " << ixia_interface << "\n"
            << "and SUT ingress interface " << sut_in_interface << " (id "
            << in_id << ")\n\n";

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

  // Set up the switch to forward inbound IPv4 packets to the egress port
  // We're doing this to overwhelm the egress port so at least some of the
  // packets we'll send from the CPU get discarded
  LOG(INFO) << "\n\n----- TestCPUOutDiscards: TrapToCPU -----\n";
  EXPECT_OK(TrapToCPU(generic_testbed->Sut()));
  LOG(INFO) << "\n\n----- TrapToCPU Done -----\n";

  // Read some initial counters via GNMI from the SUT
  ASSERT_OK_AND_ASSIGN(auto initial_in_counters,
                       ReadCounters(sut_in_interface, gnmi_stub.get()));
  std::string cpu_iface = "CPU";
  ASSERT_OK_AND_ASSIGN(auto initial_cpu_out_discards,
                       GetGnmiStat("out-discards", cpu_iface, gnmi_stub.get()));
  ASSERT_OK_AND_ASSIGN(auto initial_cpu_in_discards,
                       GetGnmiStat("in-discards", cpu_iface, gnmi_stub.get()));

  LOG(INFO) << "\n\nTestCPUOutDiscards:\n\n"
            << "\n\nInitial Ingress Counters (" << sut_in_interface << "):\n";
  ShowCounters(initial_in_counters);
  LOG(INFO) << "\n\nInitial CPU in-discards " << initial_cpu_in_discards
            << "\n\n";
  LOG(INFO) << "\n\nInitial CPU out-discards " << initial_cpu_out_discards
            << "\n\n";

  // Connect to the Ixia
  LOG(INFO) << "\n\nTestCPUOutDiscards: IxiaConnect\n\n";
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

  // Set the source & destination MAC addresses
  ASSERT_OK(ixia::SetSrcMac(tref, "00:01:02:03:04:05", *generic_testbed));
  ASSERT_OK(ixia::SetDestMac(tref, "02:02:02:02:02:02", *generic_testbed));

  // Append an IPv4 header
  ASSERT_OK(ixia::AppendIPv4(full_tref, *generic_testbed));

  // Set up the source and destination IP addresses
  ASSERT_OK(ixia::SetSrcIPv4(tref, "192.168.0.1", *generic_testbed));
  ASSERT_OK(ixia::SetDestIPv4(tref, "192.168.0.2", *generic_testbed));

  // Set the frame size to 1514 bytes
  ASSERT_OK(ixia::SetFrameSize(tref, kMtu, *generic_testbed));

  // Start the traffic
  ASSERT_OK(ixia::StartTraffic(full_tref, ixref, *generic_testbed));

  // Wait for 10 seconds after the test starts
  absl::Time t1;
  t1 = absl::Now();

  absl::Time t2;
  while (1) {
    t2 = absl::Now();
    if (t2 >= t1 + absl::Seconds(10)) break;
    absl::SleepFor(absl::Milliseconds(100));
  }

  LOG(INFO) << "Time at stop is " << t2;
  LOG(INFO) << "Delta is " << t2 - t1;

  ASSERT_OK(ixia::StopTraffic(full_tref, *generic_testbed));

  // Re-read the same counters via GNMI from the SUT
  ASSERT_OK_AND_ASSIGN(auto final_in_counters,
                       ReadCounters(sut_in_interface, gnmi_stub.get()));
  ASSERT_OK_AND_ASSIGN(auto final_cpu_in_discards,
                       GetGnmiStat("in-discards", cpu_iface, gnmi_stub.get()));
  ASSERT_OK_AND_ASSIGN(auto final_cpu_out_discards,
                       GetGnmiStat("out-discards", cpu_iface, gnmi_stub.get()));

  // Check the time again
  absl::Time t3 = absl::Now();
  LOG(INFO) << "Time after statistics read is " << t3;
  LOG(INFO) << "Delta is " << t3 - t1;
  uint64_t seconds = ((t3 - t1) / absl::Seconds(1)) + 1;

  // Display the final counters
  LOG(INFO) << "\n\nTestCPUOutDiscards:\n\n"
            << "\n\nFinal Ingress Counters (" << sut_in_interface << "):\n";
  ShowCounters(final_in_counters);
  LOG(INFO) << "\n\nFinal CPU in-discards " << final_cpu_in_discards << "\n\n";
  LOG(INFO) << "\n\nFinal CPU out-discards " << final_cpu_out_discards
            << "\n\n";

  // Compute the change for each counter
  auto delta_in = DeltaCounters(initial_in_counters, final_in_counters);
  auto delta_cpu_in_discards = final_cpu_in_discards - initial_cpu_in_discards;
  auto delta_cpu_out_discards =
      final_cpu_out_discards - initial_cpu_out_discards;

  // Display the difference in the counters for now (during test dev)
  LOG(INFO) << "\n\nTestCPUOutDiscards:\n\n"
            << "\n\nIngress Deltas (" << sut_in_interface << ") in " << seconds
            << " seconds:";
  ShowCounters(delta_in);
  LOG(INFO) << "\n\nDelta CPU in-discards " << delta_cpu_in_discards << "\n\n";
  LOG(INFO) << "\n\nDelta CPU out-discards " << delta_cpu_out_discards
            << "\n\n";

  LOG(INFO) << "\n\n\n\n\n---------- Restore ----------\n\n\n\n\n";

  // Tear down any forwarding rules set up
  EXPECT_OK(ForwardTeardown(generic_testbed->Sut()));

  LOG(INFO) << "\n\n\n\n\n---------- Finished TestCPUOutDiscards "
               "----------\n\n\n\n\n\n\n\n\n\n";
}
#endif

}  // namespace pins_test
