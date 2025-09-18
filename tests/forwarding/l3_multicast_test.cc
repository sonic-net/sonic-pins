// Copyright 2025 Google LLC
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
#include "tests/forwarding/l3_multicast_test.h"

#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

#include "absl/algorithm/container.h"
#include "absl/log/check.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "dvaas/dataplane_validation.h"
#include "dvaas/port_id_map.h"
#include "dvaas/test_vector.h"
#include "dvaas/test_vector.pb.h"
#include "dvaas/validation_result.h"
#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/status_matchers.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/gnmi/openconfig.pb.h"
#include "net/google::protobuf/contrib/fixtures/proto-fixture-repository.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/netaddr/ipv4_address.h"
#include "p4_pdpi/netaddr/ipv6_address.h"
#include "p4_pdpi/netaddr/mac_address.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_pdpi/sequencing.h"
#include "platforms/networking/gpins/testing/blackbox/p4/dvaas/gpins_dvaas.h"
#include "platforms/networking/gpins/testing/lib/test_util.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"
#include "tests/lib/p4info_helper.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "thinkit/switch.h"
#include "util/gtl/value_or_die.h"

namespace pins_test {
namespace {

using ::google::protobuf::contrib::fixtures::ProtoFixtureRepository;
using ::gutil::StatusIs;
using ::testing::AllOf;
using ::testing::HasSubstr;

// Common programming parameters.
constexpr int kMaxRifs = 128;
// TODO: Increase to 512 multicast groups.
constexpr int kMaxMulticastGroups = 505;
constexpr absl::string_view kDefaultMulticastVrf = "vrf-mcast";
constexpr netaddr::MacAddress kOriginalSrcMacAddress(0x00, 0x22, 0x33, 0x44,
                                                     0x55, 0x66);
constexpr netaddr::MacAddress kDropSrcMacAddress(0x02, 0x2a, 0x10, 0x00, 0x00,
                                                 0x02);
constexpr int kDefaultInstance = 0;
// Pair of port ID and instance.
struct ReplicaPair {
  std::string port_id;
  int instance;
};

enum class IpmcGroupAssignmentMechanism { kAclRedirect, kIpMulticastTable };

// Multicast IPv4 addresses of the form 226.10.#.#. The last two bytes
// are computed based on the multicast group ID.
absl::StatusOr<netaddr::Ipv4Address> GetIpv4AddressForReplica(
    int multicast_group_index) {
  if (multicast_group_index >= 0 && multicast_group_index < 511) {
    return netaddr::Ipv4Address(226, 10,
                                ((multicast_group_index + 1) >> 8) & 0xff,
                                (multicast_group_index + 1) & 0xff);
  } else {
    return absl::FailedPreconditionError(
        absl::StrCat("Multicast group index '", multicast_group_index,
                     "' is larger than test's maximum value of 510"));
  }
}

// Multicast IPv6 addresses of the form ff00:0:1111:2222:3333:4444:5555.#.
// The last 16-bits of the address are based on the multicast group ID.
absl::StatusOr<netaddr::Ipv6Address> GetIpv6AddressForReplica(
    int multicast_group_index) {
  if (multicast_group_index >= 0 && (multicast_group_index + 1) < 0xffff) {
    return netaddr::Ipv6Address(0xff00, 0x0, 0x1111, 0x2222, 0x3333, 0x4444,
                                0x5555, multicast_group_index + 1);
  } else {
    return absl::FailedPreconditionError(
        absl::StrCat("Multicast group index '", multicast_group_index,
                     "' is larger than test's maximum value of ", 0xfffe));
  }
}

absl::StatusOr<netaddr::MacAddress> GetSrcMacForReplica(
    int multicast_group_index, int replicas_per_group, int replicas_number) {
  if (multicast_group_index * replicas_per_group + replicas_number < 0xff) {
    return netaddr::MacAddress(
        0x00, 0x20, 0x30, 0x40, 0x50,
        multicast_group_index * replicas_per_group + replicas_number);
  } else {
    return absl::FailedPreconditionError(absl::StrCat(
        "Combination of multicast group index '", multicast_group_index,
        "', replicas per group '", replicas_per_group,
        "', and replicas_number '", replicas_number,
        "' is larger than test's maximum value of ", 0xfe));
  }
}

absl::StatusOr<std::vector<std::string>> GetNUpInterfaceIDs(
    thinkit::Switch& device, int num_interfaces) {
  // The test fixture pushes a new config during setup so we give the switch a
  // few minutes to converge before failing to report no valid ports.
  absl::Duration time_limit = absl::Minutes(3);
  absl::Time stop_time = absl::Now() + time_limit;
  std::vector<std::string> port_names;
  while (port_names.size() < num_interfaces) {
    if (absl::Now() > stop_time) {
      return absl::FailedPreconditionError(
          absl::StrCat("Could not find ", num_interfaces, " interfaces in ",
                       absl::FormatDuration(time_limit), "."));
    }
    ASSIGN_OR_RETURN(auto gnmi_stub, device.CreateGnmiStub());
    ASSIGN_OR_RETURN(port_names,
                     pins_test::GetUpInterfacesOverGnmi(
                         *gnmi_stub, pins_test::InterfaceType::kSingleton));
  }
  ASSIGN_OR_RETURN(auto gnmi_stub, device.CreateGnmiStub());
  ASSIGN_OR_RETURN(auto port_id_by_name,
                   GetAllInterfaceNameToPortId(*gnmi_stub));
  // Return encoded port ID as result.
  LOG(INFO) << "Port name to id mapping:";
  std::vector<std::string> result;
  for (const auto& port_name : port_names) {
    if (auto it = port_id_by_name.find(port_name);
        it != port_id_by_name.end()) {
      result.push_back(it->second);
      LOG(INFO) << "  " << port_name << " : " << it->second;
    }
  }
  return result;
}

// Add table entries for multicast_router_interface_table.
absl::StatusOr<std::vector<p4::v1::Entity>> CreateRifTableEntities(
    const pdpi::IrP4Info& ir_p4info, const std::string& port_id,
    const int instance, const netaddr::MacAddress& src_mac) {
  ASSIGN_OR_RETURN(std::vector<p4::v1::Entity> entities,
                   sai::EntryBuilder()
		       .AddMrifEntryRewritingSrcMac(port_id, instance, src_mac)
                       .LogPdEntries()
                       .GetDedupedPiEntities(ir_p4info,
                                             /*allow_unsupported=*/true));
  return entities;
}

// Add packet replication engine entries.
absl::StatusOr<std::vector<p4::v1::Entity>> CreateMulticastGroupEntities(
    const pdpi::IrP4Info& ir_p4info, int multicast_group_id,
    const std::vector<ReplicaPair>& replicas) {
  std::vector<sai::Replica> sai_replicas;
  for (const auto& [port, instance] : replicas) {
    sai_replicas.push_back(
        sai::Replica{.egress_port = port, .instance = instance});
  }
  ASSIGN_OR_RETURN(std::vector<p4::v1::Entity> entities,
                   sai::EntryBuilder()
                       .AddMulticastGroupEntry(multicast_group_id, sai_replicas)
                       .LogPdEntries()
                       .GetDedupedPiEntities(ir_p4info));
  return entities;
}

// Add table entries for ipv4_multicast_table.
absl::StatusOr<std::vector<p4::v1::Entity>> CreateIpv4MulticastTableEntities(
    const pdpi::IrP4Info& ir_p4info, const std::string& vrf_id,
    const netaddr::Ipv4Address& ip_address, int multicast_group_id) {
  ASSIGN_OR_RETURN(
      std::vector<p4::v1::Entity> entities,
      sai::EntryBuilder()
          .AddMulticastRoute(vrf_id, ip_address, multicast_group_id)
          .LogPdEntries()
          .GetDedupedPiEntities(ir_p4info,
                                /*allow_unsupported=*/true));
  return entities;
}

// Add table entries for ipv6_multicast_table.
absl::StatusOr<std::vector<p4::v1::Entity>> CreateIpv6MulticastTableEntities(
    const pdpi::IrP4Info& ir_p4info, const std::string& vrf_id,
    const netaddr::Ipv6Address& ip_address, int multicast_group_id) {
  ASSIGN_OR_RETURN(
      std::vector<p4::v1::Entity> entities,
      sai::EntryBuilder()
          .AddMulticastRoute(vrf_id, ip_address, multicast_group_id)
          .LogPdEntries()
          .GetDedupedPiEntities(ir_p4info,
                                /*allow_unsupported=*/true));
  return entities;
}

packetlib::Packet ParsePacketAndPadToMinimumSize(
    const ProtoFixtureRepository& repo, absl::string_view packet_pb) {
  packetlib::Packet packet = repo.ParseTextOrDie<packetlib::Packet>(packet_pb);
  CHECK_OK(packetlib::PadPacketToMinimumSize(packet));
  return packet;
}

// Clears the given `entities`.
absl::Status ClearEntities(pdpi::P4RuntimeSession& session,
                           const pdpi::IrP4Info& info,
                           absl::Span<const p4::v1::Entity> entities) {
  // Early return if there is nothing to clear.
  if (entities.empty()) return absl::OkStatus();
  std::vector<p4::v1::Entity> sorted_pi_entities{entities.begin(),
                                                 entities.end()};

  // Sort by dependency order, then reverse since we will be deleting.
  RETURN_IF_ERROR(pdpi::StableSortEntities(info, sorted_pi_entities));
  absl::c_reverse(sorted_pi_entities);

  RETURN_IF_ERROR(SendPiUpdates(
      &session,
      pdpi::CreatePiUpdates(sorted_pi_entities, p4::v1::Update::DELETE)))
      << "when attempting to delete the following entities: "
      << absl::StrJoin(sorted_pi_entities, "\n");

  return absl::OkStatus();
}

// Setup multicast and other related tables for forwarding multicast packets.
absl::Status SetupDefaultMulticastProgramming(
    pdpi::P4RuntimeSession& session, const pdpi::IrP4Info& ir_p4info,
    const p4::v1::Update_Type& update_type, int number_multicast_groups,
    int replicas_per_group, const std::vector<std::string>& port_ids,
    IpmcGroupAssignmentMechanism assignment_mechanism,
    std::vector<p4::v1::Entity>& entities_created) {
  if (port_ids.size() < replicas_per_group) {
    return gutil::InternalErrorBuilder()
           << "Not enough port IDs provided to setup multicast programming:"
           << " expected: " << replicas_per_group
           << " received: " << port_ids.size();
  }

  // Setup admission for all L3 packets, a default VRF,
  // assign all IP packets to the default VRF
  ASSIGN_OR_RETURN(std::vector<p4::v1::Entity> acl_entities,
                   sai::EntryBuilder()
                       .AddEntryAdmittingAllPacketsToL3()
                       .AddVrfEntry(kDefaultMulticastVrf)
                       .AddPreIngressAclEntryAssigningVrfForGivenIpType(
                           kDefaultMulticastVrf, sai::IpVersion::kIpv4And6)
                       .LogPdEntries()
                       .GetDedupedPiEntities(ir_p4info));

  RETURN_IF_ERROR(pdpi::InstallPiEntities(&session, ir_p4info, acl_entities));
  entities_created.insert(entities_created.end(), acl_entities.begin(),
                          acl_entities.end());
  // Setup multicast RIF table.
  std::vector<p4::v1::Entity> rif_entities;
  for (int m = 0; m < number_multicast_groups; ++m) {
    for (int r = 0; r < replicas_per_group; ++r) {
      const std::string& port_id = port_ids.at(r + 1);
      // Unique Ether src mac base address.
      ASSIGN_OR_RETURN(netaddr::MacAddress src_mac,
                       GetSrcMacForReplica(m, replicas_per_group, r));
      ASSIGN_OR_RETURN(auto rifs,
                       CreateRifTableEntities(ir_p4info, port_id,
                                              kDefaultInstance, src_mac));
      rif_entities.insert(rif_entities.end(), rifs.begin(), rifs.end());
    }
  }
  RETURN_IF_ERROR(pdpi::InstallPiEntities(&session, ir_p4info, rif_entities));
  entities_created.insert(entities_created.end(), rif_entities.begin(),
                          rif_entities.end());

  // Setup multicast groups and group members.
  std::vector<p4::v1::Entity> mc_entities;
  for (int m = 0; m < number_multicast_groups; ++m) {
    std::vector<ReplicaPair> replicas;
    for (int r = 0; r < replicas_per_group; ++r) {
      const std::string& port_id = port_ids.at(r + 1);
      replicas.push_back({port_id, kDefaultInstance});
    }
    // Note: multicast group ID 0 is not valid.
    int multicast_group_id = m + 1;
    ASSIGN_OR_RETURN(auto mcs, CreateMulticastGroupEntities(
                                   ir_p4info, multicast_group_id, replicas));
    mc_entities.insert(mc_entities.end(), mcs.begin(), mcs.end());
  }
  RETURN_IF_ERROR(pdpi::InstallPiEntities(&session, ir_p4info, mc_entities));
  entities_created.insert(entities_created.end(), mc_entities.begin(),
                          mc_entities.end());

  if (assignment_mechanism == IpmcGroupAssignmentMechanism::kAclRedirect) {
    // Setup multicast group assignment (ACL redirect).
    // In the default traffic test setup, we only send traffic on one port
    // (port_index 0), so we only need to add one ACL entry.
    const std::string& port_id = port_ids[0];
    ASSIGN_OR_RETURN(std::vector<p4::v1::Entity> acl_entities,
                     sai::EntryBuilder()
                         .AddIngressAclEntryRedirectingToMulticastGroup(
                             /*multicast_group_id=*/1,
                             {.in_port = port_id, .ipmc_table_hit = false})
                         .LogPdEntries()
                         .GetDedupedPiEntities(ir_p4info));
    RETURN_IF_ERROR(pdpi::InstallPiEntities(&session, ir_p4info, acl_entities));
    entities_created.insert(entities_created.end(), acl_entities.begin(),
                            acl_entities.end());
    return absl::OkStatus();
  }

  // Setup multicast group assignment (IPMC entries).
  std::vector<p4::v1::Entity> ipmc_entities;
  for (int m = 0; m < number_multicast_groups; ++m) {
    ASSIGN_OR_RETURN(const netaddr::Ipv4Address ipv4_address,
                     GetIpv4AddressForReplica(m));
    uint8_t multicast_group_id = m + 1;
    std::string vrf_id = std::string(kDefaultMulticastVrf);
    ASSIGN_OR_RETURN(auto ipmcs_v4,
                     CreateIpv4MulticastTableEntities(
                         ir_p4info, vrf_id, ipv4_address, multicast_group_id));
    ipmc_entities.insert(ipmc_entities.end(), ipmcs_v4.begin(), ipmcs_v4.end());
    // Also add an IPv6 address that assigns to the same multicast group.
    ASSIGN_OR_RETURN(const netaddr::Ipv6Address ipv6_address,
                     GetIpv6AddressForReplica(m));
    ASSIGN_OR_RETURN(auto ipmcs_v6,
                     CreateIpv6MulticastTableEntities(
                         ir_p4info, vrf_id, ipv6_address, multicast_group_id));
    ipmc_entities.insert(ipmc_entities.end(), ipmcs_v6.begin(), ipmcs_v6.end());
  }

  RETURN_IF_ERROR(pdpi::InstallPiEntities(&session, ir_p4info, ipmc_entities));
  entities_created.insert(entities_created.end(), ipmc_entities.begin(),
                          ipmc_entities.end());
  return absl::OkStatus();
}

// Build test packets that match the multicast table entries
absl::StatusOr<std::vector<dvaas::PacketTestVector>> BuildTestVectors(
    const std::vector<std::string>& port_ids, int number_multicast_groups,
    int replicas_per_group, bool expect_output_packets = true) {
  // Test packets injected and expected results.
  std::vector<dvaas::PacketTestVector> expectations;
  // All packets will be injected on the same port.
  const std::string& in_port = port_ids.at(0);
  int total_packets = 0;
  int unique_payload_ids = 1;
  for (int m = 0; m < number_multicast_groups; ++m) {
    ASSIGN_OR_RETURN(const auto ipv4_address, GetIpv4AddressForReplica(m));
    ASSIGN_OR_RETURN(const auto ipv6_address, GetIpv6AddressForReplica(m));
    // Construct the input packets.
    // We will inject 2 packets to touch each multicast group, one using IPv4
    // and one using IPv6.
    ProtoFixtureRepository repo;
    repo.RegisterValue("@ingress_port", in_port)
        .RegisterValue("@egress_src_mac", kOriginalSrcMacAddress.ToString())
        .RegisterValue("@ttl", "0x40")
        .RegisterValue("@hop_limit", "0x50")
        .RegisterValue("@decremented_hop_limit", "0x4f")
        .RegisterValue("@decremented_ttl", "0x3f")
        .RegisterValue("@ipv4_dst", ipv4_address.ToString())
        .RegisterValue("@ipv6_dst", ipv6_address.ToString())
        .RegisterValue(
            "@payload_ipv4",
            dvaas::MakeTestPacketPayloadFromUniqueId(unique_payload_ids++))
        .RegisterValue(
            "@payload_ipv6",
            dvaas::MakeTestPacketPayloadFromUniqueId(unique_payload_ids++));
    // Build headers.
    repo.RegisterSnippetOrDie<packetlib::Header>("@ethernet_ipv4", R"pb(
          ethernet_header {
            ethernet_destination: "01:00:5e:01:01:01"
            ethernet_source: @egress_src_mac
            ethertype: "0x0800"  # IPv4
          }
        )pb")
        .RegisterSnippetOrDie<packetlib::Header>("@ethernet_ipv6", R"pb(
          ethernet_header {
            ethernet_destination: "33:33:00:00:00:01"
            ethernet_source: @egress_src_mac
            ethertype: "0x86dd"  # IPv6
          }
        )pb")
        .RegisterSnippetOrDie<packetlib::Header>("@ipv4", R"pb(
          ipv4_header {
            version: "0x4"
            ihl: "0x5"
            dscp: "0x00"
            ecn: "0x0"
            # total_length: filled in automatically.
            identification: "0x0000"
            flags: "0x0"
            fragment_offset: "0x0000"
            ttl: @ttl
            protocol: "0x11"
            # checksum: filled in automatically
            ipv4_source: "128.252.7.36"
            ipv4_destination: @ipv4_dst
          }
        )pb")
        .RegisterSnippetOrDie<packetlib::Header>("@ipv6", R"pb(
          ipv6_header {
            version: "0x6"
            dscp: "0x00"
            ecn: "0x1"
            flow_label: "0x12345"
            # payload_length: filled in automatically.
            next_header: "0x11"
            hop_limit: @hop_limit
            ipv6_source: "2002:ad12:4100:3::"
            ipv6_destination: @ipv6_dst
          }
        )pb")
        .RegisterSnippetOrDie<packetlib::Header>("@udp", R"pb(
          udp_header {
            source_port: "0x0567"       # 1383
            destination_port: "0x1234"  # 4660
            # length: filled in automatically
            # checksum: filled in automatically
          }
        )pb")
        .RegisterMessage("@input_packet_ipv4", ParsePacketAndPadToMinimumSize(
                                                   repo,
                                                   R"pb(
                                                     headers: @ethernet_ipv4
                                                     headers: @ipv4
                                                     headers: @udp
                                                     payload: @payload_ipv4
                                                   )pb"))
        .RegisterMessage("@input_packet_ipv6", ParsePacketAndPadToMinimumSize(
                                                   repo,
                                                   R"pb(
                                                     headers: @ethernet_ipv6
                                                     headers: @ipv6
                                                     headers: @udp
                                                     payload: @payload_ipv6
                                                   )pb"));
    // Build up acceptable_outputs string, to account for each replica.
    dvaas::SwitchOutput expected_ipv4_output;
    dvaas::SwitchOutput expected_ipv6_output;
    for (int r = 0; r < replicas_per_group; ++r) {
      ASSIGN_OR_RETURN(const auto egress_src_mac,
                       GetSrcMacForReplica(m, replicas_per_group, r));
      // IPv4
      *expected_ipv4_output.add_packets() =
          repo.RegisterValue("@egress_port", port_ids.at(r + 1))
              .RegisterValue("@egress_src_mac", egress_src_mac.ToString())
              .RegisterMessage(
                  "@output_packet", ParsePacketAndPadToMinimumSize(repo, R"pb(
                    headers: @ethernet_ipv4 {
                      ethernet_header { ethernet_source: @egress_src_mac }
                    }
                    headers: @ipv4 { ipv4_header { ttl: @decremented_ttl } }
                    headers: @udp
                    payload: @payload_ipv4
                  )pb"))
              .ParseTextOrDie<dvaas::Packet>(R"pb(
                port: @egress_port
                parsed: @output_packet
              )pb");
      // IPv6
      *expected_ipv6_output.add_packets() =
          repo.RegisterValue("@egress_port", port_ids.at(r + 1))
              .RegisterValue("@egress_src_mac", egress_src_mac.ToString())
              .RegisterMessage(
                  "@output_packet", ParsePacketAndPadToMinimumSize(repo, R"pb(
                    headers: @ethernet_ipv6 {
                      ethernet_header { ethernet_source: @egress_src_mac }
                    }
                    headers: @ipv6 {
                      ipv6_header { hop_limit: @decremented_hop_limit }
                    }
                    headers: @udp
                    payload: @payload_ipv6
                  )pb"))
              .ParseTextOrDie<dvaas::Packet>(R"pb(
                port: @egress_port
                parsed: @output_packet
              )pb");
    }  // for replica
    LOG(INFO) << "Packets will be sent on port " << in_port;
    LOG(INFO) << "Expected outputs should be " << total_packets << " packets";

    if (expect_output_packets) {
      expectations.emplace_back() =
          repo.RegisterMessage("@expected_ipv4_output", expected_ipv4_output)
              .ParseTextOrDie<dvaas::PacketTestVector>(R"pb(
                input {
                  type: DATAPLANE
                  packet { port: @ingress_port parsed: @input_packet_ipv4 }
                }
                acceptable_outputs: @expected_ipv4_output
              )pb");
      expectations.emplace_back() =
          repo.RegisterMessage("@expected_ipv6_output", expected_ipv6_output)
              .ParseTextOrDie<dvaas::PacketTestVector>(R"pb(
                input {
                  type: DATAPLANE
                  packet { port: @ingress_port parsed: @input_packet_ipv6 }
                }
                acceptable_outputs: @expected_ipv6_output
              )pb");
    } else {
      expectations.push_back(repo.ParseTextOrDie<dvaas::PacketTestVector>(
          R"pb(
            input {
              type: DATAPLANE
              packet { port: @ingress_port parsed: @input_packet_ipv4 }
            }
          )pb"));
      expectations.push_back(repo.ParseTextOrDie<dvaas::PacketTestVector>(
          R"pb(
            input {
              type: DATAPLANE
              packet { port: @ingress_port parsed: @input_packet_ipv6 }
            }
          )pb"));
    }
  }  // for multicast group
  return expectations;
}

TEST_P(L3MulticastTestFixture, InsertMulticastGroupBeforeRifFails) {
  const int kNumberRifs = 2;
  ASSERT_OK_AND_ASSIGN(
      auto sut_ports_ids,
      GetNUpInterfaceIDs(GetParam().mirror_testbed->GetMirrorTestbed().Sut(),
                         kNumberRifs));
  // If we do not have a RIF, we cannot create multicast group members.
  std::vector<ReplicaPair> replicas;
  for (int r = 0; r < kNumberRifs; ++r) {
    const std::string& port_id = sut_ports_ids.at(r);
    replicas.push_back({port_id, kDefaultInstance});
  }
  ASSERT_OK_AND_ASSIGN(auto entities, CreateMulticastGroupEntities(
                                          ir_p4info_,
                                          /*multicast_group_id=*/2, replicas));
  EXPECT_THAT(
      pdpi::InstallPiEntities(sut_p4rt_session_.get(), ir_p4info_, entities),
      StatusIs(absl::StatusCode::kUnknown,
               AllOf(HasSubstr("#1: NOT_FOUND"),
                     HasSubstr("[OrchAgent] No corresponding "
                               "FIXED_MULTICAST_ROUTER_INTERFACE_TABLE"),
                     HasSubstr("entry found for multicast group"))));
}

TEST_P(L3MulticastTestFixture,
       InsertIpMulticastEntryBeforeMulticastGroupFails) {
  // Create a VRF.
  ASSERT_OK_AND_ASSIGN(const std::vector<p4::v1::Entity> vrf_entities,
                       sai::EntryBuilder()
                           .AddVrfEntry(kDefaultMulticastVrf)
                           .LogPdEntries()
                           .GetDedupedPiEntities(ir_p4info_));
  EXPECT_OK(pdpi::InstallPiEntities(sut_p4rt_session_.get(), ir_p4info_,
                                    vrf_entities));

  // If we have not created a multicast group yet, we cannot create an IPMC
  // entry.
  const int kMulticastGroupId = 7;
  ASSERT_OK_AND_ASSIGN(const auto ipv4_address,
                       GetIpv4AddressForReplica(kMulticastGroupId));

  ASSERT_OK_AND_ASSIGN(const auto entities_v4,
                       CreateIpv4MulticastTableEntities(
                           ir_p4info_, std::string(kDefaultMulticastVrf),
                           ipv4_address, kMulticastGroupId));

  EXPECT_THAT(
      pdpi::InstallPiEntities(sut_p4rt_session_.get(), ir_p4info_, entities_v4),
      StatusIs(
          absl::StatusCode::kUnknown,
          AllOf(HasSubstr("#1: NOT_FOUND"),
                HasSubstr("[OrchAgent] No multicast group ID found for"))));
  // Clean up.
  EXPECT_OK(ClearEntities(*sut_p4rt_session_, ir_p4info_, vrf_entities));
}

TEST_P(L3MulticastTestFixture, DeleteNonexistentRifEntryFails) {
  // Unable to delete RIF entry that was not added.
  ASSERT_OK_AND_ASSIGN(
      const auto entities,
      CreateRifTableEntities(ir_p4info_, /*port_id=*/"1", kDefaultInstance,
                             kOriginalSrcMacAddress));

  EXPECT_THAT(ClearEntities(*sut_p4rt_session_, ir_p4info_, entities),
              StatusIs(absl::StatusCode::kUnknown,
                       AllOf(HasSubstr("#1: NOT_FOUND"),
                             HasSubstr("given key does not exist in table "
                                       "'multicast_router_interface_table'"))));
}

TEST_P(L3MulticastTestFixture, DeleteNonexistentMulticastGroupFails) {
  const int kNumberRifs = 2;
  ASSERT_OK_AND_ASSIGN(
      const auto sut_ports_ids,
      GetNUpInterfaceIDs(GetParam().mirror_testbed->GetMirrorTestbed().Sut(),
                         kNumberRifs));
  std::vector<ReplicaPair> replicas;
  for (int r = 0; r < kNumberRifs; ++r) {
    const std::string& port_id = sut_ports_ids.at(r);
    replicas.push_back({port_id, kDefaultInstance});
  }
  // Unable to delete multicast group entry that was not added.
  ASSERT_OK_AND_ASSIGN(
      const auto entities,
      CreateMulticastGroupEntities(ir_p4info_,
                                   /*multicast_group_id=*/1, replicas));
  EXPECT_THAT(
      ClearEntities(*sut_p4rt_session_, ir_p4info_, entities),
      StatusIs(
          absl::StatusCode::kUnknown,
          AllOf(
              HasSubstr("#1: NOT_FOUND"),
              HasSubstr(
                  "entry with key of multicast group ID '1' does not exist"))));
}

TEST_P(L3MulticastTestFixture, DeleteNonexistentIpmcEntryFails) {
  // Unable to delete IPMC entry that was not added.
  const int kMulticastGroupId = 1;
  const std::string vrf_id = "vrf-mcast-1";
  ASSERT_OK_AND_ASSIGN(const auto ipv4_address,
                       GetIpv4AddressForReplica(kMulticastGroupId));
  ASSERT_OK_AND_ASSIGN(const auto ipv6_address,
                       GetIpv6AddressForReplica(kMulticastGroupId));

  ASSERT_OK_AND_ASSIGN(
      const auto entities_v4,
      CreateIpv4MulticastTableEntities(ir_p4info_, vrf_id, ipv4_address,
                                       kMulticastGroupId));
  ASSERT_OK_AND_ASSIGN(
      const auto entities_v6,
      CreateIpv6MulticastTableEntities(ir_p4info_, vrf_id, ipv6_address,
                                       kMulticastGroupId));

  EXPECT_THAT(ClearEntities(*sut_p4rt_session_, ir_p4info_, entities_v4),
              StatusIs(absl::StatusCode::kUnknown,
                       AllOf(HasSubstr("#1: NOT_FOUND"),
                             HasSubstr("given key does not exist in table "
                                       "'ipv4_multicast_table'"))));
  EXPECT_THAT(ClearEntities(*sut_p4rt_session_, ir_p4info_, entities_v6),
              StatusIs(absl::StatusCode::kUnknown,
                       AllOf(HasSubstr("#1: NOT_FOUND"),
                             HasSubstr("given key does not exist in table "
                                       "'ipv6_multicast_table'"))));
}

TEST_P(L3MulticastTestFixture, BasicReplicationProgramming) {
  thinkit::MirrorTestbed& testbed =
      GetParam().mirror_testbed->GetMirrorTestbed();
  const int kNumberMulticastGroupsInTest = 1;
  const int kPortsToUseInTest = 2;
  // Collect port IDs.
  // Get SUT and control ports to test on.
  ASSERT_OK_AND_ASSIGN(
      const std::vector<std::string> sut_ports_ids,
      GetNUpInterfaceIDs(GetParam().mirror_testbed->GetMirrorTestbed().Sut(),
                         kPortsToUseInTest + 1));
  // --------------------------------------------------------------------------
  // Add multicast programming.
  // --------------------------------------------------------------------------
  LOG(INFO) << "Adding multicast programming.";
  std::vector<p4::v1::Entity> entities_created;
  ASSERT_OK(SetupDefaultMulticastProgramming(
      *sut_p4rt_session_, ir_p4info_, p4::v1::Update::INSERT,
      kNumberMulticastGroupsInTest, /*replicas_per_group=*/kPortsToUseInTest,
      sut_ports_ids, IpmcGroupAssignmentMechanism::kIpMulticastTable,
      entities_created));
  LOG(INFO) << "Added " << entities_created.size() << " entities.";
  // Build test packets.
  ASSERT_OK_AND_ASSIGN(
      auto vectors,
      BuildTestVectors(sut_ports_ids, kNumberMulticastGroupsInTest,
                       /*replicas_per_group=*/kPortsToUseInTest,
                       /*expect_output_packets=*/true));
  // Send test packets.
  LOG(INFO) << "Sending traffic to verify added multicast programming.";
  dvaas::DataplaneValidationParams dvaas_params =
      dvaas::DefaultpinsDataplaneValidationParams();
  dvaas_params.packet_test_vector_override = vectors;

  ASSERT_OK_AND_ASSIGN(
      dvaas::ValidationResult validation_result,
      GetParam().dvaas->ValidateDataplane(testbed, dvaas_params));
  // Validate traffic.
  validation_result.LogStatistics();
  EXPECT_OK(validation_result.HasSuccessRateOfAtLeast(1.0));
  // --------------------------------------------------------------------------
  // Modify multicast programming.
  // --------------------------------------------------------------------------
  // Send traffic to confirm replicas received.
  // --------------------------------------------------------------------------
  // Delete multicast programming.
  // --------------------------------------------------------------------------
  // LOG(INFO) << "Deleting multicast programming.";
  // Delete operations in the reverse order they were programmed.
  // std::reverse(entities_created.begin(), entities_created.end());
  // EXPECT_OK(ClearEntities(*sut_p4rt_session_, ir_p4info_,
  // entities_created));
  // LOG(INFO) << "Deleted " << entities_created.size() << " entities.";
  // Send traffic and expect no packets received.
  // ASSERT_OK_AND_ASSIGN(
  //    auto vectors_del,
  //    BuildTestVectors(sut_ports_ids, kNumberMulticastGroupsInTest,
  //                            /*replicas_per_group=*/kPortsToUseInTest,
  //                            /*expect_output_packets=*/false));
  // Send test packets.
  // LOG(INFO) << "Sending traffic to verify deleted multicast programming.";
  // dvaas::DataplaneValidationParams dvaas_params_del =
  //    dvaas::DefaultpinsDataplaneValidationParams();
  // dvaas_params_del.packet_test_vector_override = vectors_del;
  // ASSERT_OK_AND_ASSIGN(
  //     dvaas::ValidationResult validation_result_del,
  //    GetParam().dvaas->ValidateDataplane(testbed, dvaas_params_del));
  // Validate traffic.
  // validation_result_del.LogStatistics();
  // EXPECT_OK(validation_result_del.HasSuccessRateOfAtLeast(1.0));
}

TEST_P(L3MulticastTestFixture, BasicReplicationProgrammingWithAclRedirect) {

  if (!pins::TableHasMatchField(
          ir_p4info_, "acl_ingress_mirror_and_redirect_table", "in_port")) {
    GTEST_SKIP()
        << "Skipping because match field 'in_port' is not available in table "
        << "'acl_ingress_mirror_and_redirect_table'";
  }

  thinkit::MirrorTestbed& testbed =
      GetParam().mirror_testbed->GetMirrorTestbed();
  constexpr int kNumberMulticastGroupsInTest = 1;
  constexpr int kPortsToUseInTest = 2;

  // Get set of ports on the SUT and control switch to test on.
  ASSERT_OK_AND_ASSIGN(
      const std::vector<std::string> sut_ports_ids,
      GetNUpInterfaceIDs(GetParam().mirror_testbed->GetMirrorTestbed().Sut(),
                         kPortsToUseInTest + 1));

  std::vector<p4::v1::Entity> entities_created;
  ASSERT_OK(SetupDefaultMulticastProgramming(
      *sut_p4rt_session_, ir_p4info_, p4::v1::Update::INSERT,
      kNumberMulticastGroupsInTest, /*replicas_per_group=*/kPortsToUseInTest,
      sut_ports_ids, IpmcGroupAssignmentMechanism::kAclRedirect,
      entities_created));
  LOG(INFO) << "Added " << entities_created.size() << " entities.";

  // Build test packets.
  ASSERT_OK_AND_ASSIGN(
      auto vectors,
      BuildTestVectors(sut_ports_ids, kNumberMulticastGroupsInTest,
                       /*replicas_per_group=*/kPortsToUseInTest,
                       /*expect_output_packets=*/true));

  // Send test packets.
  LOG(INFO) << "Sending traffic to verify added multicast programming.";
  dvaas::DataplaneValidationParams dvaas_params =
      dvaas::DefaultPinsDataplaneValidationParams();
  // Ensure the port map for the control switch can map to the SUT (for
  // situations where the config differs for SUT and control switch).
  auto interface_to_peer_entity_map = gtl::ValueOrDie(
      pins::ControlP4rtPortIdBySutP4rtPortIdFromSwitchConfig());
  dvaas_params.mirror_testbed_port_map_override = gtl::ValueOrDie(
      dvaas::MirrorTestbedP4rtPortIdMap::CreateFromControlSwitchToSutPortMap(
          interface_to_peer_entity_map));
  dvaas_params.packet_test_vector_override = vectors;

  ASSERT_OK_AND_ASSIGN(
      dvaas::ValidationResult validation_result,
      GetParam().dvaas->ValidateDataplane(testbed, dvaas_params));
  // Validate traffic.
  validation_result.LogStatistics();
  EXPECT_OK(validation_result.HasSuccessRateOfAtLeast(1.0));
}

TEST_P(L3MulticastTestFixture, ConfirmFixedDelayProgramming) {
  if (!pins::TableHasMatchField(ir_p4info_, "acl_egress_l2_table",
                                 "src_mac")) {
    GTEST_SKIP()
        << "Skipping because match field 'src_mac' is not available in table "
        << "'acl_egress_l2_table'";
  }

  thinkit::MirrorTestbed& testbed =
      GetParam().mirror_testbed->GetMirrorTestbed();
  constexpr int kNumberMulticastGroupsInTest = 1;
  // We'll use 4 "drop" replicas and 2 expected replications.
  constexpr int kPortsToUseInTest = 6;

  // Get set of ports on the SUT and control switch to test on.
  ASSERT_OK_AND_ASSIGN(
      const std::vector<std::string> sut_ports_ids,
      GetNUpInterfaceIDs(GetParam().mirror_testbed->GetMirrorTestbed().Sut(),
                         kPortsToUseInTest + 1));

  // Setup 6 RIFs, 2 with valid source MAC addresses and 4 with the drop MAC
  // address.
  std::vector<p4::v1::Entity> entities_created;
  ASSERT_OK(SetupDefaultMulticastProgramming(
      *sut_p4rt_session_, ir_p4info_, p4::v1::Update::INSERT,
      kNumberMulticastGroupsInTest, /*replicas_per_group=*/kPortsToUseInTest,
      sut_ports_ids, IpmcGroupAssignmentMechanism::kIpMulticastTable,
      entities_created));
  LOG(INFO) << "Added " << entities_created.size() << " entities.";

  // Add the 4 drop RIFs using the first 4 ports for replication.
  constexpr int kDropInstance = 33;
  for (int port_index = 1; port_index <= 4; ++port_index) {
    ASSERT_OK_AND_ASSIGN(
        auto rif_entities,
        CreateRifTableEntities(ir_p4info_, sut_ports_ids[port_index],
                               kDropInstance, kDropSrcMacAddress));
    ASSERT_OK(pdpi::InstallPiEntities(sut_p4rt_session_.get(), ir_p4info_,
                                      rif_entities));
  }

  // Create the Egress ACL entry to drop relevant Ethernet source MAC.
  // Replicas to be dropped will rewrite their source MAC address to be the
  // "drop" MAC address.
  ASSERT_OK_AND_ASSIGN(auto proto_entry,
                       gutil::ParseTextProto<pdpi::IrTableEntry>(gutil::ParseTextProto<pdpi::IrTableEntry>(
                           R"pb(table_name: "acl_egress_l2_table"
                                priority: 1
                                matches {
                                  name: "src_mac"
                                  ternary {
                                    value { mac: "02:2a:10:00:00:02" }
                                    mask { mac: "ff:ff:ff:ff:ff:ff" }
                                  }
                                }
                                action { name: "acl_drop" }
                           )pb"));

  EXPECT_OK(pdpi::InstallIrTableEntry(*sut_p4rt_session_.get(), proto_entry));

  // Override default programming to have first 4 replicas be dropped.
  std::vector<ReplicaPair> replicas;
  replicas.push_back({sut_ports_ids[1], kDropInstance});
  replicas.push_back({sut_ports_ids[2], kDropInstance});
  replicas.push_back({sut_ports_ids[3], kDropInstance});
  replicas.push_back({sut_ports_ids[4], kDropInstance});
  // The last two replicas are unchanged.   We expect these replicas to emerge.
  replicas.push_back({sut_ports_ids[5], /*.instance=*/4});
  replicas.push_back({sut_ports_ids[6], /*.instance=*/5});
  ASSERT_OK_AND_ASSIGN(auto update_multicast_group_entities,
                       CreateMulticastGroupEntities(
                           ir_p4info_, /*multicast_group_id=*/1, replicas));
  ASSERT_OK(
      pdpi::SendPiUpdates(sut_p4rt_session_.get(),
                          pdpi::CreatePiUpdates(update_multicast_group_entities,
                                                p4::v1::Update::MODIFY)));

  // Send traffic and confirm only 2 replicas received (instead of 6).
  // 4 of the "prefix" replicas should have been dropped.
  ASSERT_OK_AND_ASSIGN(
      auto update_vectors,
      BuildInputOutputVectors(sut_ports_ids,
                              /*input_group_index=*/0,
                              /*output_group_index=*/0,
                              /*replicas_per_group=*/kPortsToUseInTest,
                              /*output_replica_start_index=*/4));
  LOG(INFO) << "Sending traffic to verify added multicast programming.";
  dvaas::DataplaneValidationParams dvaas_params =
      dvaas::DefaultpinsDataplaneValidationParams();
  // Ensure the port map for the control switch can map to the SUT (for
  // situations where the config differs for SUT and control switch).
  auto interface_to_peer_entity_map = gtl::ValueOrDie(
      pins::ControlP4rtPortIdBySutP4rtPortIdFromSwitchConfig());
  dvaas_params.mirror_testbed_port_map_override = gtl::ValueOrDie(
      dvaas::MirrorTestbedP4rtPortIdMap::CreateFromControlSwitchToSutPortMap(
          interface_to_peer_entity_map));
  dvaas_params.packet_test_vector_override = update_vectors;

  ASSERT_OK_AND_ASSIGN(
      dvaas::ValidationResult update_validation_result,
      GetParam().dvaas->ValidateDataplane(testbed, dvaas_params));
  // Validate traffic.
  update_validation_result.LogStatistics();
  EXPECT_OK(update_validation_result.HasSuccessRateOfAtLeast(1.0));
}

// This test confirms replicating N times to the same port (using different
// replica instances) will produce N output packets.
TEST_P(L3MulticastTestFixture, ReplicatingNTimesToSamePortProducesNCopies) {

  thinkit::MirrorTestbed& testbed =
      GetParam().mirror_testbed->GetMirrorTestbed();
  constexpr int kNumberMulticastGroupsInTest = 1;
  constexpr int kOutputPortsToUseInTest = 1;
  constexpr int kInitialReplicasPerGroup = 1;

  // Get set of ports on the SUT and control switch to test on.
  ASSERT_OK_AND_ASSIGN(
      const std::vector<std::string> sut_ports_ids,
      GetNUpInterfaceIDs(GetParam().mirror_testbed->GetMirrorTestbed().Sut(),
                         kOutputPortsToUseInTest + 1));

  // Setup 3 RIFs, all on same port but that use different instances.
  // We will expect that the multicast group will produce three copies.
  // Setup default programming assuming only 1 replica to start, since default
  // programming wants to output on different ports.
  std::vector<p4::v1::Entity> entities_created;
  ASSERT_OK(SetupDefaultMulticastProgramming(
      *sut_p4rt_session_, ir_p4info_, p4::v1::Update::INSERT,
      kNumberMulticastGroupsInTest,
      /*replicas_per_group=*/kInitialReplicasPerGroup, sut_ports_ids,
      IpmcGroupAssignmentMechanism::kIpMulticastTable, entities_created));
  LOG(INFO) << "Added " << entities_created.size() << " entities.";

  // Add additional active RIF that will replicate to the same port.
  ASSERT_OK_AND_ASSIGN(
      const netaddr::MacAddress kExtraSrcMac,
      GetSrcMacForReplica(/*multicast_group_index=*/0, kInitialReplicasPerGroup,
                          /*replicas_number=*/1));
  constexpr int kExtraInstance = 1;
  constexpr int kExtraInstanceTwo = 2;
  ASSERT_OK_AND_ASSIGN(auto rif_entities,
                       CreateRifTableEntities(ir_p4info_, sut_ports_ids[1],
                                              kExtraInstance, kExtraSrcMac));
  // Create another RIF with different instance but same src MAC.
  ASSERT_OK_AND_ASSIGN(auto rif_entities2,
                       CreateRifTableEntities(ir_p4info_, sut_ports_ids[1],
                                              kExtraInstanceTwo, kExtraSrcMac));
  ASSERT_OK(pdpi::InstallPiEntities(sut_p4rt_session_.get(), ir_p4info_,
                                    rif_entities));
  ASSERT_OK(pdpi::InstallPiEntities(sut_p4rt_session_.get(), ir_p4info_,
                                    rif_entities2));

  // Update multicast group entity to include new replicas.
  std::vector<ReplicaPair> replicas;
  replicas.push_back({sut_ports_ids[1], /*.instance=*/0});    // unchanged
  replicas.push_back({sut_ports_ids[1], kExtraInstance});     // added
  replicas.push_back({sut_ports_ids[1], kExtraInstanceTwo});  // added
  ASSERT_OK_AND_ASSIGN(auto update_multicast_group_entities,
                       CreateMulticastGroupEntities(
                           ir_p4info_, /*multicast_group_id=*/1, replicas));
  ASSERT_OK(
      pdpi::SendPiUpdates(sut_p4rt_session_.get(),
                          pdpi::CreatePiUpdates(update_multicast_group_entities,
                                                p4::v1::Update::MODIFY)));

  // Build custom test packets.
  std::vector<dvaas::PacketTestVector> expectations;

  // All packets will be injected on the same port.
  const std::string& in_port = sut_ports_ids[0];
  int unique_payload_ids = 1;

  // We will inject an IPv4 packet that will activate the multicast group.
  ASSERT_OK_AND_ASSIGN(const auto input_ipv4_address,
                       GetIpv4AddressForReplica(/*multicast_group_index=*/0));
  ProtoFixtureRepository repo;
  repo.RegisterValue("@ingress_port", in_port)
      .RegisterValue("@egress_src_mac", kOriginalSrcMacAddress.ToString())
      .RegisterValue("@ttl", "0x40")
      .RegisterValue("@hop_limit", "0x50")
      .RegisterValue("@decremented_hop_limit", "0x4f")
      .RegisterValue("@decremented_ttl", "0x3f")
      .RegisterValue("@ipv4_dst", input_ipv4_address.ToString())
      .RegisterValue("@payload_ipv4", dvaas::MakeTestPacketPayloadFromUniqueId(
                                          unique_payload_ids++));

  // Build headers.
  repo.RegisterSnippetOrDie<packetlib::Header>("@ethernet_ipv4", R"pb(
        ethernet_header {
          ethernet_destination: "01:00:5e:01:01:01"
          ethernet_source: @egress_src_mac
          ethertype: "0x0800"  # IPv4
        }
      )pb")
      .RegisterSnippetOrDie<packetlib::Header>("@ipv4", R"pb(
        ipv4_header {
          version: "0x4"
          ihl: "0x5"
          dscp: "0x00"
          ecn: "0x0"
          # total_length: filled in automatically.
          identification: "0x0000"
          flags: "0x0"
          fragment_offset: "0x0000"
          ttl: @ttl
          protocol: "0x11"
          # checksum: filled in automatically
          ipv4_source: "128.252.7.36"
          ipv4_destination: @ipv4_dst
        }
      )pb")
      .RegisterSnippetOrDie<packetlib::Header>("@udp", R"pb(
        udp_header {
          source_port: "0x0567"       # 1383
          destination_port: "0x1234"  # 4660
          # length: filled in automatically
          # checksum: filled in automatically
        }
      )pb")
      .RegisterMessage("@input_packet_ipv4",
                       ParsePacketAndPadToMinimumSize(repo,
                                                      R"pb(
                                                        headers: @ethernet_ipv4
                                                        headers: @ipv4
                                                        headers: @udp
                                                        payload: @payload_ipv4
                                                      )pb"));

  // Build up acceptable_outputs string, to account for each replica.
  dvaas::SwitchOutput expected_ipv4_output;
  ASSERT_OK_AND_ASSIGN(
      netaddr::MacAddress src_mac_replica0,
      GetSrcMacForReplica(/*multicast_group_index=*/0,
                          /*replicas_per_group=*/kInitialReplicasPerGroup,
                          /*replicas_number=*/0));
  ASSERT_OK_AND_ASSIGN(
      netaddr::MacAddress src_mac_replica1,
      GetSrcMacForReplica(/*multicast_group_index=*/0,
                          /*replicas_per_group=*/kInitialReplicasPerGroup,
                          /*replicas_number=*/1));

  // IPv4
  *expected_ipv4_output.add_packets() =
      repo.RegisterValue("@egress_port", sut_ports_ids[1])
          .RegisterValue("@egress_src_mac", src_mac_replica0.ToString())
          .RegisterMessage(
              "@output_packet", ParsePacketAndPadToMinimumSize(repo, R"pb(
                headers: @ethernet_ipv4 {
                  ethernet_header { ethernet_source: @egress_src_mac }
                }
                headers: @ipv4 { ipv4_header { ttl: @decremented_ttl } }
                headers: @udp
                payload: @payload_ipv4
              )pb"))
          .ParseTextOrDie<dvaas::Packet>(R"pb(
            port: @egress_port
            parsed: @output_packet
          )pb");
  *expected_ipv4_output.add_packets() =
      repo.RegisterValue("@egress_port", sut_ports_ids[1])
          .RegisterValue("@egress_src_mac", src_mac_replica1.ToString())
          .RegisterMessage(
              "@output_packet", ParsePacketAndPadToMinimumSize(repo, R"pb(
                headers: @ethernet_ipv4 {
                  ethernet_header { ethernet_source: @egress_src_mac }
                }
                headers: @ipv4 { ipv4_header { ttl: @decremented_ttl } }
                headers: @udp
                payload: @payload_ipv4
              )pb"))
          .ParseTextOrDie<dvaas::Packet>(R"pb(
            port: @egress_port
            parsed: @output_packet
          )pb");
  // Expect another packet with same source MAC.
  *expected_ipv4_output.add_packets() =
      repo.RegisterValue("@egress_port", sut_ports_ids[1])
          .RegisterValue("@egress_src_mac", src_mac_replica1.ToString())
          .RegisterMessage(
              "@output_packet", ParsePacketAndPadToMinimumSize(repo, R"pb(
                headers: @ethernet_ipv4 {
                  ethernet_header { ethernet_source: @egress_src_mac }
                }
                headers: @ipv4 { ipv4_header { ttl: @decremented_ttl } }
                headers: @udp
                payload: @payload_ipv4
              )pb"))
          .ParseTextOrDie<dvaas::Packet>(R"pb(
            port: @egress_port
            parsed: @output_packet
          )pb");
  LOG(INFO) << "Packets will be sent on port " << in_port;

  expectations.emplace_back() =
      repo.RegisterMessage("@expected_ipv4_output", expected_ipv4_output)
          .ParseTextOrDie<dvaas::PacketTestVector>(R"pb(
            input {
              type: DATAPLANE
              packet { port: @ingress_port parsed: @input_packet_ipv4 }
            }
            acceptable_outputs: @expected_ipv4_output
          )pb");

  LOG(INFO) << "Sending traffic to verify added multicast programming.";
  dvaas::DataplaneValidationParams dvaas_params =
      dvaas::DefaultpinsDataplaneValidationParams();
  // Ensure the port map for the control switch can map to the SUT (for
  // situations where the config differs for SUT and control switch).
  ASSERT_OK_AND_ASSIGN(
      auto interface_to_peer_entity_map,
      pins::ControlP4rtPortIdBySutP4rtPortIdFromSwitchConfig());
  ASSERT_OK_AND_ASSIGN(
      dvaas_params.mirror_testbed_port_map_override,
      dvaas::MirrorTestbedP4rtPortIdMap::CreateFromControlSwitchToSutPortMap(
          interface_to_peer_entity_map));
  dvaas_params.packet_test_vector_override = expectations;

  ASSERT_OK_AND_ASSIGN(
      dvaas::ValidationResult validation_result,
      GetParam().dvaas->ValidateDataplane(testbed, dvaas_params));
  // Validate traffic.
  validation_result.LogStatistics();
  EXPECT_OK(validation_result.HasSuccessRateOfAtLeast(1.0));
}

TEST_P(L3MulticastTestFixture, ConfirmAclRedirectOverridesIpMulticastTable) {
  if (!pins::TableHasMatchField(
          ir_p4info_, "acl_ingress_mirror_and_redirect_table", "in_port")) {
    GTEST_SKIP()
        << "Skipping because match field 'in_port' is not available in table "
        << "'acl_ingress_mirror_and_redirect_table'";
  }

  // Setup two multicast groups, one assigned via the IPMC table and one via
  // ACL redirect.  Have both paths match.  Expect the ACL redirect to win.

  thinkit::MirrorTestbed& testbed =
      GetParam().mirror_testbed->GetMirrorTestbed();
  constexpr int kNumberMulticastGroupsInTest = 2;
  constexpr int kPortsToUseInTest = 2;

  // Get set of ports on the SUT and control switch to test on.
  ASSERT_OK_AND_ASSIGN(
      const std::vector<std::string> sut_ports_ids,
      GetNUpInterfaceIDs(GetParam().mirror_testbed->GetMirrorTestbed().Sut(),
                         kPortsToUseInTest + 1));

  std::vector<p4::v1::Entity> entities_created;
  ASSERT_OK(SetupDefaultMulticastProgramming(
      *sut_p4rt_session_, ir_p4info_, p4::v1::Update::INSERT,
      kNumberMulticastGroupsInTest, /*replicas_per_group=*/kPortsToUseInTest,
      sut_ports_ids, IpmcGroupAssignmentMechanism::kIpMulticastTable,
      entities_created));

  // Setup the ACL redirect path to use multicast group 2.
  constexpr int kMulticastGroup2 = 2;
  const std::string& input_port_id = sut_ports_ids[0];
  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::Entity> acl_entities,
      sai::EntryBuilder()
          // .AddIngressAclEntryRedirectingToMulticastGroup(
          //     kMulticastGroup2,
          //     {.in_port = input_port_id, .ipmc_table_hit = false})
          .AddIngressAclEntryRedirectingToMulticastGroup(
              kMulticastGroup2,
              {.in_port = input_port_id, .ipmc_table_hit = true})
          .LogPdEntries()
          .GetDedupedPiEntities(ir_p4info_));
  ASSERT_OK(pdpi::InstallPiEntities(sut_p4rt_session_.get(), ir_p4info_,
                                    acl_entities));
  entities_created.insert(entities_created.end(), acl_entities.begin(),
                          acl_entities.end());
  LOG(INFO) << "Added " << entities_created.size() << " entities.";

  // Inject test packets that would match the IP multicast table that would
  // assign to multicast group 1.  However, expect the ACL redirect path to
  // override the IPMC table assignment such that multicast group 2 will be
  // the outputs.
  ASSERT_OK_AND_ASSIGN(
      auto vectors,
      BuildInputOutputVectors(sut_ports_ids, /*input_group_index=*/0,
                              /*output_group_index=*/1,
                              /*replicas_per_group=*/kPortsToUseInTest));

  // Send test packets.
  LOG(INFO) << "Sending traffic to verify added multicast programming.";
  dvaas::DataplaneValidationParams dvaas_params =
      dvaas::DefaultpinsDataplaneValidationParams();
  // Ensure the port map for the control switch can map to the SUT (for
  // situations where the config differs for SUT and control switch).
  auto interface_to_peer_entity_map = gtl::ValueOrDie(
      pins::ControlP4rtPortIdBySutP4rtPortIdFromSwitchConfig());
  dvaas_params.mirror_testbed_port_map_override = gtl::ValueOrDie(
      dvaas::MirrorTestbedP4rtPortIdMap::CreateFromControlSwitchToSutPortMap(
          interface_to_peer_entity_map));
  dvaas_params.packet_test_vector_override = vectors;

  ASSERT_OK_AND_ASSIGN(
      dvaas::ValidationResult validation_result,
      GetParam().dvaas->ValidateDataplane(testbed, dvaas_params));
  // Validate traffic.
  validation_result.LogStatistics();
  EXPECT_OK(validation_result.HasSuccessRateOfAtLeast(1.0));
}

TEST_P(L3MulticastTestFixture, AddMulticastRifForUnknownPortFails) {
  // Unable to add an entry if the port does not exist.
  const std::string kUnknownPortId = "20000";
  ASSERT_OK_AND_ASSIGN(
      const auto entities,
      CreateRifTableEntities(ir_p4info_, kUnknownPortId, kDefaultInstance,
                             kOriginalSrcMacAddress));

  EXPECT_THAT(InstallPiEntities(sut_p4rt_session_.get(), ir_p4info_, entities),
              StatusIs(absl::StatusCode::kUnknown,
                       AllOf(HasSubstr("#1: INVALID_ARGUMENT"),
                             HasSubstr("[P4RT App] Cannot translate port "))));
}

TEST_P(L3MulticastTestFixture, AddMulticastReplicaForUnknownPortInstanceFails) {

  const int kPortsToUseInTest = 2;
  ASSERT_OK_AND_ASSIGN(
      const auto sut_ports_ids,
      GetNUpInterfaceIDs(GetParam().mirror_testbed->GetMirrorTestbed().Sut(),
                         kPortsToUseInTest));

  ASSERT_OK_AND_ASSIGN(
      const auto rif_entities,
      CreateRifTableEntities(ir_p4info_, sut_ports_ids.at(0), kDefaultInstance,
                             kOriginalSrcMacAddress));
  // Purposefully do not create a RIF for the second port ID.
  EXPECT_OK(pdpi::InstallPiEntities(sut_p4rt_session_.get(), ir_p4info_,
                                    rif_entities));

  std::vector<ReplicaPair> replicas;
  for (int r = 0; r < kPortsToUseInTest; ++r) {
    const std::string& port_id = sut_ports_ids.at(r);
    replicas.push_back({port_id, kDefaultInstance});
  }
  const int kMulticastGroupId = 1;
  ASSERT_OK_AND_ASSIGN(
      const auto mc_entities,
      CreateMulticastGroupEntities(ir_p4info_, kMulticastGroupId, replicas));

  EXPECT_THAT(
      pdpi::InstallPiEntities(sut_p4rt_session_.get(), ir_p4info_, mc_entities),
      StatusIs(absl::StatusCode::kUnknown,
               AllOf(HasSubstr("#1: NOT_FOUND"),
                     HasSubstr("[OrchAgent] No corresponding "
                               "FIXED_MULTICAST_ROUTER_INTERFACE_TABLE"),
                     HasSubstr("entry found for multicast group"))));

  // Clean up.
  EXPECT_OK(ClearEntities(*sut_p4rt_session_, ir_p4info_, rif_entities));
}

TEST_P(L3MulticastTestFixture, AddIpmcEntryForUnknownMulticastGroupFails) {
  const int kPortsToUseInTest = 2;
  ASSERT_OK_AND_ASSIGN(
      const auto sut_ports_ids,
      GetNUpInterfaceIDs(GetParam().mirror_testbed->GetMirrorTestbed().Sut(),
                         kPortsToUseInTest));

  std::vector<p4::v1::Entity> rif_entities;
  for (int r = 0; r < kPortsToUseInTest; ++r) {
    ASSERT_OK_AND_ASSIGN(
        const auto rifs,
        CreateRifTableEntities(ir_p4info_, sut_ports_ids.at(r),
                               kDefaultInstance, kOriginalSrcMacAddress));
    rif_entities.insert(rif_entities.end(), rifs.begin(), rifs.end());
  }
  EXPECT_OK(pdpi::InstallPiEntities(sut_p4rt_session_.get(), ir_p4info_,
                                    rif_entities));

  std::vector<ReplicaPair> replicas;
  for (int r = 0; r < kPortsToUseInTest; ++r) {
    const std::string& port_id = sut_ports_ids.at(r);
    replicas.push_back({port_id, kDefaultInstance});
  }
  const int kMulticastGroupId = 1;
  ASSERT_OK_AND_ASSIGN(
      const auto mc_entities,
      CreateMulticastGroupEntities(ir_p4info_, kMulticastGroupId, replicas));
  EXPECT_OK(pdpi::InstallPiEntities(sut_p4rt_session_.get(), ir_p4info_,
                                    mc_entities));

  // Create default VRF.
  ASSERT_OK_AND_ASSIGN(const std::vector<p4::v1::Entity> vrf_entities,
                       sai::EntryBuilder()
                           .AddVrfEntry(kDefaultMulticastVrf)
                           .LogPdEntries()
                           .GetDedupedPiEntities(ir_p4info_));
  EXPECT_OK(pdpi::InstallPiEntities(sut_p4rt_session_.get(), ir_p4info_,
                                    vrf_entities));

  // Create IPMC entry for invalid multicast group.
  const int kInvalidMulticastGroupId = 2;
  ASSERT_OK_AND_ASSIGN(const netaddr::Ipv4Address ipv4_address,
                       GetIpv4AddressForReplica(kInvalidMulticastGroupId));
  std::string vrf_id = std::string(kDefaultMulticastVrf);
  ASSERT_OK_AND_ASSIGN(auto ipmc_entities, CreateIpv4MulticastTableEntities(
                                               ir_p4info_, vrf_id, ipv4_address,
                                               kInvalidMulticastGroupId));

  EXPECT_THAT(
      pdpi::InstallPiEntities(sut_p4rt_session_.get(), ir_p4info_,
                              ipmc_entities),
      StatusIs(
          absl::StatusCode::kUnknown,
          AllOf(HasSubstr("#1: NOT_FOUND"),
                HasSubstr("[OrchAgent] No multicast group ID found for"))));

  // Clean up.
  EXPECT_OK(ClearEntities(*sut_p4rt_session_, ir_p4info_, vrf_entities));
  EXPECT_OK(ClearEntities(*sut_p4rt_session_, ir_p4info_, mc_entities));
  EXPECT_OK(ClearEntities(*sut_p4rt_session_, ir_p4info_, rif_entities));
}

TEST_P(L3MulticastTestFixture, AddIpmcEntryForUnknownVrfFails) {

  const int kPortsToUseInTest = 2;
  ASSERT_OK_AND_ASSIGN(
      const auto sut_ports_ids,
      GetNUpInterfaceIDs(GetParam().mirror_testbed->GetMirrorTestbed().Sut(),
                         kPortsToUseInTest));

  std::vector<p4::v1::Entity> rif_entities;
  for (int r = 0; r < kPortsToUseInTest; ++r) {
    ASSERT_OK_AND_ASSIGN(
        const auto rifs,
        CreateRifTableEntities(ir_p4info_, sut_ports_ids.at(r),
                               kDefaultInstance, kOriginalSrcMacAddress));
    rif_entities.insert(rif_entities.end(), rifs.begin(), rifs.end());
  }
  EXPECT_OK(pdpi::InstallPiEntities(sut_p4rt_session_.get(), ir_p4info_,
                                    rif_entities));

  std::vector<ReplicaPair> replicas;
  for (int r = 0; r < kPortsToUseInTest; ++r) {
    const std::string& port_id = sut_ports_ids.at(r);
    replicas.push_back({port_id, kDefaultInstance});
  }
  const int kMulticastGroupId = 1;
  ASSERT_OK_AND_ASSIGN(
      const auto mc_entities,
      CreateMulticastGroupEntities(ir_p4info_, kMulticastGroupId, replicas));
  EXPECT_OK(pdpi::InstallPiEntities(sut_p4rt_session_.get(), ir_p4info_,
                                    mc_entities));

  // Do not create a VRF.

  // Create IPMC entry pointint to unknown VRF.
  ASSERT_OK_AND_ASSIGN(const netaddr::Ipv4Address ipv4_address,
                       GetIpv4AddressForReplica(kMulticastGroupId));
  std::string vrf_id = std::string(kDefaultMulticastVrf);
  ASSERT_OK_AND_ASSIGN(
      const auto ipmc_entities,
      CreateIpv4MulticastTableEntities(ir_p4info_, vrf_id, ipv4_address,
                                       kMulticastGroupId));

  EXPECT_THAT(
      pdpi::InstallPiEntities(sut_p4rt_session_.get(), ir_p4info_,
                              ipmc_entities),
      StatusIs(absl::StatusCode::kUnknown,
               AllOf(HasSubstr("#1: NOT_FOUND"),
                     HasSubstr("[OrchAgent] No VRF found with name "))));

  // Clean up.
  EXPECT_OK(ClearEntities(*sut_p4rt_session_, ir_p4info_, mc_entities));
  EXPECT_OK(ClearEntities(*sut_p4rt_session_, ir_p4info_, rif_entities));
}

TEST_P(L3MulticastTestFixture, AddIpmcEntryWithInvalidIPv4AddressFails) {
  const int kPortsToUseInTest = 2;
  ASSERT_OK_AND_ASSIGN(
      const std::vector<std::string> sut_ports_ids,
      GetNUpInterfaceIDs(GetParam().mirror_testbed->GetMirrorTestbed().Sut(),
                         kPortsToUseInTest));

  std::vector<p4::v1::Entity> rif_entities;
  for (int r = 0; r < kPortsToUseInTest; ++r) {
    ASSERT_OK_AND_ASSIGN(
        const auto rifs,
        CreateRifTableEntities(ir_p4info_, sut_ports_ids[r], kDefaultInstance,
                               kOriginalSrcMacAddress));
    rif_entities.insert(rif_entities.end(), rifs.begin(), rifs.end());
  }
  EXPECT_OK(pdpi::InstallPiEntities(sut_p4rt_session_.get(), ir_p4info_,
                                    rif_entities));

  std::vector<ReplicaPair> replicas;
  for (int r = 0; r < kPortsToUseInTest; ++r) {
    const std::string& port_id = sut_ports_ids[r];
    replicas.push_back({port_id, kDefaultInstance});
  }
  const int kMulticastGroupId = 1;
  ASSERT_OK_AND_ASSIGN(
      const auto mc_entities,
      CreateMulticastGroupEntities(ir_p4info_, kMulticastGroupId, replicas));
  EXPECT_OK(pdpi::InstallPiEntities(sut_p4rt_session_.get(), ir_p4info_,
                                    mc_entities));

  // Create default VRF.
  ASSERT_OK_AND_ASSIGN(const std::vector<p4::v1::Entity> vrf_entities,
                       sai::EntryBuilder()
                           .AddVrfEntry(kDefaultMulticastVrf)
                           .LogPdEntries()
                           .GetDedupedPiEntities(ir_p4info_));
  EXPECT_OK(pdpi::InstallPiEntities(sut_p4rt_session_.get(), ir_p4info_,
                                    vrf_entities));

  // Create IPMC entry with invalid IPv4 address (not multicast range).
  const netaddr::Ipv4Address ipv4_address = netaddr::Ipv4Address(64, 10, 0, 1);
  std::string vrf_id = std::string(kDefaultMulticastVrf);
  ASSERT_OK_AND_ASSIGN(
      const auto ipmc_entities,
      CreateIpv4MulticastTableEntities(ir_p4info_, vrf_id, ipv4_address,
                                       kMulticastGroupId));

  EXPECT_THAT(pdpi::InstallPiEntities(sut_p4rt_session_.get(), ir_p4info_,
                                      ipmc_entities),
              StatusIs(absl::StatusCode::kUnknown,
                       AllOf(HasSubstr("#1: INVALID_ARGUMENT"),
                             HasSubstr("All entries must satisfy"))));

  // Clean up.
  EXPECT_OK(ClearEntities(*sut_p4rt_session_, ir_p4info_, vrf_entities));
  EXPECT_OK(ClearEntities(*sut_p4rt_session_, ir_p4info_, mc_entities));
  EXPECT_OK(ClearEntities(*sut_p4rt_session_, ir_p4info_, rif_entities));
}

TEST_P(L3MulticastTestFixture, DeleteRifWhileInUseFails) {
  // TODO: Reenable once change available in release image.
  GTEST_SKIP()
      << "Skipping until can reenable when stack change reaches release image";

  const int kPortsToUseInTest = 2;
  ASSERT_OK_AND_ASSIGN(
      const std::vector<std::string> sut_ports_ids,
      GetNUpInterfaceIDs(GetParam().mirror_testbed->GetMirrorTestbed().Sut(),
                         kPortsToUseInTest));

  std::vector<p4::v1::Entity> rif_entities;
  for (int r = 0; r < kPortsToUseInTest; ++r) {
    ASSERT_OK_AND_ASSIGN(
        const auto rifs,
        CreateRifTableEntities(ir_p4info_, sut_ports_ids[r], kDefaultInstance,
                               kOriginalSrcMacAddress));
    rif_entities.insert(rif_entities.end(), rifs.begin(), rifs.end());
  }
  EXPECT_OK(pdpi::InstallPiEntities(sut_p4rt_session_.get(), ir_p4info_,
                                    rif_entities));

  std::vector<ReplicaPair> replicas;
  for (int r = 0; r < kPortsToUseInTest; ++r) {
    const std::string& port_id = sut_ports_ids[r];
    replicas.push_back({port_id, kDefaultInstance});
  }
  const int kMulticastGroupId = 1;
  ASSERT_OK_AND_ASSIGN(
      const auto mc_entities,
      CreateMulticastGroupEntities(ir_p4info_, kMulticastGroupId, replicas));
  EXPECT_OK(pdpi::InstallPiEntities(sut_p4rt_session_.get(), ir_p4info_,
                                    mc_entities));

  // Attempting to delete a RIF entry while it is in use by a multicast group
  // causes an error.
  EXPECT_THAT(
      ClearEntities(*sut_p4rt_session_, ir_p4info_, rif_entities),
      StatusIs(absl::StatusCode::kUnknown,
               AllOf(HasSubstr("#1: INVALID_ARGUMENT"),
                     HasSubstr("[OrchAgent] RIF oid "),
                     HasSubstr("is still used by multicast group members"),
                     HasSubstr("#2: ABORTED"),
                     HasSubstr("[OrchAgent] SWSS_RC_NOT_EXECUTED"))));

  // Clean up.
  EXPECT_OK(ClearEntities(*sut_p4rt_session_, ir_p4info_, mc_entities));
  EXPECT_OK(ClearEntities(*sut_p4rt_session_, ir_p4info_, rif_entities));
}

TEST_P(L3MulticastTestFixture, DeleteMulticastGroupWhileInUseFails) {
  const int kPortsToUseInTest = 2;
  ASSERT_OK_AND_ASSIGN(
      const std::vector<std::string> sut_ports_ids,
      GetNUpInterfaceIDs(GetParam().mirror_testbed->GetMirrorTestbed().Sut(),
                         kPortsToUseInTest));

  std::vector<p4::v1::Entity> rif_entities;
  for (int r = 0; r < kPortsToUseInTest; ++r) {
    ASSERT_OK_AND_ASSIGN(
        const auto rifs,
        CreateRifTableEntities(ir_p4info_, sut_ports_ids[r], kDefaultInstance,
                               kOriginalSrcMacAddress));
    rif_entities.insert(rif_entities.end(), rifs.begin(), rifs.end());
  }
  EXPECT_OK(pdpi::InstallPiEntities(sut_p4rt_session_.get(), ir_p4info_,
                                    rif_entities));

  std::vector<ReplicaPair> replicas;
  for (int r = 0; r < kPortsToUseInTest; ++r) {
    const std::string& port_id = sut_ports_ids[r];
    replicas.push_back({port_id, kDefaultInstance});
  }
  const int kMulticastGroupId = 1;
  ASSERT_OK_AND_ASSIGN(
      const auto mc_entities,
      CreateMulticastGroupEntities(ir_p4info_, kMulticastGroupId, replicas));
  EXPECT_OK(pdpi::InstallPiEntities(sut_p4rt_session_.get(), ir_p4info_,
                                    mc_entities));

  // Create default VRF.
  ASSERT_OK_AND_ASSIGN(const std::vector<p4::v1::Entity> vrf_entities,
                       sai::EntryBuilder()
                           .AddVrfEntry(kDefaultMulticastVrf)
                           .LogPdEntries()
                           .GetDedupedPiEntities(ir_p4info_));
  EXPECT_OK(pdpi::InstallPiEntities(sut_p4rt_session_.get(), ir_p4info_,
                                    vrf_entities));

  ASSERT_OK_AND_ASSIGN(const netaddr::Ipv6Address ipv6_address,
                       GetIpv6AddressForReplica(kMulticastGroupId));
  std::string vrf_id = std::string(kDefaultMulticastVrf);
  ASSERT_OK_AND_ASSIGN(
      const auto ipmc_entities,
      CreateIpv6MulticastTableEntities(ir_p4info_, vrf_id, ipv6_address,
                                       kMulticastGroupId));
  EXPECT_OK(pdpi::InstallPiEntities(sut_p4rt_session_.get(), ir_p4info_,
                                    ipmc_entities));

  // Attempting to delete multicast group while in use results in an error.
  EXPECT_THAT(
      ClearEntities(*sut_p4rt_session_, ir_p4info_, mc_entities),
      StatusIs(absl::StatusCode::kUnknown,
               AllOf(HasSubstr("#1: INVALID_ARGUMENT"),
                     HasSubstr("[OrchAgent] Multicast group"),
                     HasSubstr("cannot be deleted because route entries"))));

  // Clean up.
  EXPECT_OK(ClearEntities(*sut_p4rt_session_, ir_p4info_, ipmc_entities));
  EXPECT_OK(ClearEntities(*sut_p4rt_session_, ir_p4info_, vrf_entities));
  EXPECT_OK(ClearEntities(*sut_p4rt_session_, ir_p4info_, mc_entities));
  EXPECT_OK(ClearEntities(*sut_p4rt_session_, ir_p4info_, rif_entities));
}

TEST_P(L3MulticastTestFixture, AbleToProgramExpectedMulticastRifCapacity) {

  constexpr int kPortsToUseInTest = 8;
  ASSERT_OK_AND_ASSIGN(
      const std::vector<std::string> sut_ports_ids,
      GetNUpInterfaceIDs(GetParam().mirror_testbed->GetMirrorTestbed().Sut(),
                         kPortsToUseInTest));

  std::vector<p4::v1::Entity> rif_entities;

  // Program RIFs one by one, in case we do not reach our intended limit.
  absl::Time start_time = absl::Now();
  for (int r = 0; r < kMaxRifs; ++r) {
    const std::string& port_id = sut_ports_ids[r % kPortsToUseInTest];
    ASSERT_OK_AND_ASSIGN(netaddr::MacAddress src_mac,
                         GetSrcMacForReplica(/*multicast_group_index=*/r,
                                             /*replicas_per_group=*/1,
                                             /*replicas_number=*/0));
    ASSERT_OK_AND_ASSIGN(
        auto rifs,
        CreateRifTableEntities(ir_p4info_, port_id,
                               /*instance=*/r / kPortsToUseInTest, src_mac));

    absl::Status add_status =
        pdpi::InstallPiEntities(sut_p4rt_session_.get(), ir_p4info_, rifs);
    ASSERT_OK(add_status)
        << "Unable to fill multicast_router_interface_table.  Failed on entity "
        << (rif_entities.size() + 1) << " of " << kMaxRifs;

    rif_entities.insert(rif_entities.end(), rifs.begin(), rifs.end());
  }
  LOG(INFO) << "Successfully programmed " << rif_entities.size()
            << " multicast_router_interface_table entities.";
  LOG(INFO) << "Total programming time: " << (absl::Now() - start_time);

  // Clean up.
  EXPECT_OK(ClearEntities(*sut_p4rt_session_, ir_p4info_, rif_entities));
}

TEST_P(L3MulticastTestFixture, AbleToProgramExpectedMulticastGroupCapacity) {

  constexpr int kPortsToUseInTest = 16;
  ASSERT_OK_AND_ASSIGN(
      const std::vector<std::string> sut_ports_ids,
      GetNUpInterfaceIDs(GetParam().mirror_testbed->GetMirrorTestbed().Sut(),
                         kPortsToUseInTest));

  // Setup RIFs and populate replicas.
  std::vector<ReplicaPair> replicas;
  sai::EntryBuilder rif_builder;
  for (int port_index = 0; port_index < kPortsToUseInTest; ++port_index) {
    const std::string& port_id = sut_ports_ids[port_index % kPortsToUseInTest];
    replicas.push_back({port_id, kDefaultInstance});
    ASSERT_OK_AND_ASSIGN(
        netaddr::MacAddress src_mac,
        GetSrcMacForReplica(/*multicast_group_index=*/1,
                            /*replicas_per_group=*/kPortsToUseInTest,
                            /*replicas_number=*/port_index));

    // Add a normal replication RIF and a "drop" RIF to correspond to the state
    // a multicast group member is allowed to be in.
    rif_builder.AddMrifEntryRewritingSrcMac(port_id, kDefaultInstance, src_mac)
        .AddMrifEntryRewritingSrcMac(port_id, kDefaultInstance + 1,
                                     kDropSrcMacAddress);
  }
  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::Entity> rif_entities,
      rif_builder.LogPdEntries().GetDedupedPiEntities(ir_p4info_));

  // Send all RIF entities in one batch.
  absl::Time rif_start_time = absl::Now();
  ASSERT_OK(pdpi::InstallPiEntities(sut_p4rt_session_.get(), ir_p4info_,
                                    rif_entities));
  LOG(INFO) << "Total RIF programming time: " << (absl::Now() - rif_start_time);

  // Now setup multicast groups.
  std::vector<p4::v1::Entity> group_entities;
  // Program multicast groups one by one, in case we do not reach our intended
  // limit.
  LOG(INFO) << "Intending to program " << kMaxMulticastGroups
            << " IP multicast groups with " << kPortsToUseInTest
            << " members per group.";
  absl::Time group_start_time = absl::Now();
  // Note: multicast group ID 0 is not valid.
  for (int multicast_group_id = 1; multicast_group_id <= kMaxMulticastGroups;
       ++multicast_group_id) {
    ASSERT_OK_AND_ASSIGN(
        auto multicast_group_entities,
        CreateMulticastGroupEntities(ir_p4info_, multicast_group_id, replicas));
    absl::Status add_status = pdpi::InstallPiEntities(
        sut_p4rt_session_.get(), ir_p4info_, multicast_group_entities);
    if (!add_status.ok()) {
      LOG(ERROR) << "Unable to fill replication table to hold "
                 << kMaxMulticastGroups << " IP multicast groups.";
      LOG(ERROR) << "Only " << group_entities.size() << " were programmed.";
    }
    ASSERT_OK(add_status);
    group_entities.insert(group_entities.end(),
                          multicast_group_entities.begin(),
                          multicast_group_entities.end());
  }
  LOG(INFO) << "Successfully programmed " << group_entities.size()
            << " entries.";
  LOG(INFO) << "Total multicast group programming time: "
            << (absl::Now() - group_start_time);

  // Clean up.  Multicast groups must be removed before the RIFs they reference.
  EXPECT_OK(ClearEntities(*sut_p4rt_session_, ir_p4info_, group_entities));
  EXPECT_OK(ClearEntities(*sut_p4rt_session_, ir_p4info_, rif_entities));
}

// TEST_P(L3MulticastTestFixture, PerformanceInitializationTime) {
//   GTEST_SKIP() << "Skipping because this test is not implemented yet.";
// }
// TEST_P(L3MulticastTestFixture, PerformanceMulticastGroupAdjustmentRate) {
//   GTEST_SKIP() << "Skipping because this test is not implemented yet.";
// }
// TEST_P(L3MulticastTestFixture, PerformanceReplicaArrivalTimeWithFixedDelay) {
//   GTEST_SKIP() << "Skipping because this test is not implemented yet.";
// }
// TEST_P(L3MulticastTestFixture,
//        PerformanceReplicaArrivalTimeWithUnregisteredParticipants) {
//   GTEST_SKIP() << "Skipping because this test is not implemented yet.";
// }
}  // namespace

void L3MulticastTestFixture::SetUp() {
  GetParam().mirror_testbed->SetUp();
  thinkit::MirrorTestbed& testbed =
      GetParam().mirror_testbed->GetMirrorTestbed();
  // Initialize the connection and clear table entries for the SUT.
  ASSERT_OK_AND_ASSIGN(
      sut_p4rt_session_,
      pins_test::ConfigureSwitchAndReturnP4RuntimeSession(
          testbed.Sut(), GetParam().gnmi_config, GetParam().p4info));
  // There is no need to push a config to the control switch.
  ASSERT_OK_AND_ASSIGN(ir_p4info_, pdpi::CreateIrP4Info(*GetParam().p4info));
}

}  // namespace pins_test
