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

#include "sai_p4/instantiations/google/test_tools/table_entry_generator.h"

#include <bitset>
#include <cstdint>
#include <functional>
#include <optional>
#include <string>
#include <utility>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "glog/logging.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "sai_p4/instantiations/google/test_tools/table_entry_generator_helper.h"

namespace sai {
namespace {

constexpr absl::string_view kVrf80 = "vrf-80";

// Returns a compatible IP type match if supported by the table. Returns
// std::nullopt is no IP match is supported.
std::optional<pdpi::IrMatch> IpTypeMatch(
    const pdpi::IrTableDefinition& table_definition) {
  std::string ip_match;
  if (table_definition.match_fields_by_name().contains("is_ip")) {
    ip_match = "is_ip";
  } else if (table_definition.match_fields_by_name().contains("is_ipv6")) {
    ip_match = "is_ipv6";
  } else if (table_definition.match_fields_by_name().contains("is_ipv4")) {
    ip_match = "is_ipv4";
  } else {
    return std::nullopt;
  }
  pdpi::IrMatch match;
  if (!ip_match.empty()) {
    match.set_name(ip_match);
    match.mutable_optional()->mutable_value()->set_hex_str("0x1");
  }
  return match;
}

pdpi::IrTableEntry DefaultVrf80Entry() {
  auto entry = gutil::ParseTextProto<pdpi::IrTableEntry>(absl::Substitute(
      R"pb(table_name: "vrf_table"
           matches {
             name: "vrf_id"
             exact { str: "$0" }
           }
           action { name: "no_action" })pb",
      kVrf80));
  if (!entry.ok()) LOG(FATAL) << entry.status();  // Crash OK
  return *entry;
}

TableEntryGenerator Ipv4TableGenerator(
    const pdpi::IrTableDefinition& table_definition) {
  TableEntryGenerator generator;
  generator.prerequisites.push_back(DefaultVrf80Entry());

  auto base_entry = gutil::ParseTextProto<pdpi::IrTableEntry>(
      absl::Substitute(R"pb(table_name: "ipv4_table"
                            matches {
                              name: "vrf_id"
                              exact { str: "$0" }
                            }
                            action { name: "drop" })pb",
                       kVrf80));
  if (!base_entry.ok()) LOG(FATAL) << base_entry.status();  // Crash OK
  generator.generator =
      IrMatchFieldGenerator(table_definition, *base_entry, "ipv4_dst");
  return generator;
}

TableEntryGenerator Ipv6TableGenerator(
    const pdpi::IrTableDefinition& table_definition) {
  TableEntryGenerator generator;
  generator.prerequisites.push_back(DefaultVrf80Entry());

  auto base_entry = gutil::ParseTextProto<pdpi::IrTableEntry>(
      absl::Substitute(R"pb(table_name: "ipv6_table"
                            matches {
                              name: "vrf_id"
                              exact { str: "$0" }
                            }
                            action { name: "drop" })pb",
                       kVrf80));
  if (!base_entry.ok()) LOG(FATAL) << base_entry.status();  // Crash OK
  generator.generator =
      IrMatchFieldGenerator(table_definition, *base_entry, "ipv6_dst");
  return generator;
}

TableEntryGenerator AclIngressTableGenerator(
    const pdpi::IrTableDefinition& table_definition) {
  TableEntryGenerator generator;
  auto base_entry = gutil::ParseTextProto<pdpi::IrTableEntry>(
      R"pb(table_name: "acl_ingress_table"
           priority: 1
           action { name: "acl_drop" })pb");
  if (!base_entry.ok()) LOG(FATAL) << base_entry.status();  // Crash OK
  generator.generator = IrMatchFieldAndPriorityGenerator(
      table_definition, *base_entry, "dst_mac");
  return generator;
}

TableEntryGenerator AclIngressCountingTableGenerator(
    const pdpi::IrTableDefinition& table_definition) {
  TableEntryGenerator generator;
  auto base_entry = gutil::ParseTextProto<pdpi::IrTableEntry>(
      R"pb(table_name: "acl_ingress_counting_table"
           priority: 1
           action { name: "acl_count" })pb");
  if (!base_entry.ok()) LOG(FATAL) << base_entry.status();  // Crash OK
  generator.generator = IrMatchFieldAndPriorityGenerator(
      table_definition, *base_entry, "route_metadata");
  return generator;
}

TableEntryGenerator AclPreIngressTableGenerator(
    const pdpi::IrTableDefinition& table_definition) {
  TableEntryGenerator generator;
  generator.prerequisites.push_back(DefaultVrf80Entry());

  auto base_entry = gutil::ParseTextProto<pdpi::IrTableEntry>(
      absl::Substitute(R"pb(table_name: "acl_pre_ingress_table"
                            action {
                              name: "set_vrf"
                              params {
                                name: "vrf_id"
                                value { str: "$0" }
                              }
                            })pb",
                       kVrf80));
  if (!base_entry.ok()) LOG(FATAL) << base_entry.status();  // Crash OK
    // Add an IP match if supported by the table.
  if (auto match = IpTypeMatch(table_definition); match.has_value()) {
    *base_entry->add_matches() = *match;
  }
  generator.generator = IrMatchFieldAndPriorityGenerator(
      table_definition, *base_entry, "src_mac");
  return generator;
}

TableEntryGenerator AclPreIngressVlanTableGenerator(
    const pdpi::IrTableDefinition& table_definition) {
  TableEntryGenerator generator;
  generator.prerequisites.push_back(DefaultVrf80Entry());

  auto base_entry = gutil::ParseTextProto<pdpi::IrTableEntry>(
      R"pb(table_name: "acl_pre_ingress_vlan_table"
           action {
             name: "set_outer_vlan_id"
             params {
               name: "vlan_id"
               value { hex_str: "0x001" }
             }
           })pb");
  if (!base_entry.ok()) LOG(FATAL) << base_entry.status();  // Crash OK
  generator.generator = PriorityGenerator(*base_entry);
  return generator;
}

TableEntryGenerator AclPreIngressMetadataTableGenerator(
    const pdpi::IrTableDefinition& table_definition) {
  TableEntryGenerator generator;
  generator.prerequisites.push_back(DefaultVrf80Entry());

  auto base_entry = gutil::ParseTextProto<pdpi::IrTableEntry>(
      R"pb(table_name: "acl_pre_ingress_metadata_table"
           action {
             name: "set_acl_metadata"
             params {
               name: "acl_metadata"
               value { hex_str: "0x01" }
             }
           })pb");
  if (!base_entry.ok()) LOG(FATAL) << base_entry.status();  // Crash OK
  
  // Add an IP match if supported by the table.
  if (auto match = IpTypeMatch(table_definition); match.has_value()) {
    *base_entry->add_matches() = *match;
  }

  generator.generator = IrMatchFieldAndPriorityGenerator(
      table_definition, *base_entry, "ip_protocol");
  return generator;
}

TableEntryGenerator AclEgressTableGenerator(
    const pdpi::IrTableDefinition& table_definition) {
  TableEntryGenerator generator;
  auto base_entry = gutil::ParseTextProto<pdpi::IrTableEntry>(
      R"pb(table_name: "acl_egress_table"
           matches {
             name: "is_ip"
             optional { value { hex_str: "0x1" } }
           }
           action { name: "acl_drop" })pb");
  if (!base_entry.ok()) LOG(FATAL) << base_entry.status();  // Crash OK
  generator.generator = PriorityGenerator(*base_entry);
  return generator;
}

TableEntryGenerator AclEgressL2TableGenerator(
    const pdpi::IrTableDefinition& table_definition) {
  TableEntryGenerator generator;
  auto base_entry = gutil::ParseTextProto<pdpi::IrTableEntry>(
      R"pb(table_name: "acl_egress_l2_table"
           action { name: "acl_drop" })pb");
  if (!base_entry.ok()) LOG(FATAL) << base_entry.status();  // Crash OK
  generator.generator = IrMatchFieldAndPriorityGenerator(
      table_definition, *base_entry, "src_mac");
  return generator;
}

TableEntryGenerator AclEgressDhcpToHostTableGenerator(
    const pdpi::IrTableDefinition& table_definition) {
  TableEntryGenerator generator;
  auto base_entry = gutil::ParseTextProto<pdpi::IrTableEntry>(
      R"pb(table_name: "acl_egress_dhcp_to_host_table"
           matches {
             name: "is_ip"
             optional { value { hex_str: "0x1" } }
           }
           action { name: "acl_drop" })pb");
  if (!base_entry.ok()) LOG(FATAL) << base_entry.status();  // Crash OK
  generator.generator = PriorityGenerator(*base_entry);
  return generator;
}

TableEntryGenerator AclIngressSecurityTableGenerator(
    const pdpi::IrTableDefinition& table_definition) {
  TableEntryGenerator generator;
  auto base_entry = gutil::ParseTextProto<pdpi::IrTableEntry>(
      R"pb(table_name: "acl_ingress_security_table"
           action { name: "acl_drop" })pb");
  if (!base_entry.ok()) LOG(FATAL) << base_entry.status();  // Crash OK
  generator.generator = IrMatchFieldAndPriorityGenerator(
      table_definition, *base_entry, "ether_type");
  return generator;
}

TableEntryGenerator AclIngressQosTableGenerator(
    const pdpi::IrTableDefinition& table_definition) {
  TableEntryGenerator generator;
  auto base_entry = gutil::ParseTextProto<pdpi::IrTableEntry>(
      R"pb(table_name: "acl_ingress_qos_table"
           meter_config { cir: 5000 cburst: 5000 pir: 5000 pburst: 5000 }
           matches {
             name: "is_ipv4"
             optional { value { hex_str: "0x1" } }
           }
           action {
             name: "set_qos_queue_and_cancel_copy_above_rate_limit"
             params {
               name: "qos_queue"
               value { str: "0x7" }
             }
           })pb");
  if (!base_entry.ok()) LOG(FATAL) << base_entry.status();  // Crash OK
  generator.generator = IrMatchFieldAndPriorityGenerator(
      table_definition, *base_entry, "ip_protocol");
  return generator;
}

TableEntryGenerator L3AdmitTableGenerator(
    const pdpi::IrTableDefinition& table_definition) {
  TableEntryGenerator generator;
  auto base_entry = gutil::ParseTextProto<pdpi::IrTableEntry>(
      R"pb(table_name: "l3_admit_table"
           priority: 1
           action { name: "admit_to_l3" })pb");
  if (!base_entry.ok()) LOG(FATAL) << base_entry.status();  // Crash OK
  generator.generator =
      IrMatchFieldGenerator(table_definition, *base_entry, "dst_mac");
  return generator;
}

TableEntryGenerator MulticastRouterInterfaceTableGenerator(
    const pdpi::IrTableDefinition& table_definition) {
  auto base_entry = gutil::ParseProtoOrDie<pdpi::IrTableEntry>(R"pb(
    table_name: "multicast_router_interface_table"
    matches {
      name: "multicast_replica_port"
      exact { str: "1" }
    }
    action {
      name: "multicast_set_src_mac"
      params {
        name: "src_mac"
        value { mac: "06:05:04:03:02:01" }
      }
    }
  )pb");
  return TableEntryGenerator{
      .generator = IrMatchFieldGenerator(table_definition, base_entry,
                                         "multicast_replica_instance"),
  };
}

TableEntryGenerator Ipv6TunnelTerminationGenerator(
    const pdpi::IrTableDefinition& table_definition) {
  TableEntryGenerator generator;
  auto base_entry = gutil::ParseTextProto<pdpi::IrTableEntry>(R"pb(
    table_name: "ipv6_tunnel_termination_table"
    priority: 1
    matches {
      name: "src_ipv6"
      ternary {
        value { ipv6: "0001:0002:0003:0004:0005:0006:1111:2222" }
        mask { ipv6: "ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff" }
      }

    }
    action { name: "tunnel_decap" }
  )pb");
  if (!base_entry.ok()) LOG(FATAL) << base_entry.status();  // Crash OK
  generator.generator =
      IrMatchFieldGenerator(table_definition, *base_entry, "dst_ipv6");
  return generator;
}

TableEntryGenerator MirrorSessionGeneratorImpl() {
  TableEntryGenerator generator;
  generator.generator = [](int index) {
    pdpi::IrTableEntry entry = gutil::ParseProtoOrDie<pdpi::IrTableEntry>(
        R"pb(
          table_name: "mirror_session_table"
          action {
            name: "mirror_with_vlan_tag_and_ipfix_encapsulation"
            params {
              name: "monitor_port"
              # Hack: Port 1 is configured on all testbeds.
              value { str: "1" }
            }
            params {
              name: "monitor_failover_port"
              # Hack: Port 2 is configured on all testbeds.
              value { str: "2" }
            }
            params {
              name: "mirror_encap_src_mac"
              value { mac: "06:05:04:03:02:01" }
            }
            params {
              name: "mirror_encap_dst_mac"
              value { mac: "06:05:04:03:02:02" }
            }
            params {
              name: "mirror_encap_vlan_id"
              value { hex_str: "0x0fe" }
            }
            params {
              name: "mirror_encap_src_ip"
              value { ipv6: "2222:2222:2222:2222:2222:2222:2222:2222" }
            }
            params {
              name: "mirror_encap_dst_ip"
              value { ipv6: "4444:4444:4444:4444:4444:4444:4444:4444" }
            }
            params {
              name: "mirror_encap_udp_src_port"
              value { hex_str: "0x1234" }
            }
            params {
              name: "mirror_encap_udp_dst_port"
              value { hex_str: "0x5678" }
            }
          }
        )pb");

    pdpi::IrMatch& match = *entry.mutable_matches()->Add();
    match.set_name("mirror_session_id");
    match.mutable_exact()->set_str(absl::StrCat("mirror_session_id_", index));
    return entry;
  };
  return generator;
}

// Returns a generator for mirror_session_table.
// The IrTableDefinition parameter is not used but is needed to conform to the
// TableEntryGenerator interface.
TableEntryGenerator MirrorSessionGenerator(
    const pdpi::IrTableDefinition& unused_table_definition) {
  return MirrorSessionGeneratorImpl();
}

// Generator for acl_ingress_mirror_and_redirect_table.
TableEntryGenerator AclIngressMirrorAndRedirectGenerator(
    const pdpi::IrTableDefinition& table_definition) {
  TableEntryGenerator generator;
  pdpi::IrTableEntry base_entry = gutil::ParseProtoOrDie<pdpi::IrTableEntry>(
      R"pb(
        table_name: "acl_ingress_mirror_and_redirect_table"
        matches {
          name: "is_ipv6"
          optional { value { hex_str: "0x1" } }
        }
        action {
          name: "redirect_to_port"
          params {
            name: "redirect_port"
            # Port 1 is almost always present in a testbed.
            value { str: "1" }
          }
        }
      )pb");
  // Generate entries with various dst_ip values.
  // the reason for using dst_ip is because, unlike in_port which is present
  // only in some instantiations, dst_ip is present in all instantiations.
  generator.generator = IrMatchFieldAndPriorityGenerator(
      table_definition, base_entry, "dst_ipv6");
  return generator;
}

const absl::flat_hash_set<std::string>& KnownUnsupportedTables() {
  static const auto* const kUnsupportedTables =
      new absl::flat_hash_set<std::string>({
          "vrf_table",
          "neighbor_table",
          "router_interface_table",
          "tunnel_table",
          "nexthop_table",
          "wcmp_group_table",
          // Logical table that is not supported by the switch.
          "ingress_clone_table",
	  // No generator is needed for these tables as there can only be one
          // entry (lpm prefix_length == 0) in these tables.
          "disable_egress_vlan_checks_table",
          "disable_ingress_vlan_checks_table",
          // These tables will be deprecated in the future.
          "disable_vlan_checks_table",
          // TODO: Remove this table once the entire fleet's P4
          // programs support ingress cloning.
          "mirror_port_to_pre_session_table",
	  // TODO: Enable this table when it has been removed from
          // unsupported roles.
          "mirror_session_table",
	  // TODO: Add support for these tables once the switch
          // supports it.
          "ipv4_multicast_table",
          "ipv6_multicast_table",
          // TODO: Remove and re-enable in `GetGenerator` once
          // resource modeling is fixed.
          "multicast_router_interface_table",
          // TODO: Add support for this table once the switch
          // supports it.
          "vlan_table",
          "vlan_membership_table",
      });
  return *kUnsupportedTables;
}

}  // namespace

absl::StatusOr<TableEntryGenerator> GetGenerator(
    const pdpi::IrTableDefinition& table) {
  // Map of table name to generator. We're using std::function instead of
  // absl::AnyInvocable because std::function is copyable.
  static auto* const kGenerators = new absl::flat_hash_map<
      std::string,
      std::function<TableEntryGenerator(const pdpi::IrTableDefinition&)>>({
      {"acl_pre_ingress_table", AclPreIngressTableGenerator},
      {"acl_pre_ingress_vlan_table", AclPreIngressVlanTableGenerator},
      {"acl_pre_ingress_metadata_table", AclPreIngressMetadataTableGenerator},
      {"acl_ingress_table", AclIngressTableGenerator},
      {"acl_ingress_qos_table", AclIngressQosTableGenerator},
      {"acl_ingress_security_table", AclIngressSecurityTableGenerator},
      {"acl_ingress_counting_table", AclIngressCountingTableGenerator},
      // TODO: Enable this table when it has been removed from
      // unsupported roles.
      // {"mirror_session_table", MirrorSessionGenerator},
      {"acl_egress_table", AclEgressTableGenerator},
      {"acl_egress_l2_table", AclEgressL2TableGenerator},
      {"acl_egress_dhcp_to_host_table", AclEgressDhcpToHostTableGenerator},
      {"ipv4_table", Ipv4TableGenerator},
      {"ipv6_table", Ipv6TableGenerator},
      {"ipv6_tunnel_termination_table", Ipv6TunnelTerminationGenerator},
      {"l3_admit_table", L3AdmitTableGenerator},
      {"acl_ingress_mirror_and_redirect_table",
       AclIngressMirrorAndRedirectGenerator},
      // TODO: Re-enable when once modeling is fixed.
      // {"multicast_router_interface_table",
      //  MulticastRouterInterfaceTableGenerator},
  });

  const std::string& table_name = table.preamble().alias();
  if (KnownUnsupportedTables().contains(table_name)) {
    return gutil::UnimplementedErrorBuilder()
           << "Table " << table_name << " is known but not supported";
  }
  auto generator = kGenerators->find(table_name);
  if (generator == kGenerators->end()) {
    return gutil::UnknownErrorBuilder()
           << "No TableEntryGenerator is implemented for  '" << table_name
           << "'. Please add a generator by following examples in "
           << "google3/third_party/pins_infra/sai_p4/instantiations/google/"
              "test_tools/table_entry_generator.cc";
  }
  return generator->second(table);
}

}  // namespace sai
