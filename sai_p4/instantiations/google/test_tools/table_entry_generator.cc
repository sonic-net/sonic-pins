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
#include <string>
#include <utility>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "glog/logging.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "sai_p4/instantiations/google/test_tools/table_entry_generator_helper.h"

namespace sai {
namespace {

constexpr absl::string_view kVrf80 = "vrf-80";

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
           matches {
             name: "is_ip"
             optional { value { hex_str: "0x1" } }
           }
           action {
             name: "set_acl_metadata"
             params {
               name: "acl_metadata"
               value { hex_str: "0x01" }
             }
           })pb");
  if (!base_entry.ok()) LOG(FATAL) << base_entry.status();  // Crash OK
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
           matches {
             name: "is_ipv4"
             optional { value { hex_str: "0x1" } }
           }
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
      name: "set_multicast_src_mac"
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
          // TODO: Add support for this table once the switch
          // supports it.
          "acl_ingress_mirror_and_redirect_table",
          // TODO: Add support for this table once the switch
          // supports it.
          "mirror_session_table",
          // TODO: Remove this table once the entire fleet's P4
          // programs support ingress cloning.
          "mirror_port_to_pre_session_table",
          // TODO: Add support for these tables once the switch
          // supports it.
          "ipv4_multicast_table",
          "ipv6_multicast_table",
          // TODO: Add support for this table once the switch
          // supports it.
          "disable_vlan_checks_table",
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
      {"acl_egress_table", AclEgressTableGenerator},
      {"acl_egress_dhcp_to_host_table", AclEgressDhcpToHostTableGenerator},
      {"ipv4_table", Ipv4TableGenerator},
      {"ipv6_table", Ipv6TableGenerator},
      {"ipv6_tunnel_termination_table", Ipv6TunnelTerminationGenerator},
      {"l3_admit_table", L3AdmitTableGenerator},
      {"multicast_router_interface_table",
       MulticastRouterInterfaceTableGenerator},
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
