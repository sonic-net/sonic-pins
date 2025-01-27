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

#include <iostream>
#include <optional>
#include <string>
#include <vector>

#include "absl/strings/str_format.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "absl/types/span.h"
#include "google/protobuf/util/message_differencer.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "tests/lib/switch_test_setup_helpers.h"

namespace {

using ::gutil::PrintTextProto;

constexpr char kBanner[] =
    "=========================================================================="
    "======\n";
constexpr char kInputHeader[] =
    "-- ORIGINAL ENTRY --------------------------------------------------------"
    "------\n";
constexpr char kOutputHeader[] =
    "-- MODIFICATIONS ---------------------------------------------------------"
    "------\n";

std::string TestHeader(absl::string_view test_name,
                       absl::Span<const pins_test::P4rtPortId> ports) {
  return absl::StrCat(
      kBanner, test_name, "\n",
      // TODO: Remove absl::StreamFormatter when we update to a new
      // LTS branch of Abseil.
      "Available ports: ", absl::StrJoin(ports, ",", absl::StreamFormatter()),
      "\n", kBanner);
}

void CompareTableEntry(const pdpi::IrTableEntry& original_entry,
                       const pdpi::IrTableEntry& rewritten_entry) {
  std::cout << kInputHeader;
  std::cout << PrintTextProto(original_entry);
  std::string diff;
  google::protobuf::util::MessageDifferencer differencer;
  differencer.ReportDifferencesToString(&diff);
  if (differencer.Compare(original_entry, rewritten_entry)) {
    std::cout << kOutputHeader << "NONE\n\n";
  } else {
    std::cout << kOutputHeader << diff << "\n";
  }
}

void CompareTableEntries(
    absl::Span<const pdpi::IrTableEntry> original_entries,
    absl::Span<const pdpi::IrTableEntry> rewritten_entries) {
  CHECK_EQ(rewritten_entries.size(), original_entries.size());  // Crash OK
  for (int i = 0; i < rewritten_entries.size(); ++i) {
    CompareTableEntry(original_entries[i], rewritten_entries[i]);
  }
}

struct PortRewriterTestCase {
  const pdpi::IrP4Info& info;
  std::string test_name;
  std::vector<pins_test::P4rtPortId> new_ports_available;
  std::vector<pdpi::IrTableEntry> original_entries;
};

void RunPortRewriterTest(const PortRewriterTestCase& test_case) {
  std::vector<pdpi::IrTableEntry> entries_to_rewrite =
      test_case.original_entries;
  ASSERT_OK(pins_test::RewritePortsInTableEntries(
      test_case.info, test_case.new_ports_available, entries_to_rewrite));
  std::cout << TestHeader(test_case.test_name, test_case.new_ports_available);
  CompareTableEntries(test_case.original_entries, entries_to_rewrite);
}

std::vector<pdpi::IrTableEntry> TableEntriesFromProtos(
    absl::Span<const std::string> protos) {
  std::vector<pdpi::IrTableEntry> entries;

  for (const auto& proto : protos) {
    entries.push_back(gutil::ParseProtoOrDie<pdpi::IrTableEntry>(proto));
  }

  return entries;
}

}  // namespace

int main(int argc, char** argv) {
  std::vector<PortRewriterTestCase> test_cases;

  test_cases.push_back(PortRewriterTestCase{
      .info = sai::GetIrP4Info(sai::Instantiation::kFabricBorderRouter),
      .test_name = "1,2,3 -> 4",
      .new_ports_available =
          pins_test::P4rtPortId::MakeVectorFromOpenConfigEncodings({4}),
      .original_entries = TableEntriesFromProtos({
          R"pb(
            table_name: "router_interface_table"
            matches {
              name: "router_interface_id"
              exact { str: "router-interface-1" }
            }
            action {
              name: "set_port_and_src_mac"
              params {
                name: "port"
                value { str: "1" }
              }
              params {
                name: "src_mac"
                value { mac: "00:02:03:04:05:06" }
              }
            }
          )pb",
          R"pb(
            table_name: "wcmp_group_table"
            matches {
              name: "wcmp_group_id"
              exact { str: "group-4294934545" }
            }
            action_set {
              actions {
                action {
                  name: "set_nexthop_id"
                  params {
                    name: "nexthop_id"
                    value { str: "nexthop-1" }
                  }
                }
                weight: 1
                watch_port: "2"
              }
              actions {
                action {
                  name: "set_nexthop_id"
                  params {
                    name: "nexthop_id"
                    value { str: "nexthop-2" }
                  }
                }
                weight: 1
                watch_port: "3"
              }
            }
          )pb",
      }),
  });

  test_cases.push_back(PortRewriterTestCase{
      .info = sai::GetIrP4Info(sai::Instantiation::kFabricBorderRouter),
      .test_name = "1 -> Exactly one of {2,3}",
      .new_ports_available =
          pins_test::P4rtPortId::MakeVectorFromOpenConfigEncodings({2, 3}),
      .original_entries = TableEntriesFromProtos({
          R"pb(
            table_name: "router_interface_table"
            matches {
              name: "router_interface_id"
              exact { str: "router-interface-1" }
            }
            action {
              name: "set_port_and_src_mac"
              params {
                name: "port"
                value { str: "1" }
              }
              params {
                name: "src_mac"
                value { mac: "00:02:03:04:05:06" }
              }
            }
          )pb",
          R"pb(
            table_name: "wcmp_group_table"
            matches {
              name: "wcmp_group_id"
              exact { str: "group-4294934545" }
            }
            action_set {
              actions {
                action {
                  name: "set_nexthop_id"
                  params {
                    name: "nexthop_id"
                    value { str: "nexthop-1" }
                  }
                }
                weight: 1
                watch_port: "1"
              }
              actions {
                action {
                  name: "set_nexthop_id"
                  params {
                    name: "nexthop_id"
                    value { str: "nexthop-2" }
                  }
                }
                weight: 1
                watch_port: "1"
              }
            }
          )pb",
      }),
  });

  test_cases.push_back(PortRewriterTestCase{
      .info = sai::GetIrP4Info(sai::Instantiation::kFabricBorderRouter),
      .test_name = "Unchanged due to only existing ports",
      .new_ports_available =
          pins_test::P4rtPortId::MakeVectorFromOpenConfigEncodings({2, 3}),
      .original_entries = TableEntriesFromProtos({
          R"pb(
            table_name: "router_interface_table"
            matches {
              name: "router_interface_id"
              exact { str: "router-interface-1" }
            }
            action {
              name: "set_port_and_src_mac"
              params {
                name: "port"
                value { str: "2" }
              }
              params {
                name: "src_mac"
                value { mac: "00:02:03:04:05:06" }
              }
            }
          )pb",
          R"pb(
            table_name: "wcmp_group_table"
            matches {
              name: "wcmp_group_id"
              exact { str: "group-4294934545" }
            }
            action_set {
              actions {
                action {
                  name: "set_nexthop_id"
                  params {
                    name: "nexthop_id"
                    value { str: "nexthop-1" }
                  }
                }
                weight: 1
                watch_port: "2"
              }
              actions {
                action {
                  name: "set_nexthop_id"
                  params {
                    name: "nexthop_id"
                    value { str: "nexthop-2" }
                  }
                }
                weight: 1
                watch_port: "3"
              }
            }
          )pb",
      }),
  });

  test_cases.push_back(PortRewriterTestCase{
      .info = sai::GetIrP4Info(sai::Instantiation::kFabricBorderRouter),
      .test_name = "All unchanged due to no ports",
      .new_ports_available =
          pins_test::P4rtPortId::MakeVectorFromOpenConfigEncodings({1}),
      .original_entries = TableEntriesFromProtos({
          R"pb(
            table_name: "neighbor_table"
            matches {
              name: "router_interface_id"
              exact { str: "router-interface-1" }
            }
            matches {
              name: "neighbor_id"
              exact { str: "fe80::3e28:6dff:fe34:c002" }
            }
            action {
              name: "set_dst_mac"
              params {
                name: "dst_mac"
                value { mac: "3c:28:6d:34:c0:02" }
              }
            }
          )pb",
          R"pb(
            table_name: "nexthop_table"
            matches {
              name: "nexthop_id"
              exact { str: "nexthop-1" }
            }
            action {
              name: "set_ip_nexthop"
              params {
                name: "router_interface_id"
                value { str: "router-interface-1" }
              }
              params {
                name: "neighbor_id"
                value { str: "fe80::3e28:6dff:fe34:c002" }
              }
            }
          )pb",
          R"pb(
            table_name: "ipv4_table"
            matches {
              name: "vrf_id"
              exact { str: "vrf-80" }
            }
            action {
              name: "set_wcmp_group_id"
              params {
                name: "wcmp_group_id"
                value { str: "group-4294934531" }
              }
            }
          )pb",
          R"pb(
            table_name: "ipv6_table"
            matches {
              name: "vrf_id"
              exact { str: "vrf-80" }
            }
            action {
              name: "set_wcmp_group_id"
              params {
                name: "wcmp_group_id"
                value { str: "group-4294934531" }
              }
            }
          )pb",
          R"pb(
            table_name: "vrf_table"
            matches {
              name: "vrf_id"
              exact { str: "vrf-80" }
            }
            action { name: "no_action" }
          )pb",
      }),
  });

  test_cases.push_back(PortRewriterTestCase{
      .info = sai::GetIrP4Info(sai::Instantiation::kFabricBorderRouter),
      .test_name = "Roughly even number of 1, 2, and 3, with existing 3 "
                   "and port-less entries unchanged",
      .new_ports_available =
          pins_test::P4rtPortId::MakeVectorFromOpenConfigEncodings({1, 2, 3}),
      .original_entries = TableEntriesFromProtos({
          R"pb(
            table_name: "neighbor_table"
            matches {
              name: "router_interface_id"
              exact { str: "router-interface-1" }
            }
            matches {
              name: "neighbor_id"
              exact { str: "fe80::3e28:6dff:fe34:c002" }
            }
            action {
              name: "set_dst_mac"
              params {
                name: "dst_mac"
                value { mac: "3c:28:6d:34:c0:02" }
              }
            }
          )pb",
          R"pb(
            table_name: "router_interface_table"
            matches {
              name: "router_interface_id"
              exact { str: "router-interface-1" }
            }
            action {
              name: "set_port_and_src_mac"
              params {
                name: "port"
                value { str: "3" }
              }
              params {
                name: "src_mac"
                value { mac: "00:02:03:04:05:06" }
              }
            }
          )pb",
          R"pb(
            table_name: "wcmp_group_table"
            matches {
              name: "wcmp_group_id"
              exact { str: "group-4294934545" }
            }
            action_set {
              actions {
                action {
                  name: "set_nexthop_id"
                  params {
                    name: "nexthop_id"
                    value { str: "nexthop-1" }
                  }
                }
                weight: 1
                watch_port: "4"
              }
              actions {
                action {
                  name: "set_nexthop_id"
                  params {
                    name: "nexthop_id"
                    value { str: "nexthop-2" }
                  }
                }
                weight: 1
                watch_port: "5"
              }
            }
          )pb",
          R"pb(
            table_name: "l3_admit_table"
            matches {
              name: "dst_mac"
              ternary {
                value { mac: "02:32:0a:ce:c4:04" }
                mask { mac: "ff:ff:ff:ff:ff:ff" }
              }
            }
            matches {
              name: "in_port"
              optional { value { str: "7" } }
            }
            priority: 2030
            action { name: "admit_to_l3" }
          )pb",
          R"pb(
            table_name: "acl_ingress_table"
            matches {
              name: "is_ipv4"
              optional { value { hex_str: "0x1" } }
            }
            matches {
              name: "ip_protocol"
              ternary {
                value { hex_str: "0x11" }
                mask { hex_str: "0xff" }
              }
            }
            matches {
              name: "l4_dst_port"
              ternary {
                value { hex_str: "0x0223" }
                mask { hex_str: "0xffff" }
              }
            }
            matches {
              name: "in_port"
              optional { value { str: "8" } }
            }
            priority: 3100
            action { name: "acl_drop" }
          )pb",
          R"pb(
            table_name: "acl_pre_ingress_table"
            matches {
              name: "in_port"
              optional { value { str: "9" } }
            }
            priority: 1151
            action {
              name: "set_vrf"
              params {
                name: "vrf_id"
                value { str: "vrf-210" }
              }
            }
          )pb",
          R"pb(
            table_name: "acl_egress_table"
            matches {
              name: "ether_type"
              ternary {
                value { hex_str: "0x0800" }
                mask { hex_str: "" }
              }
            }
            matches {
              name: "ip_protocol"
              ternary {
                value { hex_str: "0x11" }
                mask { hex_str: "0xff" }
              }
            }
            matches {
              name: "l4_dst_port"
              ternary {
                value { hex_str: "0x0223" }
                mask { hex_str: "0xffff" }
              }
            }
            matches {
              name: "out_port"
              optional { value { str: "10" } }
            }
            priority: 3101
            action { name: "acl_drop" }
          )pb",
          R"pb(
            table_name: "wcmp_group_table"
            matches {
              name: "wcmp_group_id"
              exact { str: "group-4294934545" }
            }
            action_set {
              actions {
                action {
                  name: "set_nexthop_id"
                  params {
                    name: "nexthop_id"
                    value { str: "nexthop-1" }
                  }
                }
                weight: 1
                watch_port: "11"
              }
              actions {
                action {
                  name: "set_nexthop_id"
                  params {
                    name: "nexthop_id"
                    value { str: "nexthop-2" }
                  }
                }
                weight: 1
                watch_port: "12"
              }
              actions {
                action {
                  name: "set_nexthop_id"
                  params {
                    name: "nexthop_id"
                    value { str: "nexthop-2" }
                  }
                }
                weight: 1
                watch_port: "13"
              }
              actions {
                action {
                  name: "set_nexthop_id"
                  params {
                    name: "nexthop_id"
                    value { str: "nexthop-2" }
                  }
                }
                weight: 1
                watch_port: "14"
              }
              actions {
                action {
                  name: "set_nexthop_id"
                  params {
                    name: "nexthop_id"
                    value { str: "nexthop-2" }
                  }
                }
                weight: 1
                watch_port: "15"
              }
              actions {
                action {
                  name: "set_nexthop_id"
                  params {
                    name: "nexthop_id"
                    value { str: "nexthop-2" }
                  }
                }
                weight: 1
                watch_port: "16"
              }
              actions {
                action {
                  name: "set_nexthop_id"
                  params {
                    name: "nexthop_id"
                    value { str: "nexthop-2" }
                  }
                }
                weight: 1
                watch_port: "17"
              }
            }
          )pb",
      }),
  });

  for (const PortRewriterTestCase& test_case : test_cases) {
    RunPortRewriterTest(test_case);
  }

  return 0;
}  // NOLINT(readability/fn_size)
