
#include <iostream>
#include <string>

#include "absl/strings/string_view.h"
#include "dvaas/packet_trace.h"
#include "dvaas/packet_trace.pb.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/testing.h"

namespace dvaas {
namespace {

TEST(GetPacketTraceSummaryTest, GetPacketTraceSummaryGoldenTest) {
  dvaas::PacketTrace packet_trace = gutil::ParseProtoOrDie<PacketTrace>(R"pb(
    bmv2_textual_log: "BMv2 textual log"
    events {
      table_apply {
        table_name: "ingress.vlan_untag.disable_vlan_checks_table"
        hit_or_miss_textual_log: "Table \'ingress.vlan_untag.disable_vlan_checks_table\': hit with handle 0\n[0.0] [cxt 0] Dumping entry 0\nMatch key:\n* dummy_match         : TERNARY   00 &&& 00\nPriority: 2147483646\nAction entry: ingress.vlan_untag.disable_vlan_checks - "
        hit {
          table_entry {
            table_name: "disable_vlan_checks_table"
            priority: 1
            action { name: "disable_vlan_checks" }
          }
        }
      }
    }
    events {
      table_apply {
        table_name: "egress.packet_rewrites.multicast_rewrites.multicast_router_interface_table"
        hit_or_miss_textual_log: "Table \'egress.packet_rewrites.multicast_rewrites.multicast_router_interface_table\': hit with handle 2\n[0.1] [cxt 0] Dumping entry 2\nMatch key:\n* multicast_replica_port    : EXACT     0037\n* multicast_replica_instance: EXACT     04d2\nAction entry: egress.packet_rewrites.multicast_rewrites.set_multicast_src_mac - 70707070707,"
        hit {}
      }
    }
    events {
      table_apply {
        table_name: "ingress.ingress_vlan_checks.vlan_membership_table"
        hit_or_miss_textual_log: "Table \'ingress.ingress_vlan_checks.vlan_membership_table\': miss"
        miss {}
      }
    }
    events {
      mark_to_drop {
        source_location: "./third_party/pins_infra/sai_p4/fixed/routing.p4(275)"
      }
    }
    events { packet_replication { number_of_packets_replicated: 3 } }
  )pb");

  std::string packet_trace_summary = dvaas::GetPacketTraceSummary(packet_trace);

  // Print the input packet trace and output packet trace summary to diff
  // against the golden file "dataplane_validation_test.expected". Golden
  // testing is preferable to using expectations as we expect the packet trace
  // summary to change and updating the test manually is tedious.
  std::cout << "== INPUT: dvaas::PacketTrace proto ====================\n"
            << gutil::PrintTextProto(packet_trace)
            << "== OUTPUT: PacketTraceSummary ====================\n"
            << packet_trace_summary;
}

}  // namespace
}  // namespace dvaas
