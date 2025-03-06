#ifndef PINS_P4_SYMBOLIC_SAI_SAI_COVERAGE_GOALS_H_
#define PINS_P4_SYMBOLIC_SAI_SAI_COVERAGE_GOALS_H_

#include "gutil/gutil/testing.h"
#include "p4_symbolic/packet_synthesizer/coverage_goal.pb.h"

namespace p4_symbolic::packet_synthesizer {

inline CoverageGoals SaiDefaultCoverageGoals() {
  return gutil::ParseProtoOrDie<CoverageGoals>(
      R"pb(
        coverage_goals {
          cartesian_product_coverage {
            # TODO: Restore header coverage when performance is
            # improved.
            # header_coverage {
            #  headers { patterns: [ "*" ] }
            #  header_exclusions {
            #    patterns: [
            #      # Optimization: do not need to target ethernet individually.
            #      All
            #      # valid packets for SAI-P4 will have the ethernet header.
            #      "ethernet"
            #    ]
            #    patterns: [
            #      # PacketIO is currently handled differently in dataplane
            #      tests.
            #      "packet_in_header",
            #      "packet_out_header"
            #    ]
            #    patterns: [
            #      # The following are not satisfiable anyway (because the
            #      # headers will never be valid in ingress).
            #      "erspan_ipv4",
            #      "erspan_gre",
            #      "erspan_ethernet",
            #      "tunnel_encap_ipv6",
            #      "tunnel_encap_gre"
            #    ]
            #  }
            #  headers_to_prevent_unless_explicitly_covered {
            #    patterns: [ "vlan" ]
            #  }
            #  include_wildcard_header: true
            # }
            packet_fate_coverage { fates: [ DROP, NOT_DROP ] }
            entry_coverage {
              tables { patterns: [ "*" ] }
              table_exclusions {
                # TODO: Excluding tables that are covered by
                # covering other tables and for which packet synthesis is
                # expensive.
                patterns: [
                  "ingress.routing_resolution.neighbor_table",
                  "ingress.routing_resolution.nexthop_table",
                  "ingress.routing_resolution.router_interface_table",
                  "ingress.routing_resolution.wcmp_group_table",
                  "ingress.routing_resolution.tunnel_table",
                  # TODO: Remove the following when PINS releases
                  # no longer include the tables.
                  "ingress.routing.neighbor_table",
                  "ingress.routing.nexthop_table",
                  "ingress.routing.router_interface_table",
                  "ingress.routing.wcmp_group_table",
                  "ingress.routing.tunnel_table"
                ]
              }
              cover_default_actions: true
              # TODO: Currently must ignore cover for default
              # action of empty tables due to the limitation of
              # packet_util::SynthesizePackets's return type
              # (TestPacketsByTargetEntry).
              # TODO: Also covering these tables is
              # expensive. Remove when these limitations are addressed.
              exclude_empty_tables: true
            }
            # Avoid L2 broadcast packets.
            # TODO: Remove when L2 broadcast is modeled
            custom_criteria_coverage {
              criteria_list {
                input_packet_header_criteria {
                  field_criteria {
                    negated: true
                    field_match {
                      name: "ethernet.dst_addr"
                      exact { mac: "ff:ff:ff:ff:ff:ff" }
                    }
                  }
                }
              }
            }
          }
        }
      )pb");
}

}  // namespace p4_symbolic::packet_synthesizer

#endif  // PINS_P4_SYMBOLIC_SAI_SAI_COVERAGE_GOALS_H_
