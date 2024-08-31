#ifndef PINS_P4_SYMBOLIC_SAI_SAI_COVERAGE_GOALS_H_
#define PINS_P4_SYMBOLIC_SAI_SAI_COVERAGE_GOALS_H_

#include "gutil/testing.h"
#include "p4_symbolic/packet_synthesizer/coverage_goal.pb.h"

namespace p4_symbolic::packet_synthesizer {

inline CoverageGoals SaiDefaultCoverageGoals() {
  return gutil::ParseProtoOrDie<CoverageGoals>(
      R"pb(
        coverage_goals {
          cartesian_product_coverage {
            header_coverage {
              headers { patterns: [ "*" ] }
              header_exclusions {
                patterns: [
                  # Optimization: do not need to target ethernet individually.
                  # All valid packets for SAI-P4 will have the ethernet header.
                  "ethernet"
                ]
                patterns: [
                  # PacketIO is currently handled differently in dataplane
                  # tests.
                  "packet_in_header",
                  "packet_out_header"
                ]
                patterns: [
                  # Optimization: The following are not satisfiable anyway
                  # (because the headers will never be valid in ingress).
                  "mirror_encap_ethernet",
                  "mirror_encap_vlan",
                  "mirror_encap_ipv6",
                  "mirror_encap_udp",
                  "mirror_encap_ipfix",
                  "mirror_encap_psamp_extended",
                  "ipfix",
                  "psamp_extended",
                  "tunnel_encap_ipv6",
                  "tunnel_encap_gre"
                ]
              }
              headers_to_prevent_unless_explicitly_covered {
                patterns: [ "vlan" ]
              }
              include_wildcard_header: true
            }
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
                  "ingress.routing_resolution.tunnel_table"
                ]
              }
              cover_default_actions: true
              # TODO: Currently must ignore cover for default
              # action of empty tables due to the limitation of
              # packet_util::SynthesizePackets's return type
              # (TestPacketsByTargetEntity).
              # TODO: Also covering these tables is
              # expensive. Remove when these limitations are addressed.
              exclude_empty_tables: true
            }
            custom_criteria_coverage {
              criteria_list {
                input_packet_header_criteria {
                  # Don't test PTP packets. Forwarding behavior is very switch
                  # dependent. The spec allows for packets to be dropped,
                  # updated to newer versions, or ignored
                  # PTP behavior will be covered in
                  # standalone tests: go/switch-ptp-tp.
                  field_criteria {
                    negated: true
                    field_match {
                      name: "udp.dst_port"
                      exact { hex_str: "0x013f" }  # PTP: port=319
                    }
                  }
                  # Today we only model PSP transport mode in our P4 programs.
                  # So we  should not see the optional virtualization cookie
                  # which is only used by PSP tunnel mode.
                  #
                  # In our P4 program the psp_info field holds:
                  #   +-+-+-+-+-+-+-+-+
                  #   |S|D|Version|V|R|
                  #   +-+-+-+-+-+-+-+-+
                  #    7 6 5 4 3 2 1 0
                  # Where V is the bit that says whether a virutalization cookie
                  # is present or not.
                  field_criteria {
                    field_match {
                      name: "psp.psp_info"
                      ternary {
                        value { hex_str: "0x00" }
                        mask { hex_str: "0x02" }
                      }
                    }
                  }
                  # Avoid L2 broadcast packets.
                  # TODO: Remove when L2 broadcast is modeled
                  field_criteria {
                    negated: true
                    field_match {
                      name: "ethernet.dst_addr"
                      exact { mac: "ff:ff:ff:ff:ff:ff" }
                    }
                  }
                  # Avoid IPv4 packets with src IP 255.255.255.255 (broadcast).
                  # Per https://www.rfc-editor.org/rfc/rfc1812#section-5.3.7
                  # such packets are martian packets and should not be forwarded
                  # but some of our targets are not compliant so we avoid
                  # testing them.
                  # TODO: Remove when all targets are compliant.
                  field_criteria {
                    negated: true
                    field_match {
                      name: "ipv4.src_addr"
                      exact { ipv4: "255.255.255.255" }
                    }
                  }
                  field_criteria {
                    negated: true
                    field_match {
                      name: "inner_ipv4.src_addr"
                      exact { ipv4: "255.255.255.255" }
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
