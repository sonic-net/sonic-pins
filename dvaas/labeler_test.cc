#include "dvaas/labeler.h"

#include "dvaas/packet_trace.pb.h"
#include "dvaas/test_vector.pb.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "p4_pdpi/ir.pb.h"

namespace dvaas {
namespace {

using ::testing::ElementsAre;
using ::testing::IsEmpty;

TEST(LabelerTest, TestVectorLabeledWithVlanTaggedInput) {
  ASSERT_OK_AND_ASSIGN(
      Labels labels,
      dvaas::VlanTaggedInputLabeler(
          gutil::ParseProtoOrDie<dvaas::PacketTestRun>(R"pb(
            test_vector {
              input {
                packet {
                  # Exclude unnecessary packet fields for testing.
                  parsed {
                    headers {
                      ethernet_header {
                        ethernet_destination: "02:03:04:05:06:07"
                        ethertype: "0x8100"  # VLAN
                      }
                    }
                    headers {
                      vlan_header {
                        vlan_identifier: "0x0",
                        ethertype: "0x0800"  # IPv4
                      }
                    }
                    headers {
                      ipv4_header { ipv4_destination: "192.168.100.1" }
                    }
                    payload: "VLAN tagged IPv4 packet."
                  }
                }
              }
            }
          )pb")));
  EXPECT_THAT(labels.labels(), ElementsAre("vlan_tagged_input"));
}

TEST(LabelerTest, TestVectorLabeledWithMulticastSrcMacInput) {
  ASSERT_OK_AND_ASSIGN(
      Labels labels,
      dvaas::MulticastSrcMacInputLabeler(
          gutil::ParseProtoOrDie<dvaas::PacketTestRun>(R"pb(
            test_vector {
              input {
                packet {
                  # Exclude unnecessary packet fields for testing.
                  parsed {
                    headers {
                      ethernet_header {
                        # Multicast MAC.
                        ethernet_source: "11:11:5e:05:06:07"
                      }
                    }
                    payload: "MAC multicast test packet."
                  }
                }
              }
            }
          )pb")));
  EXPECT_THAT(labels.labels(), ElementsAre("multicast_src_mac_input"));
}

TEST(LabelerTest, TestVectorLabeledWithIpv4MulticastInput) {
  ASSERT_OK_AND_ASSIGN(
      Labels labels,
      dvaas::UnicastDstMacMulticastDstIpInputLabeler(
          gutil::ParseProtoOrDie<dvaas::PacketTestRun>(R"pb(
            test_vector {
              input {
                packet {
                  # Exclude unnecessary packet fields for testing.
                  parsed {
                    headers {
                      ethernet_header {
                        # IPv4 Unicast MAC.
                        ethernet_destination: "00:00:5e:05:06:07"
                        ethertype: "0x0800"  # IPv4
                      }
                    }
                    headers {
                      ipv4_header {
                        # IPv4 Multicast IP.
                        ipv4_destination: "232.1.2.3"
                      }
                    }
                    payload: "IPv4 multicast test packet."
                  }
                }
              }
            }
          )pb")));
  EXPECT_THAT(labels.labels(),
              ElementsAre("unicast_dst_mac_multicast_dst_ip_input"));
}

TEST(LabelerTest, TestVectorLabeledWithIpv6MulticastInput) {
  ASSERT_OK_AND_ASSIGN(
      Labels labels,
      dvaas::UnicastDstMacMulticastDstIpInputLabeler(
          gutil::ParseProtoOrDie<dvaas::PacketTestRun>(R"pb(
            test_vector {
              input {
                packet {
                  # Exclude unnecessary packet fields for testing.
                  parsed {
                    headers {
                      ethernet_header {
                        # IPv6 Multicast MAC.
                        ethernet_destination: "00:33:04:05:06:07"
                        ethertype: "0x86dd"  # IPv6
                      }
                    }
                    headers {
                      ipv6_header {
                        # IPv6 Multicast IP.
                        ipv6_destination: "ff30::2"
                      }
                    }
                    payload: "IPv6 multicast test packet."
                  }
                }
              }
            }
          )pb")));
  EXPECT_THAT(labels.labels(),
              ElementsAre("unicast_dst_mac_multicast_dst_ip_input"));
}

TEST(LabelerTest, Ipv4TestVectorLabeledWithTtl01InputForwarding) {
  ASSERT_OK_AND_ASSIGN(
      Labels labels,
      dvaas::Ttl01InputForwardingLabeler(
          gutil::ParseProtoOrDie<dvaas::PacketTestRun>(R"pb(
            test_vector {
              input {
                packet {
                  # Exclude unnecessary packet fields for testing.
                  parsed { headers { ipv4_header { ttl: "0x00" } } }
                }
              }
              acceptable_outputs {
                packet_trace {
                  events {
                    table_apply {
                      table_name: "ipv4_table"
                      hit { table_entry { table_name: "ipv4_table" } }
                    }
                  }
                }
              }
            }
          )pb")));
  EXPECT_THAT(labels.labels(), ElementsAre("ttl_01_input_forward"));
}

TEST(LabelerTest, Ipv6TestVectorLabeledWithTtl01InputForwarding) {
  ASSERT_OK_AND_ASSIGN(
      Labels labels,
      dvaas::Ttl01InputForwardingLabeler(
          gutil::ParseProtoOrDie<dvaas::PacketTestRun>(R"pb(
            test_vector {
              input {
                packet {
                  # Exclude unnecessary packet fields for testing.
                  parsed { headers { ipv6_header { hop_limit: "0x00" } } }
                }
              }
              acceptable_outputs {
                packet_trace {
                  events {
                    table_apply {
                      table_name: "ipv6_table"
                      hit { table_entry { table_name: "ipv6_table" } }
                    }
                  }
                }
              }
            }
          )pb")));
  EXPECT_THAT(labels.labels(), ElementsAre("ttl_01_input_forward"));
}

TEST(LabelerTest, TestVectorWithNoLabelsUsingTtl01InputForwardingLabeler) {
  ASSERT_OK_AND_ASSIGN(
      Labels labels,
      dvaas::Ttl01InputForwardingLabeler(
          gutil::ParseProtoOrDie<dvaas::PacketTestRun>(R"pb(
            test_vector {
              input {
                packet {
                  # Exclude unnecessary packet fields for testing.
                  parsed { headers { ipv4_header { ttl: "0x00" } } }
                }
              }
              acceptable_outputs {
                packet_trace {
                  events {
                    table_apply {
                      table_name: "ipv4_table"
                      hit { table_entry { table_name: "ipv4_table" } }
                    }
                  }
                  events {
                    table_apply {
                      table_name: "acl_ingress_table"
                      hit { table_entry { table_name: "acl_ingress_table" } }
                    }
                  }
                }
              }
            }
          )pb")));
  EXPECT_THAT(labels.labels(), IsEmpty());
}

}  // namespace
}  // namespace dvaas
