#include "fourward/trace_conversion.h"

#include "dvaas/packet_trace.pb.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "simulator.pb.h"

namespace dvaas {
namespace {

using ::gutil::EqualsProto;

fourward::sim::TraceTree ParseTraceTree(const std::string& textproto) {
  fourward::sim::TraceTree tree;
  EXPECT_TRUE(google::protobuf::TextFormat::ParseFromString(textproto, &tree))
      << "Failed to parse TraceTree: " << textproto;
  return tree;
}

TEST(TraceConversionTest, EmptyTraceTreeProducesEmptyPacketTrace) {
  PacketTrace trace = FourwardTraceTreeToDvaasPacketTrace(fourward::sim::TraceTree());
  EXPECT_EQ(trace.events_size(), 0);
}

TEST(TraceConversionTest, TableMiss) {
  fourward::sim::TraceTree tree = ParseTraceTree(R"pb(
    events {
      table_lookup {
        table_name: "ingress.acl.acl_ingress_table"
        hit: false
        action_name: "NoAction"
      }
    }
  )pb");

  PacketTrace trace = FourwardTraceTreeToDvaasPacketTrace(tree);

  ASSERT_EQ(trace.events_size(), 1);
  EXPECT_TRUE(trace.events(0).has_table_apply());
  EXPECT_EQ(trace.events(0).table_apply().table_name(),
            "ingress.acl.acl_ingress_table");
  EXPECT_TRUE(trace.events(0).table_apply().has_miss());
}

TEST(TraceConversionTest, TableHit) {
  fourward::sim::TraceTree tree = ParseTraceTree(R"pb(
    events {
      table_lookup {
        table_name: "ingress.routing.ipv4_table"
        hit: true
        action_name: "set_nexthop"
      }
    }
  )pb");

  PacketTrace trace = FourwardTraceTreeToDvaasPacketTrace(tree);

  ASSERT_EQ(trace.events_size(), 1);
  EXPECT_TRUE(trace.events(0).table_apply().has_hit());
  EXPECT_EQ(trace.events(0).table_apply().table_name(),
            "ingress.routing.ipv4_table");
}

TEST(TraceConversionTest, MarkToDrop) {
  fourward::sim::TraceTree tree = ParseTraceTree(R"pb(
    events { mark_to_drop {} }
  )pb");

  PacketTrace trace = FourwardTraceTreeToDvaasPacketTrace(tree);

  ASSERT_EQ(trace.events_size(), 1);
  EXPECT_TRUE(trace.events(0).has_mark_to_drop());
}

TEST(TraceConversionTest, MarkToDropWithSourceInfo) {
  fourward::sim::TraceTree tree = ParseTraceTree(R"pb(
    events {
      mark_to_drop {}
      source_info { source_fragment: "mark_to_drop(standard_metadata)" }
    }
  )pb");

  PacketTrace trace = FourwardTraceTreeToDvaasPacketTrace(tree);

  ASSERT_EQ(trace.events_size(), 1);
  EXPECT_EQ(trace.events(0).mark_to_drop().source_location(),
            "mark_to_drop(standard_metadata)");
}

TEST(TraceConversionTest, CloneEvent) {
  fourward::sim::TraceTree tree = ParseTraceTree(R"pb(
    events { clone { session_id: 42 } }
  )pb");

  PacketTrace trace = FourwardTraceTreeToDvaasPacketTrace(tree);

  ASSERT_EQ(trace.events_size(), 1);
  EXPECT_TRUE(trace.events(0).has_packet_replication());
  EXPECT_EQ(trace.events(0).packet_replication().number_of_packets_replicated(),
            1);
}

TEST(TraceConversionTest, DropOutcome) {
  fourward::sim::TraceTree tree = ParseTraceTree(R"pb(
    packet_outcome { drop {} }
  )pb");

  PacketTrace trace = FourwardTraceTreeToDvaasPacketTrace(tree);

  ASSERT_EQ(trace.events_size(), 1);
  EXPECT_TRUE(trace.events(0).has_drop());
}

TEST(TraceConversionTest, OutputOutcome) {
  fourward::sim::TraceTree tree = ParseTraceTree(R"pb(
    packet_outcome {
      output { p4rt_egress_port: "Ethernet0" payload: "hello" }
    }
  )pb");

  PacketTrace trace = FourwardTraceTreeToDvaasPacketTrace(tree);

  ASSERT_EQ(trace.events_size(), 1);
  EXPECT_TRUE(trace.events(0).has_transmit());
  EXPECT_EQ(trace.events(0).transmit().port(), "Ethernet0");
  EXPECT_EQ(trace.events(0).transmit().packet_size(), 5);
}

TEST(TraceConversionTest, ParserTransitionsAreIgnored) {
  fourward::sim::TraceTree tree = ParseTraceTree(R"pb(
    events {
      parser_transition {
        parser_name: "parser"
        from_state: "start"
        to_state: "parse_ethernet"
      }
    }
    events {
      parser_transition {
        parser_name: "parser"
        from_state: "parse_ethernet"
        to_state: "accept"
      }
    }
  )pb");

  PacketTrace trace = FourwardTraceTreeToDvaasPacketTrace(tree);
  EXPECT_EQ(trace.events_size(), 0);
}

TEST(TraceConversionTest, ActionExecutionsAreIgnored) {
  fourward::sim::TraceTree tree = ParseTraceTree(R"pb(
    events { action_execution { action_name: "set_dst_mac" } }
  )pb");

  PacketTrace trace = FourwardTraceTreeToDvaasPacketTrace(tree);
  EXPECT_EQ(trace.events_size(), 0);
}

TEST(TraceConversionTest, BranchEventsAreIgnored) {
  fourward::sim::TraceTree tree = ParseTraceTree(R"pb(
    events { branch { control_name: "ingress.acl" taken: true } }
  )pb");

  PacketTrace trace = FourwardTraceTreeToDvaasPacketTrace(tree);
  EXPECT_EQ(trace.events_size(), 0);
}

TEST(TraceConversionTest, ExternCallsAreIgnored) {
  fourward::sim::TraceTree tree = ParseTraceTree(R"pb(
    events {
      extern_call { extern_instance_name: "counter0" method: "count" }
    }
  )pb");

  PacketTrace trace = FourwardTraceTreeToDvaasPacketTrace(tree);
  EXPECT_EQ(trace.events_size(), 0);
}

TEST(TraceConversionTest, CloneForkFollowsAllBranches) {
  fourward::sim::TraceTree tree = ParseTraceTree(R"pb(
    fork_outcome {
      reason: CLONE
      branches {
        label: "original"
        subtree { packet_outcome { output { p4rt_egress_port: "1" } } }
      }
      branches {
        label: "clone"
        subtree { packet_outcome { output { p4rt_egress_port: "2" } } }
      }
    }
  )pb");

  PacketTrace trace = FourwardTraceTreeToDvaasPacketTrace(tree);

  // Both branches should be present (parallel fork).
  ASSERT_EQ(trace.events_size(), 2);
  EXPECT_EQ(trace.events(0).transmit().port(), "1");
  EXPECT_EQ(trace.events(1).transmit().port(), "2");
}

TEST(TraceConversionTest, MulticastForkEmitsReplicationAndAllBranches) {
  fourward::sim::TraceTree tree = ParseTraceTree(R"pb(
    fork_outcome {
      reason: MULTICAST
      branches {
        label: "replica_0"
        subtree { packet_outcome { output { p4rt_egress_port: "1" } } }
      }
      branches {
        label: "replica_1"
        subtree { packet_outcome { output { p4rt_egress_port: "2" } } }
      }
      branches {
        label: "replica_2"
        subtree { packet_outcome { output { p4rt_egress_port: "3" } } }
      }
    }
  )pb");

  PacketTrace trace = FourwardTraceTreeToDvaasPacketTrace(tree);

  // Replication event + 3 transmit events.
  ASSERT_EQ(trace.events_size(), 4);
  EXPECT_TRUE(trace.events(0).has_packet_replication());
  EXPECT_EQ(trace.events(0).packet_replication().number_of_packets_replicated(),
            3);
  EXPECT_EQ(trace.events(1).transmit().port(), "1");
  EXPECT_EQ(trace.events(2).transmit().port(), "2");
  EXPECT_EQ(trace.events(3).transmit().port(), "3");
}

TEST(TraceConversionTest, ActionSelectorForkFollowsFirstBranchOnly) {
  fourward::sim::TraceTree tree = ParseTraceTree(R"pb(
    fork_outcome {
      reason: ACTION_SELECTOR
      branches {
        label: "member_0"
        subtree { packet_outcome { output { p4rt_egress_port: "1" } } }
      }
      branches {
        label: "member_1"
        subtree { packet_outcome { output { p4rt_egress_port: "2" } } }
      }
    }
  )pb");

  PacketTrace trace = FourwardTraceTreeToDvaasPacketTrace(tree);

  // Only the first branch (alternative fork).
  ASSERT_EQ(trace.events_size(), 1);
  EXPECT_EQ(trace.events(0).transmit().port(), "1");
}

TEST(TraceConversionTest, ActionSelectorForkWithNoBranchesProducesNothing) {
  fourward::sim::TraceTree tree = ParseTraceTree(R"pb(
    fork_outcome { reason: ACTION_SELECTOR }
  )pb");

  PacketTrace trace = FourwardTraceTreeToDvaasPacketTrace(tree);
  EXPECT_EQ(trace.events_size(), 0);
}

TEST(TraceConversionTest, FullDropTrace) {
  fourward::sim::TraceTree tree = ParseTraceTree(R"pb(
    events {
      table_lookup {
        table_name: "ingress.routing.ipv4_table"
        hit: false
        action_name: "NoAction"
      }
    }
    events { mark_to_drop {} }
    packet_outcome { drop {} }
  )pb");

  PacketTrace trace = FourwardTraceTreeToDvaasPacketTrace(tree);

  ASSERT_EQ(trace.events_size(), 3);
  EXPECT_TRUE(trace.events(0).has_table_apply());
  EXPECT_TRUE(trace.events(0).table_apply().has_miss());
  EXPECT_TRUE(trace.events(1).has_mark_to_drop());
  EXPECT_TRUE(trace.events(2).has_drop());
}

TEST(TraceConversionTest, FullForwardTrace) {
  fourward::sim::TraceTree tree = ParseTraceTree(R"pb(
    events {
      table_lookup {
        table_name: "ingress.routing.ipv4_table"
        hit: true
        action_name: "set_nexthop"
      }
    }
    packet_outcome {
      output { p4rt_egress_port: "Ethernet4" payload: "forwarded" }
    }
  )pb");

  PacketTrace trace = FourwardTraceTreeToDvaasPacketTrace(tree);

  ASSERT_EQ(trace.events_size(), 2);
  EXPECT_TRUE(trace.events(0).table_apply().has_hit());
  EXPECT_EQ(trace.events(1).transmit().port(), "Ethernet4");
  EXPECT_EQ(trace.events(1).transmit().packet_size(), 9);
}

TEST(TraceConversionTest, EventsBeforeCloneForkArePreserved) {
  fourward::sim::TraceTree tree = ParseTraceTree(R"pb(
    events {
      table_lookup {
        table_name: "ingress.routing.ipv4_table"
        hit: true
        action_name: "forward"
      }
    }
    events { clone { session_id: 1 } }
    fork_outcome {
      reason: CLONE
      branches {
        label: "original"
        subtree { packet_outcome { output { p4rt_egress_port: "1" } } }
      }
      branches {
        label: "clone"
        subtree { packet_outcome { output { p4rt_egress_port: "2" } } }
      }
    }
  )pb");

  PacketTrace trace = FourwardTraceTreeToDvaasPacketTrace(tree);

  // Table hit + clone replication + 2 transmits.
  ASSERT_EQ(trace.events_size(), 4);
  EXPECT_TRUE(trace.events(0).has_table_apply());
  EXPECT_TRUE(trace.events(1).has_packet_replication());
  EXPECT_EQ(trace.events(2).transmit().port(), "1");
  EXPECT_EQ(trace.events(3).transmit().port(), "2");
}

TEST(TraceConversionTest, NestedForksAreFlattened) {
  // Clone fork where one branch itself has a multicast fork.
  fourward::sim::TraceTree tree = ParseTraceTree(R"pb(
    fork_outcome {
      reason: CLONE
      branches {
        label: "original"
        subtree { packet_outcome { output { p4rt_egress_port: "1" } } }
      }
      branches {
        label: "clone"
        subtree {
          fork_outcome {
            reason: MULTICAST
            branches {
              label: "replica_0"
              subtree {
                packet_outcome { output { p4rt_egress_port: "2" } }
              }
            }
            branches {
              label: "replica_1"
              subtree {
                packet_outcome { output { p4rt_egress_port: "3" } }
              }
            }
          }
        }
      }
    }
  )pb");

  PacketTrace trace = FourwardTraceTreeToDvaasPacketTrace(tree);

  // original output + multicast replication + 2 multicast outputs.
  ASSERT_EQ(trace.events_size(), 4);
  EXPECT_EQ(trace.events(0).transmit().port(), "1");
  EXPECT_TRUE(trace.events(1).has_packet_replication());
  EXPECT_EQ(trace.events(1).packet_replication().number_of_packets_replicated(),
            2);
  EXPECT_EQ(trace.events(2).transmit().port(), "2");
  EXPECT_EQ(trace.events(3).transmit().port(), "3");
}

TEST(TraceConversionTest, Bmv2TextualLogIsEmpty) {
  fourward::sim::TraceTree tree = ParseTraceTree(R"pb(
    packet_outcome { drop {} }
  )pb");

  PacketTrace trace = FourwardTraceTreeToDvaasPacketTrace(tree);
  EXPECT_TRUE(trace.bmv2_textual_log().empty());
}

}  // namespace
}  // namespace dvaas
