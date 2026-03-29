#include "fourward/trace_summary.h"

#include <string>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/testing.h"
#include "simulator.pb.h"

namespace dvaas {
namespace {

using ::gutil::ParseProtoOrDie;
using ::testing::HasSubstr;
using ::testing::Not;

TEST(TraceSummaryTest, EmptyTrace) {
  std::string summary = SummarizeTrace(fourward::sim::TraceTree());
  EXPECT_THAT(summary, HasSubstr("Fate: UNKNOWN"));
}

TEST(TraceSummaryTest, TableHitAndMiss) {
  fourward::sim::TraceTree trace = ParseProtoOrDie<fourward::sim::TraceTree>(
      R"pb(
        events {
          table_lookup {
            table_name: "vrf_table"
            hit: true
            action_name: "no_action"
          }
        }
        events {
          table_lookup {
            table_name: "ipv4_table"
            hit: false
            action_name: "NoAction"
          }
        }
        packet_outcome { drop {} }
      )pb");

  std::string summary = SummarizeTrace(trace);
  EXPECT_THAT(summary, HasSubstr("vrf_table: HIT"));
  EXPECT_THAT(summary, HasSubstr("ipv4_table: MISS"));
  EXPECT_THAT(summary, HasSubstr("Fate: DROPPED"));
}

TEST(TraceSummaryTest, ForwardedPacket) {
  fourward::sim::TraceTree trace = ParseProtoOrDie<fourward::sim::TraceTree>(
      R"pb(
        events {
          table_lookup {
            table_name: "ipv4_table"
            hit: true
            action_name: "set_nexthop_id"
          }
        }
        packet_outcome {
          output { p4rt_egress_port: "Ethernet4" }
        }
      )pb");

  std::string summary = SummarizeTrace(trace);
  EXPECT_THAT(summary, HasSubstr("ipv4_table: HIT"));
  EXPECT_THAT(summary, HasSubstr("Fate: OUTPUT on port Ethernet4"));
}

TEST(TraceSummaryTest, DropWithCondition) {
  fourward::sim::TraceTree trace = ParseProtoOrDie<fourward::sim::TraceTree>(
      R"pb(
        events {
          branch { control_name: "ingress" taken: false }
          source_info { source_fragment: "local_metadata.admit_to_l3" }
        }
        events {
          mark_to_drop {}
          source_info {
            file: "routing.p4"
            line: 269
          }
        }
        packet_outcome { drop {} }
      )pb");

  std::string summary = SummarizeTrace(trace);
  EXPECT_THAT(summary, HasSubstr("mark_to_drop at routing.p4:269"));
  EXPECT_THAT(summary, HasSubstr("admit_to_l3"));
  EXPECT_THAT(summary, HasSubstr("Fate: DROPPED"));
}

TEST(TraceSummaryTest, BranchConditionShownBeforeDrop) {
  fourward::sim::TraceTree trace = ParseProtoOrDie<fourward::sim::TraceTree>(
      R"pb(
        events {
          branch { control_name: "ingress" taken: true }
          source_info { source_fragment: "headers.ipv4.isValid()" }
        }
        events {
          branch { control_name: "ingress" taken: false }
          source_info { source_fragment: "local_metadata.admit_to_l3" }
        }
        events {
          mark_to_drop {}
          source_info { file: "routing.p4" line: 42 }
        }
        packet_outcome { drop {} }
      )pb");

  std::string summary = SummarizeTrace(trace);
  // The last branch condition before mark_to_drop is shown.
  EXPECT_THAT(summary, HasSubstr("admit_to_l3 [false]"));
  EXPECT_THAT(summary, HasSubstr("mark_to_drop"));
}

TEST(TraceSummaryTest, ParserAndActionEventsAreFiltered) {
  fourward::sim::TraceTree trace = ParseProtoOrDie<fourward::sim::TraceTree>(
      R"pb(
        events {
          parser_transition {
            parser_name: "parser"
            from_state: "start"
            to_state: "accept"
          }
        }
        events { action_execution { action_name: "set_dst_mac" } }
        events { extern_call { extern_instance_name: "counter" method: "count" } }
        packet_outcome { drop {} }
      )pb");

  std::string summary = SummarizeTrace(trace);
  EXPECT_THAT(summary, Not(HasSubstr("parser")));
  EXPECT_THAT(summary, Not(HasSubstr("set_dst_mac")));
  EXPECT_THAT(summary, Not(HasSubstr("counter")));
  EXPECT_THAT(summary, HasSubstr("Fate: DROPPED"));
}

}  // namespace
}  // namespace dvaas
