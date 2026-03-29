// Golden test runner for TraceTree → PacketTrace conversion.
//
// Prints the input TraceTree, its conversion to PacketTrace, and a
// human-readable description for each test case. The output is diffed
// against a checked-in golden file.
//
// Update golden file:
//   bazel run //fourward:trace_conversion_golden_test -- --update

#include <iostream>
#include <string>
#include <vector>

#include "fourward/trace_conversion.h"
#include "google/protobuf/text_format.h"
#include "dvaas/packet_trace.pb.h"
#include "simulator.pb.h"

namespace dvaas {
namespace {

struct TestCase {
  std::string description;
  std::string trace_tree_textproto;
};

std::vector<TestCase> AllTestCases() {
  return {
      {
          .description = "Empty trace tree → empty packet trace.",
          .trace_tree_textproto = "",
      },
      {
          .description = "Table miss + mark_to_drop → TableApply(miss) + "
                         "MarkToDrop + Drop.",
          .trace_tree_textproto = R"pb(
            events {
              table_lookup {
                table_name: "ingress.routing.ipv4_table"
                hit: false
                action_name: "NoAction"
              }
            }
            events { mark_to_drop {} }
            packet_outcome { drop {} }
          )pb",
      },
      {
          .description =
              "Table hit → forward. Transmit carries port and packet size.",
          .trace_tree_textproto = R"pb(
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
          )pb",
      },
      {
          .description = "MarkToDrop preserves source_info as source_location.",
          .trace_tree_textproto = R"pb(
            events {
              mark_to_drop {}
              source_info {
                source_fragment: "mark_to_drop(standard_metadata)"
              }
            }
          )pb",
      },
      {
          .description = "Clone event → PacketReplication with count 1.",
          .trace_tree_textproto = R"pb(
            events { clone { session_id: 42 } }
          )pb",
      },
      {
          .description = "Clone fork (parallel): both branches appear in output.",
          .trace_tree_textproto = R"pb(
            fork_outcome {
              reason: CLONE
              branches {
                label: "original"
                subtree {
                  packet_outcome { output { p4rt_egress_port: "1" } }
                }
              }
              branches {
                label: "clone"
                subtree {
                  packet_outcome { output { p4rt_egress_port: "2" } }
                }
              }
            }
          )pb",
      },
      {
          .description = "Multicast fork (parallel): replication event with "
                         "count, then all replicas.",
          .trace_tree_textproto = R"pb(
            fork_outcome {
              reason: MULTICAST
              branches {
                label: "replica_0"
                subtree {
                  packet_outcome { output { p4rt_egress_port: "1" } }
                }
              }
              branches {
                label: "replica_1"
                subtree {
                  packet_outcome { output { p4rt_egress_port: "2" } }
                }
              }
              branches {
                label: "replica_2"
                subtree {
                  packet_outcome { output { p4rt_egress_port: "3" } }
                }
              }
            }
          )pb",
      },
      {
          .description = "Action selector fork (alternative): only the first "
                         "branch appears.",
          .trace_tree_textproto = R"pb(
            fork_outcome {
              reason: ACTION_SELECTOR
              branches {
                label: "member_0"
                subtree {
                  packet_outcome { output { p4rt_egress_port: "1" } }
                }
              }
              branches {
                label: "member_1"
                subtree {
                  packet_outcome { output { p4rt_egress_port: "2" } }
                }
              }
            }
          )pb",
      },
      {
          .description =
              "Parser transitions, action executions, branch events, and "
              "extern calls are ignored (no DVaaS equivalent).",
          .trace_tree_textproto = R"pb(
            events {
              parser_transition {
                parser_name: "parser"
                from_state: "start"
                to_state: "accept"
              }
            }
            events { action_execution { action_name: "set_dst_mac" } }
            events { branch { control_name: "ingress.acl" taken: true } }
            events {
              extern_call {
                extern_instance_name: "counter0"
                method: "count"
              }
            }
          )pb",
      },
      {
          .description = "Events before a clone fork are preserved in the "
                         "flattened output.",
          .trace_tree_textproto = R"pb(
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
                subtree {
                  packet_outcome { output { p4rt_egress_port: "1" } }
                }
              }
              branches {
                label: "clone"
                subtree {
                  packet_outcome { output { p4rt_egress_port: "2" } }
                }
              }
            }
          )pb",
      },
      {
          .description = "Nested forks are fully flattened: clone → multicast.",
          .trace_tree_textproto = R"pb(
            fork_outcome {
              reason: CLONE
              branches {
                label: "original"
                subtree {
                  packet_outcome { output { p4rt_egress_port: "1" } }
                }
              }
              branches {
                label: "clone"
                subtree {
                  fork_outcome {
                    reason: MULTICAST
                    branches {
                      label: "replica_0"
                      subtree {
                        packet_outcome {
                          output { p4rt_egress_port: "2" }
                        }
                      }
                    }
                    branches {
                      label: "replica_1"
                      subtree {
                        packet_outcome {
                          output { p4rt_egress_port: "3" }
                        }
                      }
                    }
                  }
                }
              }
            }
          )pb",
      },
  };
}

}  // namespace
}  // namespace dvaas

int main() {
  for (const dvaas::TestCase& test_case : dvaas::AllTestCases()) {
    std::cout << std::string(72, '=') << std::endl;
    std::cout << "Description: " << test_case.description << std::endl;
    std::cout << std::string(72, '-') << std::endl;

    fourward::sim::TraceTree trace_tree;
    if (!test_case.trace_tree_textproto.empty()) {
      google::protobuf::TextFormat::ParseFromString(
          test_case.trace_tree_textproto, &trace_tree);
    }

    std::string input_text;
    google::protobuf::TextFormat::PrintToString(trace_tree, &input_text);
    std::cout << "Input TraceTree:" << std::endl;
    if (input_text.empty()) {
      std::cout << "  (empty)" << std::endl;
    } else {
      std::cout << input_text;
    }

    std::cout << std::string(72, '-') << std::endl;

    dvaas::PacketTrace result = dvaas::FourwardTraceTreeToDvaasPacketTrace(trace_tree);

    std::string output_text;
    google::protobuf::TextFormat::PrintToString(result, &output_text);
    std::cout << "Output PacketTrace:" << std::endl;
    if (output_text.empty()) {
      std::cout << "  (empty)" << std::endl;
    } else {
      std::cout << output_text;
    }
  }
  return 0;
}
