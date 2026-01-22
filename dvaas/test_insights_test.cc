#include "dvaas/test_insights.h"

#include <iostream>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/str_split.h"
#include "dvaas/test_vector.pb.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "p4_pdpi/ir.pb.h"

namespace dvaas {
namespace {

TEST(GetTestInsightsTableAsCsvTest, CsvHasAsManyRowsAsTestOutcomesPlusHeader) {
  ASSERT_OK_AND_ASSIGN(
      const std::string csv,
      GetTestInsightsTableAsCsv(
          gutil::ParseProtoOrDie<PacketTestOutcomes>(
              R"pb(outcomes {
                     test_run {
                       test_vector {
                         input {
                           packet {
                             parsed { headers { ethernet_header {} } }
                             hex: "74657374207061636b65742023313a2064756d6d79"
                           }
                         }
                       }
                     }
                   }
                   outcomes {
                     test_run {
                       test_vector {
                         input {
                           packet {
                             parsed { headers { ethernet_header {} } }
                             hex: "74657374207061636b65742023313a2064756d6d79"
                           }
                         }
                       }
                     }
                   })pb"),
          gutil::ParseProtoOrDie<pdpi::IrP4Info>(R"pb()pb")));
  // Expect # test outcomes + 1 (header) + 1 (new line at the end) rows.
  ASSERT_THAT(std::vector<std::string>(absl::StrSplit(csv, "\n")),
              testing::SizeIs(4));
}

TEST(GetTestInsightsTableAsCsvTest,
     ToleratesCyclesInPacketTraceTableApplicationOrder) {
  ASSERT_THAT(
      GetTestInsightsTableAsCsv(
          gutil::ParseProtoOrDie<PacketTestOutcomes>(
              R"pb(outcomes {
                     test_run {
                       test_vector {
                         input {
                           packet {
                             parsed { headers { ethernet_header {} } }
                             hex: "74657374207061636b65742023313a2064756d6d79"
                           }
                         }
                         acceptable_outputs {
                           packet_trace {
                             events { table_apply { table_name: "table1" } }
                             events { table_apply { table_name: "table1" } }
                           }
                         }
                       }
                     }
                   })pb"),
          gutil::ParseProtoOrDie<pdpi::IrP4Info>(R"pb()pb")),
      gutil::StatusIs(absl::StatusCode::kOk));
}

TEST(GetTestInsightsTableAsCsvTest, GoldenTest) {
  const auto test_outcomes = gutil::ParseProtoOrDie<PacketTestOutcomes>(
      R"pb(
        outcomes {
          test_run {
            test_vector {
              input {
                type: DATAPLANE
                packet {
                  port: "16"
                  parsed {
                    headers {
                      ethernet_header {
                        ethernet_destination: "fd:ff:fe:ff:ff:ff"
                        ethernet_source: "02:00:01:00:00:00"
                        ethertype: "0x86dd"
                      }
                    }
                    headers {
                      ipv6_header {
                        version: "0x6"
                        dscp: "0x00"
                        ecn: "0x0"
                        flow_label: "0x00000"
                        payload_length: "0x01d7"
                        next_header: "0x11"
                        hop_limit: "0x40"
                        ipv6_source: "2000::"
                        ipv6_destination: "2002:af4:ea7e:19::2"
                      }
                    }
                    headers {
                      udp_header {
                        source_port: "0x0000"
                        destination_port: "0x0222"
                        length: "0x01d7"
                        checksum: "0xbb29"
                      }
                    }
                    payload: "test packet #1: dummy"
                  }
                  hex: "74657374207061636b65742023313a2064756d6d79"
                }
              }
              acceptable_outputs {
                packet_trace {
                  events {
                    table_apply {
                      table_name: "table_1"
                      miss {}
                    }
                  }
                  events {
                    table_apply {
                      table_name: "table_2"
                      hit {
                        table_entry {
                          table_name: "action_1"
                          matches {
                            name: "field_1"
                            optional { value { hex_str: "0x1" } }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
            actual_output {}
          }
          test_result {}
        }
        outcomes {
          test_run {
            test_vector {
              input {
                type: SUBMIT_TO_INGRESS
                packet {
                  port: "20"
                  parsed {
                    headers {
                      ethernet_header {
                        ethernet_destination: "aa:aa:aa:aa:aa:aa"
                        ethernet_source: "02:00:01:00:00:00"
                        ethertype: "0x8833"
                      }
                    }
                    payload: "test packet #2: dummy"
                  }
                  hex: "74657374207061636b65742023323a2064756d6d79"
                }
              }
              acceptable_outputs {}
            }
            actual_output { packets {} }
          }
          test_result { failure {} }
        })pb");
  ASSERT_OK_AND_ASSIGN(
      const std::string csv,
      GetTestInsightsTableAsCsv(test_outcomes,
                                gutil::ParseProtoOrDie<pdpi::IrP4Info>(R"pb(
                                  tables_by_name {
                                    key: "table_1"
                                    value { preamble { id: 1 name: "table_1" } }
                                  }
                                  tables_by_name {
                                    key: "table_2"
                                    value { preamble { id: 2 name: "table_2" } }
                                  }
                                  # Internal table (no ID). Should be ignored.
                                  tables_by_name {
                                    key: "internal_table"
                                    value {}
                                  }
                                  tables_by_name {
                                    key: "table_3"
                                    value { preamble { id: 3 name: "table_3" } }
                                  }
                                )pb")));
  std::cout << "== Input ====================\n"
            << gutil::PrintTextProto(test_outcomes);
  std::cout << "== Output ====================\n" << csv;
}

}  // namespace
}  // namespace dvaas
