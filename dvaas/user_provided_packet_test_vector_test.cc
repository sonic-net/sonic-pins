// Empowers users to specify custom packet test vectors that can be validated
// by DVaaS or Arriba.

// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "dvaas/user_provided_packet_test_vector.h"

#include <iostream>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "dvaas/test_vector.h"
#include "dvaas/test_vector.pb.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/collections.h"
#include "gutil/gutil/proto.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/status_matchers.h"
#include "gutil/gutil/testing.h"
#include "p4_infra/p4_pdpi/test_p4info.h"
#include "p4_infra/packetlib/packetlib.h"
#include "p4_infra/packetlib/packetlib.pb.h"

namespace dvaas {
namespace {

using ::gutil::IsOk;
using ::gutil::PrintTextProto;
using ::testing::Not;

struct TestCase {
  std::string description;
  std::vector<PacketTestVector> vectors;
};

absl::StatusOr<int> ExtractIdFromUserProvidedTestVector(
    packetlib::Packet packet) {
  RETURN_IF_ERROR(packetlib::UpdateAllComputedFields(packet).status());
  ASSIGN_OR_RETURN(std::string serialized_packet,
                   packetlib::RawSerializePacket(packet));
  ASSIGN_OR_RETURN(int id, ExtractIdFromTaggedPacket(serialized_packet));
  return id;
}

void RunTestCase(const TestCase& test_case) {
  // Print header.
  std::cout << std::string(80, '=') << "\n"
            << "InternalizeUserProvidedTestVectors Test: "
            << test_case.description << "\n"
            << std::string(80, '=') << "\n";

  // Print input.
  std::cout << "-- Input ---------------------------------------------------\n";
  for (int i = 0; i < test_case.vectors.size(); ++i) {
    std::cout << "-- Input Packet Test Vector #" << (i + 1) << " --\n"
              << PrintTextProto(test_case.vectors[i]);
  }
  std::cout << "\n";

  // Print output.
  std::cout << "-- Output --------------------------------------------------\n";
  pdpi::IrP4Info ir_p4info = pdpi::GetTestIrP4Info();
  absl::StatusOr<PacketTestVectorById> output =
      LegitimizeUserProvidedTestVectors(test_case.vectors, ir_p4info);
  if (!output.ok()) {
    // Print error without stack trace, for golden testing.
    std::cout << "ERROR: "
              << output.status().ToString(
                     absl::StatusToStringMode::kWithNoExtraData)
              << "\n\n";
    return;
  }

  // Print output vectors in order of input vectors.
  for (int i = 0; i < test_case.vectors.size(); ++i) {
    const PacketTestVector& original_vector = test_case.vectors[i];
    ASSERT_OK_AND_ASSIGN(int id,
                         ExtractIdFromUserProvidedTestVector(
                             original_vector.input().packet().parsed()));
    ASSERT_OK_AND_ASSIGN(const PacketTestVector* legitimized_vector,
                         gutil::FindPtrOrStatus(*output, id));
    ASSERT_OK_AND_ASSIGN(
        std::string diff,
        gutil::ProtoDiff(original_vector, *legitimized_vector));
    std::cout << "-- Internalized Packet Test Vector #" << (i + 1) << " --\n"
	      << "test packet ID extracted from payload: " << id << "\n"
              << "diff of internalized vector vs input vector:\n"
              << diff << "\n";
  }
  std::cout << "\n";
}

std::vector<TestCase> GetPositiveTestCases() {
  std::vector<TestCase> test_cases;

  test_cases.emplace_back() = TestCase{
      .description = "empty list of vectors",
      .vectors = {},
  };

  test_cases.emplace_back() = TestCase{
      .description = "single Ethernet packet expected to be dropped",
      .vectors =
          {
              gutil::ParseProtoOrDie<PacketTestVector>(R"pb(
                input {
                  type: DATAPLANE
                  packet {
                    port: "1"
                    parsed {
                      headers {
                        ethernet_header {
                          ethernet_destination: "ff:ee:dd:cc:bb:aa"
                          ethernet_source: "55:44:33:22:11:00"
                          ethertype: "0x0010"
                        }
                      }
                      payload: "test packet #42:"
                    }
                  }
                }
                acceptable_outputs {}
              )pb"),
          },
  };

  test_cases.emplace_back() = TestCase{
      .description = "single IPv6 packet expected to be forwarded",
      .vectors =
          {
              gutil::ParseProtoOrDie<PacketTestVector>(R"pb(
                input {
                  type: DATAPLANE
                  packet {
                    port: "1"
                    parsed {
                      headers {
                        ethernet_header {
                          ethernet_destination: "ff:ee:dd:cc:bb:aa"
                          ethernet_source: "55:44:33:22:11:00"
                          ethertype: "0x86dd"
                        }
                      }
                      headers {
                        ipv6_header {
                          version: "0x6"
                          dscp: "0x1b"
                          ecn: "0x1"
                          flow_label: "0x12345"
                          next_header: "0xfd"
                          hop_limit: "0xf2"
                          ipv6_source: "2001::2"
                          ipv6_destination: "2001::4"
                        }
                      }
                      payload: "test packet #42:"
                    }
                  }
                }
                acceptable_outputs {
                  packets {
                    port: "8"
                    parsed {
                      headers {
                        ethernet_header {
                          ethernet_destination: "1:2:3:4:5:6"
                          ethernet_source: "6:5:4:3:2:1"
                          ethertype: "0x86dd"
                        }
                      }
                      headers {
                        ipv6_header {
                          version: "0x6"
                          dscp: "0x1b"
                          ecn: "0x1"
                          flow_label: "0x12345"
                          next_header: "0xfd"
                          hop_limit: "0xf1"
                          ipv6_source: "2001::2"
                          ipv6_destination: "2001::4"
                        }
                      }
                      payload: "test packet #42:"
                    }
                  }
                }
              )pb"),
          },
  };

  test_cases.emplace_back() = TestCase{
      .description = "several packets with different IDs",
      .vectors =
          {
              gutil::ParseProtoOrDie<PacketTestVector>(R"pb(
                input {
                  type: DATAPLANE
                  packet {
                    port: "1"
                    parsed {
                      headers {
                        ethernet_header {
                          ethernet_destination: "42:42:42:42:42:42"
                          ethernet_source: "42:42:42:42:42:42"
                          ethertype: "0x0010"
                        }
                      }
                      payload: "test packet #42:"
                    }
                  }
                }
                acceptable_outputs {}
              )pb"),
              gutil::ParseProtoOrDie<PacketTestVector>(R"pb(
                input {
                  type: DATAPLANE
                  packet {
                    port: "1"
                    parsed {
                      headers {
                        ethernet_header {
                          ethernet_destination: "5:5:5:5:5:5"
                          ethernet_source: "5:5:5:5:5:5"
                          ethertype: "0x000f"
                        }
                      }
                      payload: "test packet #5:"
                    }
                  }
                }
                acceptable_outputs {}
              )pb"),
          },
  };

  test_cases.emplace_back() = TestCase{
      .description = "packet_in with matching tag",
      .vectors =
          {
              gutil::ParseProtoOrDie<PacketTestVector>(R"pb(
                input {
                  type: DATAPLANE
                  packet {
                    port: "1"
                    parsed {
                      headers {
                        ethernet_header {
                          ethernet_destination: "ff:ee:dd:cc:bb:aa"
                          ethernet_source: "55:44:33:22:11:00"
                          ethertype: "0x0010"
                        }
                      }
                      payload: "test packet #42:"
                    }
                  }
                }
                acceptable_outputs {
                  packet_ins {
                    metadata {
                      name: "ingress_port"
                      value: { hex_str: "0x00f" }
                    }
                    metadata {
                      name: "target_egress_port"
                      value: { str: "1" }
                    }
                    parsed {
                      headers {
                        ethernet_header {
                          ethernet_destination: "5:5:5:5:5:5"
                          ethernet_source: "5:5:5:5:5:5"
                          ethertype: "0x0010"
                        }
                      }
                      payload: "test packet #42:"
                    }
                  }
                }
              )pb"),
          },
  };

  test_cases.emplace_back() = TestCase{
      .description = "input type = SUBMIT_TO_INGRESS",
      .vectors =
          {
              gutil::ParseProtoOrDie<PacketTestVector>(R"pb(
                input {
                  type: SUBMIT_TO_INGRESS
                  packet {
                    parsed {
                      headers {
                        ethernet_header {
                          ethernet_destination: "ff:ee:dd:cc:bb:aa"
                          ethernet_source: "55:44:33:22:11:00"
                          ethertype: "0x0010"
                        }
                      }
                      payload: "test packet #42:"
                    }
                  }
                }
                acceptable_outputs {
                  packets {
                    parsed {
                      headers {
                        ethernet_header {
                          ethernet_destination: "ff:ee:dd:cc:bb:aa"
                          ethernet_source: "55:44:33:22:11:00"
                          ethertype: "0x0010"
                        }
                      }
                      payload: "test packet #42:"
                    }
                  }
                }
              )pb"),
          },
  };

  test_cases.emplace_back() = TestCase{
      .description = "input type = PACKET_OUT",
      .vectors =
          {
              gutil::ParseProtoOrDie<PacketTestVector>(R"pb(
                input {
                  type: PACKET_OUT
                  packet {
                    port: "1"
                    parsed {
                      headers {
                        ethernet_header {
                          ethernet_destination: "ff:ee:dd:cc:bb:aa"
                          ethernet_source: "55:44:33:22:11:00"
                          ethertype: "0x0010"
                        }
                      }
                      payload: "test packet #42:"
                    }
                  }
                }
                acceptable_outputs {
                  packets {
                    port: "1"
                    parsed {
                      headers {
                        ethernet_header {
                          ethernet_destination: "ff:ee:dd:cc:bb:aa"
                          ethernet_source: "55:44:33:22:11:00"
                          ethertype: "0x0010"
                        }
                      }
                      payload: "test packet #42:"
                    }
                  }
                }
              )pb"),
          },
  };
  return test_cases;
}

std::vector<TestCase> GetNegativeTestCases() {
  std::vector<TestCase> test_cases;

  test_cases.emplace_back() = TestCase{
      .description = "missing expectation",
      .vectors =
          {
              gutil::ParseProtoOrDie<PacketTestVector>(R"pb(
                input {
                  type: DATAPLANE
                  packet {
                    port: "1"
                    parsed {
                      headers {
                        ethernet_header {
                          ethernet_destination: "42:42:42:42:42:42"
                          ethernet_source: "42:42:42:42:42:42"
                          ethertype: "0x0010"
                        }
                      }
                      payload: "test packet #42:"
                    }
                  }
                }
              )pb"),
          },
  };

  test_cases.emplace_back() = TestCase{
      .description = "missing test packet ID",
      .vectors =
          {
              gutil::ParseProtoOrDie<PacketTestVector>(R"pb(
                input {
                  type: DATAPLANE
                  packet {
                    port: "1"
                    parsed {
                      headers {
                        ethernet_header {
                          ethernet_destination: "42:42:42:42:42:42"
                          ethernet_source: "42:42:42:42:42:42"
                          ethertype: "0x0002"
                        }
                      }
                      payload: "Hi"
                    }
                  }
                }
              )pb"),
          },
  };

  test_cases.emplace_back() = TestCase{
      .description = "inconsistent test packet ID in input vs output",
      .vectors =
          {
              gutil::ParseProtoOrDie<PacketTestVector>(R"pb(
                input {
                  type: DATAPLANE
                  packet {
                    port: "1"
                    parsed {
                      headers {
                        ethernet_header {
                          ethernet_destination: "42:42:42:42:42:42"
                          ethernet_source: "42:42:42:42:42:42"
                          ethertype: "0x0010"
                        }
                      }
                      payload: "test packet #42:"
                    }
                  }
                }
                acceptable_outputs {
                  packets {
                    port: "8"
                    parsed {
                      headers {
                        ethernet_header {
                          ethernet_destination: "5:5:5:5:5:5"
                          ethernet_source: "5:5:5:5:5:5"
                          ethertype: "0x0010"
                        }
                      }
                      payload: "test packet #24:"
                    }
                  }
                }
              )pb"),
          },
  };

  test_cases.emplace_back() = TestCase{
      .description = "several packets with same test packet ID",
      .vectors =
          {
              gutil::ParseProtoOrDie<PacketTestVector>(R"pb(
                input {
                  type: DATAPLANE
                  packet {
                    port: "1"
                    parsed {
                      headers {
                        ethernet_header {
                          ethernet_destination: "42:42:42:42:42:42"
                          ethernet_source: "42:42:42:42:42:42"
                          ethertype: "0x0010"
                        }
                      }
                      payload: "test packet #42:"
                    }
                  }
                }
                acceptable_outputs {}
              )pb"),
              gutil::ParseProtoOrDie<PacketTestVector>(R"pb(
                input {
                  type: DATAPLANE
                  packet {
                    port: "1"
                    parsed {
                      headers {
                        ethernet_header {
                          ethernet_destination: "5:5:5:5:5:5"
                          ethernet_source: "5:5:5:5:5:5"
                          ethertype: "0x0010"
                        }
                      }
                      payload: "test packet #42:"
                    }
                  }
                }
                acceptable_outputs {}
              )pb"),
          },
  };

  test_cases.emplace_back() = TestCase{
      .description = "invalid input packet",
      .vectors =
          {
              gutil::ParseProtoOrDie<PacketTestVector>(R"pb(
                input {
                  type: DATAPLANE
                  packet {
                    port: "1"
                    parsed {
                      headers {
                        ethernet_header {
                          ethernet_destination: "5:5:5:5:5:5"
                          ethernet_source: "5:5:5:5:5:5"
                          ethertype: "0x86dd"  # IPv6.
                        }
                      }
                      # Missing IPv6 header.
                      payload: "test packet #42:"
                    }
                  }
                }
                acceptable_outputs {}
              )pb"),
          },
  };

  test_cases.emplace_back() = TestCase{
      .description = "packet_in with mismatching tag",
      .vectors =
          {
              gutil::ParseProtoOrDie<PacketTestVector>(R"pb(
                input {
                  type: DATAPLANE
                  packet {
                    port: "1"
                    parsed {
                      headers {
                        ethernet_header {
                          ethernet_destination: "ff:ee:dd:cc:bb:aa"
                          ethernet_source: "55:44:33:22:11:00"
                          ethertype: "0x0010"
                        }
                      }
                      payload: "test packet #42:"
                    }
                  }
                }
                acceptable_outputs {
                  packet_ins {
                    metadata {
                      name: "ingress_port"
                      value: { hex_str: "0x00f" }
                    }
                    metadata {
                      name: "target_egress_port"
                      value: { str: "1" }
                    }
                    parsed {
                      headers {
                        ethernet_header {
                          ethernet_destination: "5:5:5:5:5:5"
                          ethernet_source: "5:5:5:5:5:5"
                          ethertype: "0x0010"
                        }
                      }
                      payload: "test packet #24:"
                    }
                  }
                }
              )pb"),
          },
  };

  test_cases.emplace_back() = TestCase{
      .description = "packet_in with malformed metadata",
      .vectors =
          {
              gutil::ParseProtoOrDie<PacketTestVector>(R"pb(
                input {
                  type: DATAPLANE
                  packet {
                    port: "1"
                    parsed {
                      headers {
                        ethernet_header {
                          ethernet_destination: "ff:ee:dd:cc:bb:aa"
                          ethernet_source: "55:44:33:22:11:00"
                          ethertype: "0x0010"
                        }
                      }
                      payload: "test packet #42:"
                    }
                  }
                }
                acceptable_outputs {
                  packet_ins {
                    metadata {
                      name: "foobar"
                      value: { str: "foobar" }
                    }
                    metadata {
                      name: "ingress_port"
                      value: { hex_str: "0x00f" }
                    }
                    metadata {
                      name: "target_egress_port"
                      value: { str: "1" }
                    }
                    parsed {
                      headers {
                        ethernet_header {
                          ethernet_destination: "5:5:5:5:5:5"
                          ethernet_source: "5:5:5:5:5:5"
                          ethertype: "0x0010"
                        }
                      }
                      payload: "test packet #24:"
                    }
                  }
                }
              )pb"),
          },
  };

  return test_cases;
}

TEST(InternalizeUserProvidedTestVectorsTest, PositiveTestCases) {
  pdpi::IrP4Info ir_p4info = pdpi::GetTestIrP4Info();
  for (TestCase test_case : GetPositiveTestCases()) {
    EXPECT_THAT(LegitimizeUserProvidedTestVectors(test_case.vectors, ir_p4info),
                IsOk());
    RunTestCase(test_case);
  }
}

TEST(InternalizeUserProvidedTestVectorsTest, NegativeTestCases) {
  pdpi::IrP4Info ir_p4info = pdpi::GetTestIrP4Info();
  for (TestCase test_case : GetNegativeTestCases()) {
    EXPECT_THAT(LegitimizeUserProvidedTestVectors(test_case.vectors, ir_p4info),
                Not(IsOk()));
    RunTestCase(test_case);
  }
}

}  // namespace
}  // namespace dvaas
