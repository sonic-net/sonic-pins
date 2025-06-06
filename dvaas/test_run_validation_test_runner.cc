// Copyright 2024 Google LLC
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
#include <string>
#include <vector>

#include "absl/status/statusor.h"
#include "dvaas/test_run_validation.h"
#include "dvaas/test_vector.pb.h"
#include "glog/logging.h"
#include "gutil/gutil/testing.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4_infra/packetlib/packetlib.pb.h"

namespace dvaas {
namespace {

using ::gutil::ParseProtoOrDie;

// A test case for the `ValidateTestRun` function.
struct TestCase {
  // Human-readable description of this test case, for documentation.
  std::string description;
  // The inputs to the `ValidateTestRun` function to be
  // used by this test case.
  PacketTestVector test_vector;
  SwitchOutput actual_output;
  SwitchOutputDiffParams diff_params;
};

// Defines and returns test cases (i.e., inputs) for the
// `ValidateTestRun` oracle, which will produce error
// messages when given these inputs. Used to test the quality of the oracle's
// error messages.
std::vector<TestCase> TestCases() {
  std::vector<TestCase> tests;

  {
    TestCase& test = tests.emplace_back();
    test = TestCase{
        .description =
            "Packet is expected to be forwarded (out of one\nof several "
            "acceptable ports), but gets dropped.",
        .test_vector = ParseProtoOrDie<PacketTestVector>(R"pb(
          input {
            type: DATAPLANE
            packet {
              port: "1"
              parsed {
                headers {
                  ethernet_header {
                    ethernet_destination: "02:08:02:08:10:40"
                    ethernet_source: "40:04:10:04:04:20"
                    ethertype: "0x86dd"
                  }
                }
                headers {
                  ipv6_header {
                    version: "0x6"
                    dscp: "0x00"
                    ecn: "0x0"
                    flow_label: "0x00000"
                    payload_length: "0x00ee"
                    next_header: "0x3a"
                    hop_limit: "0x80"
                    ipv6_source: "fe80::"
                    ipv6_destination: "2002:a05:6860:4f00::"
                  }
                }
                headers {
                  icmp_header {
                    type: "0x00"
                    code: "0x00"
                    checksum: "0x1461"
                    rest_of_header: "0x00000000"
                  }
                }
                payload: "test packet"
              }
            }
          }
          # Acceptable outputs filled in below.
        )pb"),
        // The packet gets dropped -- no output.
        .actual_output = SwitchOutput(),
    };
    // We expect the packet to be forwarded unmodified, out of one of several
    // acceptable ports (due to WCMP, for example).
    for (std::string port : {"8", "12", "16", "20"}) {
      auto& acceptable_output =
          *test.test_vector.add_acceptable_outputs()->add_packets();
      acceptable_output = test.test_vector.input().packet();
      acceptable_output.set_port(port);
    }
  }

  {
    TestCase& test = tests.emplace_back();
    test = TestCase{
        .description =
            "Submit-to-ingress packet is expected to be\nforwarded and "
            "mirrored and punted, but doesn't get punted.",
        .test_vector = ParseProtoOrDie<PacketTestVector>(R"pb(
          input {
            type: SUBMIT_TO_INGRESS
            packet {
              port: "1"
              parsed {
                headers {
                  ethernet_header {
                    ethernet_destination: "02:08:02:08:10:40"
                    ethernet_source: "40:04:10:04:04:20"
                    ethertype: "0x86dd"
                  }
                }
                headers {
                  ipv6_header {
                    version: "0x6"
                    dscp: "0x00"
                    ecn: "0x0"
                    flow_label: "0x00000"
                    payload_length: "0x00ee"
                    next_header: "0x3a"
                    hop_limit: "0x80"
                    ipv6_source: "fe80::"
                    ipv6_destination: "2002:a05:6860:4f00::"
                  }
                }
                headers {
                  icmp_header {
                    type: "0x00"
                    code: "0x00"
                    checksum: "0x1461"
                    rest_of_header: "0x00000000"
                  }
                }
                payload: "test packet"
              }
            }
          }
          acceptable_outputs {
            # The mirrored (and encapsulated) packet.
            packets {
              port: "1"
              parsed {
                headers {
                  ethernet_header {
                    ethernet_destination: "00:1a:11:17:5f:80"
                    ethernet_source: "00:02:03:04:05:06"
                    ethertype: "0x0800"
                  }
                }
                headers {
                  ipv4_header {
                    version: "0x4"
                    ihl: "0x5"
                    dscp: "0x00"
                    ecn: "0x0"
                    total_length: "0x0116"
                    identification: "0x0000"
                    flags: "0x2"
                    fragment_offset: "0x0000"
                    ttl: "0x40"
                    protocol: "0x2f"
                    checksum: "0xbe0b"
                    ipv4_source: "10.206.196.0"
                    ipv4_destination: "172.20.0.203"
                  }
                }
                # Mirrored packets get encapsulated but packetlib does not parse
                # inner headers, hence the strange payload here containing the
                # encapsulated headers.
                payload: "\000\000\210\276\002\n\000 \000\000\002*\020\200\000\005\010\000Ex\000\360\000\000\000\000\020\375\323\372\n\000\000\000\n5\300jtest packet"
              }
            }
            # The forwarded packet.
            packets {
              port: "31"
              parsed {
                headers {
                  ethernet_header {
                    ethernet_destination: "00:1a:11:17:5f:80"
                    ethernet_source: "02:2a:10:00:00:06"
                    ethertype: "0x0800"
                  }
                }
                headers {
                  ipv4_header {
                    version: "0x4"
                    ihl: "0x5"
                    dscp: "0x1e"
                    ecn: "0x0"
                    total_length: "0x00f0"
                    identification: "0x0000"
                    flags: "0x0"
                    fragment_offset: "0x0000"
                    ttl: "0x0f"
                    protocol: "0xfd"
                    checksum: "0xd4fa"
                    ipv4_source: "10.0.0.0"
                    ipv4_destination: "10.53.192.106"
                  }
                }
                payload: "test packet"
              }
            }
            # The punted packet.
            packet_ins {
              metadata {
                name: "ingress_port"
                value: { str: "1" }
              }
              metadata {
                name: "target_egress_port"
                value: { str: "1" }
              }
              parsed {
                headers {
                  ethernet_header {
                    ethernet_destination: "02:0a:00:20:00:00"
                    ethernet_source: "02:2a:10:80:00:05"
                    ethertype: "0x0800"
                  }
                }
                headers {
                  ipv4_header {
                    version: "0x4"
                    ihl: "0x5"
                    dscp: "0x1e"
                    ecn: "0x0"
                    total_length: "0x00f0"
                    identification: "0x0000"
                    flags: "0x0"
                    fragment_offset: "0x0000"
                    ttl: "0x10"
                    protocol: "0xfd"
                    checksum: "0xd3fa"
                    ipv4_source: "10.0.0.0"
                    ipv4_destination: "10.53.192.106"
                  }
                }
                payload: "test packet"
              }
            }
          }
        )pb"),
    };
    // Actual output: the forwarded and mirrored packet, but not the punted
    // packet.
    *test.actual_output.mutable_packets() =
        test.test_vector.acceptable_outputs(0).packets();
  }

  {
    TestCase& test = tests.emplace_back();
    test = TestCase{
        .description =
            "Packet gets forwarded with an unexpected\nmodification of two "
            "header fields.",
        .test_vector = ParseProtoOrDie<PacketTestVector>(R"pb(
          input {
            type: DATAPLANE
            packet {
              port: "1"
              parsed {
                headers {
                  ethernet_header {
                    ethernet_destination: "02:03:04:05:06:07"
                    ethernet_source: "00:01:02:03:04:05"
                    ethertype: "0x0800"
                  }
                }
                headers {
                  ipv4_header {
                    version: "0x4"
                    ihl: "0x5"
                    dscp: "0x1c"
                    ecn: "0x0"
                    total_length: "0x012e"
                    identification: "0x0000"
                    flags: "0x0"
                    fragment_offset: "0x0000"
                    ttl: "0x20"
                    protocol: "0x11"
                    checksum: "0x1b62"
                    ipv4_source: "10.0.0.0"
                    ipv4_destination: "10.206.105.32"
                  }
                }
                headers {
                  udp_header {
                    source_port: "0x0000"
                    destination_port: "0x0000"
                    length: "0x011a"
                    checksum: "0xad82"
                  }
                }
                payload: "test packet"
              }
            }
          }
          # Acceptable outputs and actual output filled in below.
        )pb"),
        // Overridden below.
        .actual_output = SwitchOutput(),
    };

    // We expect the packet to be forwarded out of port 12 unmodified.
    auto& acceptable_output =
        *test.test_vector.add_acceptable_outputs()->add_packets();
    acceptable_output = test.test_vector.input().packet();
    acceptable_output.set_port("12");

    // The packet instead gets forwarded with two header field modifications.
    auto& actual_output = *test.actual_output.add_packets();
    actual_output = acceptable_output;
    actual_output.mutable_parsed()
        ->mutable_headers(1)
        ->mutable_ipv4_header()
        ->set_dscp("0x00");
    actual_output.mutable_parsed()
        ->mutable_headers(1)
        ->mutable_ipv4_header()
        ->set_checksum("0x0000");
  }
  {
    TestCase& test = tests.emplace_back();
    test = TestCase{
        .description =
            "Packet gets forwarded with an unexpected\nmodification of two "
            "header fields. This is the same test case as above,"
            "\nbut ethernet header is ignored and dscp field in ipv4"
            "\nis ignored by test_run_validation.",
        .test_vector = ParseProtoOrDie<PacketTestVector>(R"pb(
          input {
            type: DATAPLANE
            packet {
              port: "1"
              parsed {
                headers {
                  ethernet_header {
                    ethernet_destination: "02:03:04:05:06:07"
                    ethernet_source: "00:01:02:03:04:05"
                    ethertype: "0x0800"
                  }
                }
                headers {
                  ipv4_header {
                    version: "0x4"
                    ihl: "0x5"
                    dscp: "0x1c"
                    ecn: "0x0"
                    total_length: "0x012e"
                    identification: "0x0000"
                    flags: "0x0"
                    fragment_offset: "0x0000"
                    ttl: "0x20"
                    protocol: "0x11"
                    checksum: "0x1b62"
                    ipv4_source: "10.0.0.0"
                    ipv4_destination: "10.206.105.32"
                  }
                }
                headers {
                  udp_header {
                    source_port: "0x0000"
                    destination_port: "0x0000"
                    length: "0x011a"
                    checksum: "0xad82"
                  }
                }
                payload: "test packet"
              }
            }
          }
          # Acceptable outputs and actual output filled in below.
        )pb"),
        .actual_output = SwitchOutput(),
        .diff_params =
            {.ignored_packetlib_fields =
                 {
                     packetlib::Ipv4Header::descriptor()->FindFieldByName(
                         "checksum"),
                     packetlib::Header::descriptor()->FindFieldByName(
                         "udp_header"),
                 }},
    };

    // We expect the packet to be forwarded out of port 12 unmodified.
    auto& acceptable_output =
        *test.test_vector.add_acceptable_outputs()->add_packets();
    acceptable_output = test.test_vector.input().packet();
    acceptable_output.set_port("12");

    // The packet instead gets forwarded with three header field modifications.
    // Two of the mods are ignored but the DSCP modification will fail
    // the validation.
    auto& actual_output = *test.actual_output.add_packets();
    actual_output = acceptable_output;
    actual_output.mutable_parsed()
        ->mutable_headers(1)
        ->mutable_ipv4_header()
        ->set_checksum("0x0000");
    actual_output.mutable_parsed()
        ->mutable_headers(1)
        ->mutable_ipv4_header()
        ->set_dscp("0x00");
    // Erase UDP header's fields but the UDP header is still present.
    actual_output.mutable_parsed()->mutable_headers(2)->mutable_udp_header();
  }

  {
    TestCase& test = tests.emplace_back();
    test = TestCase{
        .description =
            "Packet gets forwarded with an unexpected\nmodification of two "
            "header fields. This is the same test case as above,\nbut many "
            "fields are ignored by test_run_validation."
            "\nOne of the modified field is ignored by test_run_validation.",
        .test_vector = ParseProtoOrDie<PacketTestVector>(R"pb(
          input {
            type: DATAPLANE
            packet {
              port: "1"
              parsed {
                headers {
                  ethernet_header {
                    ethernet_destination: "02:03:04:05:06:07"
                    ethernet_source: "00:01:02:03:04:05"
                    ethertype: "0x0800"
                  }
                }
                headers {
                  ipv4_header {
                    version: "0x4"
                    ihl: "0x5"
                    dscp: "0x1c"
                    ecn: "0x0"
                    total_length: "0x012e"
                    identification: "0x0000"
                    flags: "0x0"
                    fragment_offset: "0x0000"
                    ttl: "0x20"
                    protocol: "0x11"
                    checksum: "0x1b62"
                    ipv4_source: "10.0.0.0"
                    ipv4_destination: "10.206.105.32"
                  }
                }
                headers {
                  udp_header {
                    source_port: "0x0000"
                    destination_port: "0x0000"
                    length: "0x011a"
                    checksum: "0xad82"
                  }
                }
                payload: "test packet"
              }
            }
          }
          # Acceptable outputs and actual output filled in below.
        )pb"),
        // Overridden below.
        .actual_output = SwitchOutput(),
        .diff_params =
            {.ignored_packetlib_fields =
                 {
                     packetlib::Ipv4Header::descriptor()->FindFieldByName(
                         "dscp"),
                     packetlib::PsampHeader::descriptor()->FindFieldByName(
                         "length"),
                     packetlib::UdpHeader::descriptor()->FindFieldByName(
                         "source_port"),
                 }},
    };

    // We expect the packet to be forwarded out of port 12 unmodified.
    auto& acceptable_output =
        *test.test_vector.add_acceptable_outputs()->add_packets();
    acceptable_output = test.test_vector.input().packet();
    acceptable_output.set_port("12");

    // The packet instead gets forwarded with two header field modifications.
    auto& actual_output = *test.actual_output.add_packets();
    actual_output = acceptable_output;
    actual_output.mutable_parsed()
        ->mutable_headers(1)
        ->mutable_ipv4_header()
        ->set_dscp("0x00");
    actual_output.mutable_parsed()
        ->mutable_headers(1)
        ->mutable_ipv4_header()
        ->set_checksum("0x0000");
  }

  {
    TestCase& test = tests.emplace_back();
    test = TestCase{
        .description = "Packet gets forwarded with an unexpected port.",
        .test_vector = ParseProtoOrDie<PacketTestVector>(R"pb(
          input {
            type: DATAPLANE
            packet {
              port: "1"
              parsed {
                headers {
                  ethernet_header {
                    ethernet_destination: "02:03:04:05:06:07"
                    ethernet_source: "00:01:02:03:04:05"
                    ethertype: "0x0888"
                  }
                }
                payload: "test packet"
              }
            }
          }
          # Acceptable outputs and actual output filled in below.
        )pb"),
        // Overridden below.
        .actual_output = SwitchOutput(),
    };

    // Set expected packet to be forwarded out of port 12.
    Packet& acceptable_output =
        *test.test_vector.add_acceptable_outputs()->add_packets();
    acceptable_output = test.test_vector.input().packet();
    acceptable_output.set_port("12");

    // Set actual packet to be forwarded out of port 15.
    Packet& actual_output = *test.actual_output.add_packets();
    actual_output = acceptable_output;
    actual_output.set_port("15");
  }

  {
    TestCase& test = tests.emplace_back();
    test = TestCase{
        .description = "Packet gets punted with wrong metadata.",
        .test_vector = ParseProtoOrDie<PacketTestVector>(R"pb(
          input {
            type: DATAPLANE
            packet {
              port: "1"
              parsed {
                headers {
                  ethernet_header {
                    ethernet_destination: "02:03:04:05:06:07"
                    ethernet_source: "00:01:02:03:04:05"
                    ethertype: "0x0888"
                  }
                }
                payload: "test packet"
              }
            }
          }
          acceptable_outputs {
            packet_ins {
              metadata {
                name: "ingress_port"
                value: { str: "1" }
              }
              metadata {
                name: "target_egress_port"
                value: { str: "2" }
              }
              parsed: {}  # Filled in below.
            }
          }
          # Acceptable outputs and actual output filled in below.
        )pb"),
        // Overridden below.
        .actual_output = SwitchOutput(),
    };

    // Complete expected output.
    PacketIn& acceptable_output =
        *test.test_vector.mutable_acceptable_outputs(0)->mutable_packet_ins(0);
    *acceptable_output.mutable_parsed() =
        test.test_vector.input().packet().parsed();

    // Set 'target_egress_port' in actual packet to 3.
    PacketIn& actual_output = *test.actual_output.add_packet_ins();
    actual_output = acceptable_output;
    actual_output.mutable_metadata(1)->mutable_value()->set_str("3");
  }

  return tests;
}

void main() {
  for (auto& test : TestCases()) {
    PacketTestRun test_run;
    *test_run.mutable_test_vector() = test.test_vector;
    *test_run.mutable_actual_output() = test.actual_output;
    absl::StatusOr<PacketTestValidationResult> result =
        ValidateTestRun(test_run, test.diff_params);
    CHECK_OK(result.status());    // Crash OK: this is test code.
    CHECK(result->has_failure())  // Crash OK: this is test code.
        << "for test case with description '" << test.description << "'";
    std::cout << std::string(80, '=')
              << "\nValidateTestRun Test: " << test.description << "\n"
              << std::string(80, '=') << "\n"
              << result->failure().description() << "\n\n";
  }
}

}  // namespace
}  // namespace dvaas

int main() { dvaas::main(); }
