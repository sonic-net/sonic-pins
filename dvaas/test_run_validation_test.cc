#include "dvaas/test_run_validation.h"

#include "dvaas/test_vector.pb.h"
#include "google/protobuf/descriptor.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h" // IWYU pragma: keep
#include "gutil/testing.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace dvaas {
namespace {

using ::gutil::EqualsProto;
using ::testing::HasSubstr;

TEST(TestRunValidationTest,
     PacketFieldIsIgnoredIfAndOnlyIfIncludedInIgnoredPacketlibFields) {
  const PacketTestRun test_run = gutil::ParseProtoOrDie<PacketTestRun>(R"pb(
    test_vector {
      acceptable_outputs {
        packets {
          port: "1"
          parsed { headers { ethernet_header { ethertype: "0x0888" } } }
        }
      }
    }
    actual_output {
      packets {
        port: "1"
        parsed { headers { ethernet_header { ethertype: "0x0111" } } }
      }
    }
  )pb");

  // Without ignoring ethertype, validation must fail.
  ASSERT_THAT(ValidateTestRun(test_run).failure().description(),
              HasSubstr("modified:"));

  const google::protobuf::FieldDescriptor* ethertype_field_descriptor =
      packetlib::EthernetHeader::descriptor()->FindFieldByName("ethertype");
  ASSERT_THAT(ethertype_field_descriptor, testing::NotNull());

  // Ignoring ethertype, validation must succeed.
  ASSERT_THAT(ValidateTestRun(
                  test_run,
                  {
                      .ignored_packetlib_fields = {ethertype_field_descriptor},
                  }),
              EqualsProto(R"pb()pb"));
}
// When a header is ignored via ignored_packetlib_fields, none of the field
// of the ignored header in actual_output is checked against acceptable_outputs.
TEST(TestRunValidationTest, IgnoringEntireHeaderIgnoresAllHeaderFields) {
  const PacketTestRun test_run = gutil::ParseProtoOrDie<PacketTestRun>(R"pb(
    test_vector {
      acceptable_outputs {
        packets {
          port: "1"
          parsed {
            headers {
              ipfix_header {
                version: "v1"
                export_time: "1234"
                sequence_number: "4321"
              }
            }
          }
        }
      }
    }
    actual_output {
      packets {
        port: "1"
        parsed {
          headers {
            ipfix_header {
              version: "v2"
              export_time: "1234"
              sequence_number: "5678"
            }
          }
        }
      }
    }
  )pb");

  // Without ignoring IPFIX header, validation must fail.
  ASSERT_THAT(ValidateTestRun(test_run).failure().description(),
              HasSubstr("modified:"));

  const google::protobuf::FieldDescriptor* ipfix_header_descriptor =
      packetlib::Header::descriptor()->FindFieldByName("ipfix_header");
  ASSERT_THAT(ipfix_header_descriptor, testing::NotNull());

  // Ignoring IPFIX header, validation must succeed.
  ASSERT_THAT(
      ValidateTestRun(test_run,
                      {
                          .ignored_packetlib_fields = {ipfix_header_descriptor},
                      }),
      EqualsProto(R"pb()pb"));
}

// When a header is ignored via ignored_packetlib_fields, the header's presence
// is still checked and that header's absence is considered a failure.
TEST(TestRunValidationTest, IgnoringEntireHeaderStillChecksForPresence) {
  PacketTestRun test_run = gutil::ParseProtoOrDie<PacketTestRun>(R"pb(
    test_vector {
      acceptable_outputs {
        packets {
          port: "1"
          parsed {
            headers { ethernet_header { ethertype: "0x0888" } }
            headers { udp_header { source_port: "1234" } }
          }
        }
      }
    }
    actual_output {
      packets {
        port: "1"
        parsed { headers { ethernet_header { ethertype: "0x0888" } } }
      }
    }
  )pb");

  const google::protobuf::FieldDescriptor* udp_header_descriptor =
      packetlib::Header::descriptor()->FindFieldByName("udp_header");
  ASSERT_THAT(udp_header_descriptor, testing::NotNull());

  // Even though UDP header is ignored, the fact that it is missing in
  // actual_output is still considered a failure.
  ASSERT_THAT(
      ValidateTestRun(test_run,
                      {
                          .ignored_packetlib_fields = {udp_header_descriptor},
                      })
          .failure()
          .description(),
      HasSubstr("deleted:"));

  test_run = gutil::ParseProtoOrDie<PacketTestRun>(R"pb(
    test_vector {
      acceptable_outputs {
        packets {
          port: "1"
          parsed { headers { ethernet_header { ethertype: "0x0888" } } }
        }
      }
    }
    actual_output {
      packets {
        port: "1"
        parsed {
          headers { ethernet_header { ethertype: "0x0888" } }
          headers { udp_header { source_port: "1234" } }
        }
      }
    }
  )pb");
  // Even though UDP header is ignored, the fact that it is present in
  // actual_output is still considered a failure.
  ASSERT_THAT(
      ValidateTestRun(test_run,
                      {
                          .ignored_packetlib_fields = {udp_header_descriptor},
                      })
          .failure()
          .description(),
      HasSubstr("added:"));
}

TEST(TestRunValidationTest,
     PacketInFieldIsIgnoredIfAndOnlyIfIncludedInIgnoredPacketlibFields) {
  const PacketTestRun test_run = gutil::ParseProtoOrDie<PacketTestRun>(R"pb(
    test_vector {
      acceptable_outputs {
        packet_ins {
          parsed { headers { ethernet_header { ethertype: "0x0888" } } }
        }
      }
    }
    actual_output {
      packet_ins {
        parsed { headers { ethernet_header { ethertype: "0x0111" } } }
      }
    }
  )pb");

  // Without ignoring ethertype, validation must fail.
  ASSERT_THAT(ValidateTestRun(test_run).failure().description(),
              HasSubstr("modified:"));

  const google::protobuf::FieldDescriptor* ethertype_field_descriptor =
      packetlib::EthernetHeader::descriptor()->FindFieldByName("ethertype");
  ASSERT_THAT(ethertype_field_descriptor, testing::NotNull());

  // Ignoring ethertype, validation must succeed.
  ASSERT_THAT(ValidateTestRun(
                  test_run,
                  {
                      .ignored_packetlib_fields = {ethertype_field_descriptor},
                  }),
              EqualsProto(R"pb()pb"));
}

TEST(TestRunValidationTest,
     PacketInMetadataIsIgnoredIfAndOnlyIfIncludedInIgnoredPacketinMetadata) {
  const PacketTestRun test_run = gutil::ParseProtoOrDie<PacketTestRun>(R"pb(
    test_vector {
      acceptable_outputs {
        packet_ins {
          metadata {
            name: "target_egress_port"
            value { str: "1" }
          }
        }
      }
    }
    actual_output {
      packet_ins {
        metadata {
          name: "target_egress_port"
          value { str: "2" }
        }
      }
    }
  )pb");

  // Without ignoring target_egress_port, validation must fail.
  ASSERT_THAT(ValidateTestRun(test_run).failure().description(),
              HasSubstr("modified:"));

  // Ignoring target_egress_port, validation must succeed.
  ASSERT_THAT(
      ValidateTestRun(test_run,
                      {
                          .ignored_packet_in_metadata = {"target_egress_port"},
                      }),
      EqualsProto(R"pb()pb"));
}

TEST(TestRunValidationTest,
     DifferenceBetweenPortsInActualAndAcceptableOutputLeadToFailure) {
  // Without ignoring target_egress_port, validation must fail.
  ASSERT_THAT(ValidateTestRun(gutil::ParseProtoOrDie<PacketTestRun>(R"pb(
                test_vector { acceptable_outputs { packets { port: "1" } } }
                actual_output { packets { port: "2" } }
              )pb"))
                  .failure()
                  .description(),
              HasSubstr("mismatched ports:"));
}

TEST(TestRunValidationTest, DifferentPortOrderOfPacketsIsOk) {
  EXPECT_FALSE(ValidateTestRun(gutil::ParseProtoOrDie<PacketTestRun>(R"pb(
                 test_vector {
                   acceptable_outputs {
                     packets { port: "1" }
                     packets { port: "2" }
                   }
                 }
                 actual_output {
                   packets { port: "2" }
                   packets { port: "1" }
                 }
               )pb"))
                   .has_failure());
}

TEST(TestRunValidationTest,
     MissingPacketInsAreIgnoredIfAndOnlyIfIgnorePacketInsIsSet) {
  const PacketTestRun test_run = gutil::ParseProtoOrDie<PacketTestRun>(R"pb(
    test_vector {
      acceptable_outputs {
        packets { port: "1" }
        packet_ins {
          metadata {
            name: "target_egress_port"
            value { str: "1" }
          }
        }
      }
    }
    actual_output { packets { port: "1" } }
  )pb");

  // Without ignoring packet-ins, validation must fail.
  ASSERT_THAT(ValidateTestRun(test_run).failure().description(),
              HasSubstr("packet in"));

  // Ignoring packet-ins, validation must succeed.
  ASSERT_THAT(
      ValidateTestRun(
          test_run,
          {
              .treat_expected_and_actual_outputs_as_having_no_packet_ins = true,
          }),
      EqualsProto(R"pb()pb"));
}

TEST(TestRunValidationTest,
     PacketInDifferencesAreIgnoredIfAndOnlyIfIgnorePacketInsIsSet) {
  const PacketTestRun test_run = gutil::ParseProtoOrDie<PacketTestRun>(R"pb(
    test_vector {
      acceptable_outputs {
        packets { port: "1" }
        packet_ins {
          metadata {
            name: "target_egress_port"
            value { str: "1" }
          }
        }
      }
    }
    actual_output {
      packets { port: "1" }
      packet_ins {
        metadata {
          name: "target_egress_port"
          value { str: "2" }
        }
      }
    }
  )pb");

  // Without ignoring packet-ins, validation must fail.
  ASSERT_THAT(ValidateTestRun(test_run).failure().description(),
              HasSubstr("target_egress_port"));

  // Ignoring packet-ins, validation must succeed.
  ASSERT_THAT(
      ValidateTestRun(
          test_run,
          {
              .treat_expected_and_actual_outputs_as_having_no_packet_ins = true,
          }),
      EqualsProto(R"pb()pb"));
}

TEST(TestRunValidationTest, IgnorePacketInsHasNoEffectWhenPacketInsMatch) {
  ASSERT_THAT(
      ValidateTestRun(
          gutil::ParseProtoOrDie<PacketTestRun>(R"pb(
            test_vector {
              acceptable_outputs {
                packets { port: "1" }
                packet_ins {
                  metadata {
                    name: "target_egress_port"
                    value { str: "1" }
                  }
                }
              }
            }
            actual_output {
              packets { port: "1" }
              packet_ins {
                metadata {
                  name: "target_egress_port"
                  value { str: "1" }
                }
              }
            }
          )pb"),
          {
              .treat_expected_and_actual_outputs_as_having_no_packet_ins = true,
          }),
      EqualsProto(R"pb()pb"));
}

TEST(TestRunValidationTest, PacketFieldReasonsInvalidIsIgnored) {
  const PacketTestRun test_run = gutil::ParseProtoOrDie<PacketTestRun>(R"pb(
    test_vector {
      acceptable_outputs {
        packets {
          port: "1"
          parsed {
            reasons_invalid: "invalid reason 1"
            reasons_invalid: "invalid reason 2"
          }
        }
      }
    }
    actual_output {
      packets {
        port: "1"
        parsed {}
      }
    }
  )pb");

  // Validation must succeed.
  ASSERT_THAT(ValidateTestRun(test_run), EqualsProto(R"pb()pb"));
}

}  // namespace
}  // namespace dvaas
