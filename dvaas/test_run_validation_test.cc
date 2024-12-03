#include "dvaas/test_run_validation.h"

#include "dvaas/test_vector.pb.h"
#include "gmock/gmock.h"
#include "google/protobuf/descriptor.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/testing.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"

namespace dvaas {
namespace {

using gutil::EqualsProto;
using testing::HasSubstr;

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

}  // namespace
}  // namespace dvaas
