#include "dvaas/test_run_validation.h"

#include <optional>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "dvaas/switch_api.h"
#include "dvaas/test_vector.pb.h"
#include "gmock/gmock.h"
#include "google/protobuf/descriptor.h"
#include "google/protobuf/repeated_ptr_field.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "gutil/testing.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"

namespace dvaas {
namespace {

using ::gutil::EqualsProto;
using ::testing::HasSubstr;

TEST(TestRunValidationTest,
     PacketFieldIsIgnoredIfAndOnlyIfIncludedInIgnoredPacketlibFields) {
  PacketTestRun test_run = gutil::ParseProtoOrDie<PacketTestRun>(R"pb(
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
  ASSERT_OK_AND_ASSIGN(PacketTestValidationResult result,
                       ValidateTestRun(test_run));
  ASSERT_THAT(result.failure().description(), HasSubstr("modified:"));

  const google::protobuf::FieldDescriptor* ethertype_field_descriptor =
      packetlib::EthernetHeader::descriptor()->FindFieldByName("ethertype");
  ASSERT_THAT(ethertype_field_descriptor, testing::NotNull());

  // Ignoring ethertype, validation must succeed.
  ASSERT_OK_AND_ASSIGN(
      result, ValidateTestRun(
                  test_run,
                  SwitchOutputDiffParams{
                      .ignored_packetlib_fields = {ethertype_field_descriptor},
                  },
                  /*sut=*/nullptr));
  ASSERT_THAT(result, EqualsProto(R"pb()pb"));
}
// When a header is ignored via ignored_packetlib_fields, none of the field
// of the ignored header in actual_output is checked against acceptable_outputs.
TEST(TestRunValidationTest, IgnoringEntireHeaderIgnoresAllHeaderFields) {
  PacketTestRun test_run = gutil::ParseProtoOrDie<PacketTestRun>(R"pb(
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
  ASSERT_OK_AND_ASSIGN(PacketTestValidationResult result,
                       ValidateTestRun(test_run));
  ASSERT_THAT(result.failure().description(), HasSubstr("modified:"));

  const google::protobuf::FieldDescriptor* ipfix_header_descriptor =
      packetlib::Header::descriptor()->FindFieldByName("ipfix_header");
  ASSERT_THAT(ipfix_header_descriptor, testing::NotNull());

  // Ignoring IPFIX header, validation must succeed.
  ASSERT_OK_AND_ASSIGN(
      result,
      ValidateTestRun(test_run,
                      SwitchOutputDiffParams{
                          .ignored_packetlib_fields = {ipfix_header_descriptor},
                      },
                      /*sut=*/nullptr));
  ASSERT_THAT(result, EqualsProto(R"pb()pb"));
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
  ASSERT_OK_AND_ASSIGN(
      PacketTestValidationResult result,
      ValidateTestRun(test_run,
                      SwitchOutputDiffParams{
                          .ignored_packetlib_fields = {udp_header_descriptor},
                      },
                      /*sut=*/nullptr));
  ASSERT_THAT(result.failure().description(), HasSubstr("deleted:"));

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
  ASSERT_OK_AND_ASSIGN(
      result,
      ValidateTestRun(test_run,
                      SwitchOutputDiffParams{
                          .ignored_packetlib_fields = {udp_header_descriptor},
                      },
                      /*sut=*/nullptr));
  ASSERT_THAT(result.failure().description(), HasSubstr("added:"));
}

TEST(TestRunValidationTest,
     PacketInFieldIsIgnoredIfAndOnlyIfIncludedInIgnoredPacketlibFields) {
  PacketTestRun test_run = gutil::ParseProtoOrDie<PacketTestRun>(R"pb(
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
  ASSERT_OK_AND_ASSIGN(PacketTestValidationResult result,
                       ValidateTestRun(test_run));
  ASSERT_THAT(result.failure().description(), HasSubstr("modified:"));

  const google::protobuf::FieldDescriptor* ethertype_field_descriptor =
      packetlib::EthernetHeader::descriptor()->FindFieldByName("ethertype");
  ASSERT_THAT(ethertype_field_descriptor, testing::NotNull());

  // Ignoring ethertype, validation must succeed.
  ASSERT_OK_AND_ASSIGN(
      result, ValidateTestRun(
                  test_run,
                  SwitchOutputDiffParams{
                      .ignored_packetlib_fields = {ethertype_field_descriptor},
                  },
                  /*sut=*/nullptr));
  ASSERT_THAT(result, EqualsProto(R"pb()pb"));
}

TEST(TestRunValidationTest,
     PacketInMetadataIsIgnoredIfAndOnlyIfIncludedInIgnoredPacketinMetadata) {
  PacketTestRun test_run = gutil::ParseProtoOrDie<PacketTestRun>(R"pb(
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
  ASSERT_OK_AND_ASSIGN(PacketTestValidationResult result,
                       ValidateTestRun(test_run));
  ASSERT_THAT(result.failure().description(), HasSubstr("modified:"));

  // Ignoring target_egress_port, validation must succeed.
  ASSERT_OK_AND_ASSIGN(
      result,
      ValidateTestRun(test_run,
                      SwitchOutputDiffParams{
                          .ignored_packet_in_metadata = {"target_egress_port"},
                      },
                      /*sut=*/nullptr));
  ASSERT_THAT(result, EqualsProto(R"pb()pb"));
}

TEST(TestRunValidationTest,
     DifferenceBetweenPortsInActualAndAcceptableOutputLeadToFailure) {
  // Without ignoring target_egress_port, validation must fail.
  PacketTestRun test_run = gutil::ParseProtoOrDie<PacketTestRun>(R"pb(
    test_vector { acceptable_outputs { packets { port: "1" } } }
    actual_output { packets { port: "2" } }
  )pb");
  ASSERT_OK_AND_ASSIGN(PacketTestValidationResult result,
                       ValidateTestRun(test_run));
  ASSERT_THAT(result.failure().description(), HasSubstr("mismatched ports:"));
}

TEST(TestRunValidationTest, DifferentPortOrderOfPacketsIsOk) {
  PacketTestRun test_run = gutil::ParseProtoOrDie<PacketTestRun>(R"pb(
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
  )pb");
  ASSERT_OK_AND_ASSIGN(PacketTestValidationResult result,
                       ValidateTestRun(test_run));
  EXPECT_FALSE(result.has_failure());
}

TEST(TestRunValidationTest,
     MissingPacketInsAreIgnoredIfAndOnlyIfIgnorePacketInsIsSet) {
  PacketTestRun test_run = gutil::ParseProtoOrDie<PacketTestRun>(R"pb(
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
  ASSERT_OK_AND_ASSIGN(PacketTestValidationResult result,
                       ValidateTestRun(test_run));
  ASSERT_THAT(result.failure().description(), HasSubstr("packet in"));

  // Ignoring packet-ins, validation must succeed.
  ASSERT_OK_AND_ASSIGN(
      result,
      ValidateTestRun(
          test_run,
          SwitchOutputDiffParams{
              .treat_expected_and_actual_outputs_as_having_no_packet_ins = true,
          },
          /*sut=*/nullptr));
  ASSERT_THAT(result, EqualsProto(R"pb()pb"));
}

TEST(TestRunValidationTest,
     PacketInDifferencesAreIgnoredIfAndOnlyIfIgnorePacketInsIsSet) {
  PacketTestRun test_run = gutil::ParseProtoOrDie<PacketTestRun>(R"pb(
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
  ASSERT_OK_AND_ASSIGN(PacketTestValidationResult result,
                       ValidateTestRun(test_run));
  ASSERT_THAT(result.failure().description(), HasSubstr("target_egress_port"));

  // Ignoring packet-ins, validation must succeed.
  ASSERT_OK_AND_ASSIGN(
      result,
      ValidateTestRun(
          test_run,
          SwitchOutputDiffParams{
              .treat_expected_and_actual_outputs_as_having_no_packet_ins = true,
          },
          /*sut=*/nullptr));
  ASSERT_THAT(result, EqualsProto(R"pb()pb"));
}

TEST(TestRunValidationTest, IgnorePacketInsHasNoEffectWhenPacketInsMatch) {
  PacketTestRun test_run = gutil::ParseProtoOrDie<PacketTestRun>(R"pb(
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
  )pb");
  ASSERT_OK_AND_ASSIGN(
      PacketTestValidationResult result,
      ValidateTestRun(
          test_run,
          SwitchOutputDiffParams{
              .treat_expected_and_actual_outputs_as_having_no_packet_ins = true,
          },
          /*sut=*/nullptr));
  ASSERT_THAT(result, EqualsProto(R"pb()pb"));
}

TEST(TestRunValidationTest, PacketFieldReasonsInvalidIsIgnored) {
  PacketTestRun test_run = gutil::ParseProtoOrDie<PacketTestRun>(R"pb(
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
  ASSERT_OK_AND_ASSIGN(PacketTestValidationResult result,
                       ValidateTestRun(test_run));
  ASSERT_THAT(result, EqualsProto(R"pb()pb"));
}

TEST(TestRunValidationTest, PacketInFieldReasonsInvalidIsIgnored) {
  PacketTestRun test_run = gutil::ParseProtoOrDie<PacketTestRun>(R"pb(
    test_vector {
      acceptable_outputs {
        packet_ins {
          parsed {
            reasons_invalid: "invalid reason 1"
            reasons_invalid: "invalid reason 2"
          }
        }
      }
    }
    actual_output { packet_ins { parsed {} } }
  )pb");

  // Validation must succeed.
  ASSERT_OK_AND_ASSIGN(PacketTestValidationResult result,
                       ValidateTestRun(test_run));
  ASSERT_THAT(result, EqualsProto(R"pb()pb"));
}

TEST(TestRunValidationTest, ModifyExpectedOutputPreDiffingTest) {
  PacketTestRun test_run = gutil::ParseProtoOrDie<PacketTestRun>(R"pb(
    test_vector {
      acceptable_outputs {
        packets {
          port: "1"
          parsed { payload: "" }
        }
      }
    }
    actual_output {
      packets {
        port: "1"
        parsed { payload: "new-payload" }
      }
    }
  )pb");

  ASSERT_OK_AND_ASSIGN(PacketTestValidationResult result_without_modify,
                       ValidateTestRun(test_run));
  ASSERT_TRUE(result_without_modify.has_failure());

  dvaas::SwitchApi sut;

  // If the expected output is modified before diffing, validation must succeed.
  ASSERT_OK_AND_ASSIGN(
      PacketTestValidationResult result_with_modify,
      ValidateTestRun(
          test_run,
          SwitchOutputDiffParams{
              .GetModifiedExpectedOutputPreDiffing =
                  [](const PacketTestRun& packet_test_run,
                     const SwitchApi& sut) {
                    std::vector<SwitchOutput> expected_outputs;
                    for (const auto& output :
                         packet_test_run.test_vector().acceptable_outputs()) {
                      SwitchOutput modified_output = output;
                      *modified_output.mutable_packets(0)
                           ->mutable_parsed()
                           ->mutable_payload() = "new-payload";
                      expected_outputs.push_back(modified_output);
                    }
                    return expected_outputs;
                  },
          },
          /*sut=*/&sut));

  ASSERT_FALSE(result_with_modify.has_failure());
}

std::optional<std::string> FailCustomPayloadCheck(
    absl::string_view /*actual_payload*/,
    absl::string_view /*expected_payload*/) {
  return "failed payload check";
}

std::optional<std::string> PassCustomPayloadCheck(
    absl::string_view /*actual_payload*/,
    absl::string_view /*expected_payload*/) {
  return std::nullopt;
}

TEST(TestRunValidationTest, CustomPayloadCheckForPacket) {
  PacketTestRun test_run = gutil::ParseProtoOrDie<PacketTestRun>(R"pb(
    test_vector {
      acceptable_outputs {
        packets {
          port: "1"
          parsed { payload: "original-payload" }
        }
      }
    }
    actual_output {
      packets {
        port: "1"
        parsed { payload: "new-payload" }
      }
    }
  )pb");

  // Sanity check to confirm that we would fail without the ManualPayloadCheck.
  ASSERT_OK_AND_ASSIGN(PacketTestValidationResult result_without_modify,
                       ValidateTestRun(test_run));
  EXPECT_TRUE(result_without_modify.has_failure());

  ASSERT_OK_AND_ASSIGN(PacketTestValidationResult result_with_modify,
                       ValidateTestRun(test_run, SwitchOutputDiffParams{
                                                     .ManualPayloadCheck =
                                                         PassCustomPayloadCheck,
                                                 }));
  EXPECT_FALSE(result_with_modify.has_failure());
}

TEST(TestRunValidationTest, CustomPayloadCheckForPacketIn) {
  PacketTestRun test_run = gutil::ParseProtoOrDie<PacketTestRun>(R"pb(
    test_vector {
      acceptable_outputs {
        packet_ins { parsed { payload: "original-payload" } }
      }
    }
    actual_output { packet_ins { parsed { payload: "new-payload" } } }
  )pb");

  // Sanity check to confirm that we would fail without the ManualPayloadCheck.
  ASSERT_OK_AND_ASSIGN(PacketTestValidationResult result_without_modify,
                       ValidateTestRun(test_run));
  EXPECT_TRUE(result_without_modify.has_failure());

  ASSERT_OK_AND_ASSIGN(PacketTestValidationResult result_with_modify,
                       ValidateTestRun(test_run, SwitchOutputDiffParams{
                                                     .ManualPayloadCheck =
                                                         PassCustomPayloadCheck,
                                                 }));
  EXPECT_FALSE(result_with_modify.has_failure());
}

TEST(TestRunValidationTest, CustomPayloadCheckFailsForPacket) {
  PacketTestRun test_run = gutil::ParseProtoOrDie<PacketTestRun>(R"pb(
    test_vector {
      acceptable_outputs {
        packets {
          port: "1"
          parsed { payload: "original-payload" }
        }
      }
    }
    actual_output {
      packets {
        port: "1"
        parsed { payload: "new-payload" }
      }
    }
  )pb");

  ASSERT_OK_AND_ASSIGN(PacketTestValidationResult result_with_modify,
                       ValidateTestRun(test_run, SwitchOutputDiffParams{
                                                     .ManualPayloadCheck =
                                                         FailCustomPayloadCheck,
                                                 }));
  EXPECT_TRUE(result_with_modify.has_failure());
}

TEST(TestRunValidationTest, CustomPayloadCheckFailsForPacketIn) {
  PacketTestRun test_run = gutil::ParseProtoOrDie<PacketTestRun>(R"pb(
    test_vector {
      acceptable_outputs {
        packet_ins { parsed { payload: "original-payload" } }
      }
    }
    actual_output { packet_ins { parsed { payload: "new-payload" } } }
  )pb");

  ASSERT_OK_AND_ASSIGN(PacketTestValidationResult result_with_modify,
                       ValidateTestRun(test_run, SwitchOutputDiffParams{
                                                     .ManualPayloadCheck =
                                                         FailCustomPayloadCheck,
                                                 }));
  EXPECT_TRUE(result_with_modify.has_failure());
}

TEST(TestRunValidationTest,
     IngoredPacketInMetadataDoNotAffectPacketInOrderingDuringValidation) {
  PacketTestRun test_run = gutil::ParseProtoOrDie<PacketTestRun>(R"pb(
    test_vector {
      acceptable_outputs {
        packet_ins { metadata { name: "name1" } }
        packet_ins { metadata { name: "name4" } }
        packet_ins { metadata { name: "name2" } }
      }
    }
    actual_output {
      packet_ins { metadata { name: "name2" } }
      packet_ins { metadata { name: "name3" } }
      packet_ins { metadata { name: "name4" } }
    }
  )pb");

  ASSERT_OK_AND_ASSIGN(
      PacketTestValidationResult result_with_modify,
      ValidateTestRun(test_run,
                      SwitchOutputDiffParams{
                          .ignored_packet_in_metadata = {"name1", "name3"},
                      }));
  EXPECT_FALSE(result_with_modify.has_failure());
}

}  // namespace
}  // namespace dvaas
