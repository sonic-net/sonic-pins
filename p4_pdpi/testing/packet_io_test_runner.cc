// Copyright 2020 Google LLC
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

#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "gutil/gutil/status.h"
#include "gutil/gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/pd.h"
#include "p4_pdpi/testing/main_p4_pd.pb.h"
#include "p4_pdpi/testing/test_helper.h"

using ::p4::config::v1::P4Info;

static void RunPiPacketInTest(const pdpi::IrP4Info& info,
                              const std::string& test_name,
                              const p4::v1::PacketIn& pi) {
  RunGenericPiTest<pdpi::IrPacketIn, p4::v1::PacketIn>(
      info, absl::StrCat("PacketIn test: ", test_name), pi,
      pdpi::TranslationOptions(), pdpi::PiPacketInToIr);
}

static void RunIrToPiPacketInTest(const pdpi::IrP4Info& info,
                                  const std::string& test_name,
                                  const pdpi::IrPacketIn& ir) {
  RunGenericIrToPiTest<pdpi::IrPacketIn, p4::v1::PacketIn>(
      info, absl::StrCat("PacketIn test: ", test_name), ir,
      pdpi::TranslationOptions(), pdpi::IrPacketInToPi);
}

static void RunIrToPdPacketInTest(const pdpi::IrP4Info& info,
                                  const std::string& test_name,
                                  const pdpi::IrPacketIn& ir) {
  RunGenericIrToPdTest<pdpi::IrPacketIn, pdpi::PacketIn>(
      info, absl::StrCat("PacketIn test: ", test_name), ir,
      pdpi::TranslationOptions(), pdpi::IrPacketInToPd);
}

static void RunPdPacketInTest(const pdpi::IrP4Info& info,
                              const std::string& test_name,
                              const pdpi::PacketIn& pd,
                              const InputValidity validity) {
  RunGenericPdTest<pdpi::PacketIn, pdpi::IrPacketIn, p4::v1::PacketIn>(
      info, absl::StrCat("PacketIn test: ", test_name), pd,
      pdpi::TranslationOptions(), pdpi::PdPacketInToIr, pdpi::IrPacketInToPd,
      pdpi::IrPacketInToPi, pdpi::PiPacketInToIr, pdpi::PdPacketInToPi,
      pdpi::PiPacketInToPd, validity);
}

static void RunPiPacketOutTest(const pdpi::IrP4Info& info,
                               const std::string& test_name,
                               const p4::v1::PacketOut& pi) {
  RunGenericPiTest<pdpi::IrPacketOut, p4::v1::PacketOut>(
      info, absl::StrCat("PacketOut test: ", test_name), pi,
      pdpi::TranslationOptions(), pdpi::PiPacketOutToIr);
}

static void RunIrToPiPacketOutTest(const pdpi::IrP4Info& info,
                                   const std::string& test_name,
                                   const pdpi::IrPacketOut& ir) {
  RunGenericIrToPiTest<pdpi::IrPacketOut, p4::v1::PacketOut>(
      info, absl::StrCat("PacketOut test: ", test_name), ir,
      pdpi::TranslationOptions(), pdpi::IrPacketOutToPi);
}

static void RunIrToPdPacketOutTest(const pdpi::IrP4Info& info,
                                   const std::string& test_name,
                                   const pdpi::IrPacketOut& ir) {
  RunGenericIrToPdTest<pdpi::IrPacketOut, pdpi::PacketOut>(
      info, absl::StrCat("PacketOut test: ", test_name), ir,
      pdpi::TranslationOptions(), pdpi::IrPacketOutToPd);
}

static void RunPdPacketOutTest(const pdpi::IrP4Info& info,
                               const std::string& test_name,
                               const pdpi::PacketOut& pd,
                               const InputValidity validity) {
  RunGenericPdTest<pdpi::PacketOut, pdpi::IrPacketOut, p4::v1::PacketOut>(
      info, absl::StrCat("PacketOut test: ", test_name), pd,
      pdpi::TranslationOptions(), pdpi::PdPacketOutToIr, pdpi::IrPacketOutToPd,
      pdpi::IrPacketOutToPi, pdpi::PiPacketOutToIr, pdpi::PdPacketOutToPi,
      pdpi::PiPacketOutToPd, validity);
}

static void RunPacketInTests(pdpi::IrP4Info info) {
  RunPiPacketInTest(info, "duplicate id",
                    gutil::ParseProtoOrDie<p4::v1::PacketIn>(R"pb(
                      payload: "1"
                      metadata { metadata_id: 1 value: "\x34" }
                      metadata { metadata_id: 1 value: "\x34" }
                      metadata { metadata_id: 2 value: "\x23" }
                      metadata { metadata_id: 3 value: "\x0" }
                    )pb"));
  RunPiPacketInTest(info, "missing metadata",
                    gutil::ParseProtoOrDie<p4::v1::PacketIn>(R"pb(
                      payload: "1"
                      metadata { metadata_id: 1 value: "\x34" }
                      metadata { metadata_id: 3 value: "\x0" }
                    )pb"));
  RunPiPacketInTest(info, "extra metadata",
                    gutil::ParseProtoOrDie<p4::v1::PacketIn>(R"pb(
                      payload: "1"
                      metadata { metadata_id: 1 value: "\x34" }
                      metadata { metadata_id: 2 value: "\x23" }
                      metadata { metadata_id: 3 value: "\x0" }
                      metadata { metadata_id: 4 value: "\x124" }
                    )pb"));
  RunPiPacketInTest(info, "padding metadata is non-zero",
                    gutil::ParseProtoOrDie<p4::v1::PacketIn>(R"pb(
                      payload: "1"
                      metadata { metadata_id: 1 value: "\x34" }
                      metadata { metadata_id: 2 value: "\x23" }
                      metadata { metadata_id: 3 value: "\x12" }
                    )pb"));
  RunIrToPiPacketInTest(info, "padding metadata present in IR during IR->PI",
                        gutil::ParseProtoOrDie<pdpi::IrPacketIn>(R"pb(
                          payload: "1"
                          metadata {
                            name: "ingress_port"
                            value { hex_str: "0x034" }
                          }
                          metadata {
                            name: "target_egress_port"
                            value { str: "eth-1/2/3" }
                          }
                          metadata {
                            name: "unused_padding"
                            value { hex_str: "0x0" }
                          }
                        )pb"));
  RunIrToPdPacketInTest(info, "padding metadata present in IR during IR->PD",
                        gutil::ParseProtoOrDie<pdpi::IrPacketIn>(R"pb(
                          payload: "1"
                          metadata {
                            name: "ingress_port"
                            value { hex_str: "0x034" }
                          }
                          metadata {
                            name: "target_egress_port"
                            value { str: "eth-1/2/3" }
                          }
                          metadata {
                            name: "unused_padding"
                            value { hex_str: "0x0" }
                          }
                        )pb"));
  RunPdPacketInTest(info, "Format::STRING with empty bytestring",
                    gutil::ParseProtoOrDie<pdpi::PacketIn>(R"pb(
                      payload: "1"
                      metadata { ingress_port: "0x034" target_egress_port: "" }
                    )pb"),
                    INPUT_IS_INVALID);
  RunPdPacketInTest(
      info, "ok", gutil::ParseProtoOrDie<pdpi::PacketIn>(R"pb(
        payload: "1"
        metadata { ingress_port: "0x034" target_egress_port: "eth-1/2/3" }
      )pb"),
      INPUT_IS_VALID);
  RunPdPacketInTest(
      info, "Format::STRING with null characters",
      gutil::ParseProtoOrDie<pdpi::PacketIn>(R"pb(
        payload: "1"
        metadata { ingress_port: "0x034" target_egress_port: "\00423" }
      )pb"),
      INPUT_IS_VALID);
}

static void RunPacketOutTests(pdpi::IrP4Info info) {
  RunPiPacketOutTest(info, "duplicate id",
                     gutil::ParseProtoOrDie<p4::v1::PacketOut>(R"pb(
                       payload: "1"
                       metadata { metadata_id: 1 value: "\x1" }
                       metadata { metadata_id: 1 value: "\x1" }
                       metadata { metadata_id: 2 value: "\x1" }
                       metadata { metadata_id: 3 value: "\x0" }
                     )pb"));

  RunPiPacketOutTest(info, "missing metadata",
                     gutil::ParseProtoOrDie<p4::v1::PacketOut>(R"pb(
                       payload: "1"
                       metadata { metadata_id: 1 value: "\x1" }
                       metadata { metadata_id: 3 value: "\x0" }
                     )pb"));
  RunPiPacketOutTest(info, "extra metadata",
                     gutil::ParseProtoOrDie<p4::v1::PacketOut>(R"pb(
                       payload: "1"
                       metadata { metadata_id: 1 value: "\x0" }
                       metadata { metadata_id: 2 value: "\x1" }
                       metadata { metadata_id: 3 value: "\x0" }
                       metadata { metadata_id: 4 value: "\x1" }
                     )pb"));
  RunPiPacketOutTest(info, "padding metadata is non-zero",
                     gutil::ParseProtoOrDie<p4::v1::PacketOut>(R"pb(
                       payload: "1"
                       metadata { metadata_id: 1 value: "\x0" }
                       metadata { metadata_id: 2 value: "\x1" }
                       metadata { metadata_id: 3 value: "\x1" }
                     )pb"));
  RunIrToPiPacketOutTest(info, "padding metadata present in IR during IR->PI",
                         gutil::ParseProtoOrDie<pdpi::IrPacketOut>(R"pb(
                           payload: "1"
                           metadata {
                             name: "egress_port"
                             value { str: "eth-1/2/3" }
                           }
                           metadata {
                             name: "submit_to_ingress"
                             value { hex_str: "0x1" }
                           }
                           metadata {
                             name: "unused_padding"
                             value { hex_str: "0x0" }
                           }
                         )pb"));
  RunIrToPdPacketOutTest(info, "padding metadata present in IR during IR->PD",
                         gutil::ParseProtoOrDie<pdpi::IrPacketOut>(R"pb(
                           payload: "1"
                           metadata {
                             name: "egress_port"
                             value { str: "eth-1/2/3" }
                           }
                           metadata {
                             name: "submit_to_ingress"
                             value { hex_str: "0x1" }
                           }
                           metadata {
                             name: "unused_padding"
                             value { hex_str: "0x0" }
                           }
                         )pb"));
  RunPdPacketOutTest(info, "empty bytestring due to only one field set",
                     gutil::ParseProtoOrDie<pdpi::PacketOut>(R"pb(
                       payload: "1"
                       metadata { submit_to_ingress: "0x1" }
                     )pb"),
                     INPUT_IS_INVALID);
  RunPdPacketOutTest(
      info, "ok", gutil::ParseProtoOrDie<pdpi::PacketOut>(R"pb(
        payload: "1"
        metadata { submit_to_ingress: "0x1" egress_port: "eth-1/2/3" }
      )pb"),
      INPUT_IS_VALID);
}

int main(int argc, char** argv) {
  // Usage: packet_io_test <p4info file>.
  if (argc != 2) {
    std::cerr << "Invalid number of arguments." << std::endl;
    return 1;
  }
  const auto p4info =
      gutil::ParseProtoFileOrDie<p4::config::v1::P4Info>(argv[1]);

  absl::StatusOr<pdpi::IrP4Info> status_or_info = pdpi::CreateIrP4Info(p4info);
  if (!status_or_info.status().ok()) {
    std::cerr << "Unable to create IrP4Info." << std::endl;
    return 1;
  }
  pdpi::IrP4Info info = status_or_info.value();

  RunPacketInTests(info);
  RunPacketOutTests(info);
  return 0;
}
