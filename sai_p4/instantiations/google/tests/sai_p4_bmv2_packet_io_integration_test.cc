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

#include <cassert>
#include <memory>
#include <string>
#include <vector>

#include "glog/logging.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status.h"
#include "gutil/testing.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "p4_pdpi/packetlib/packetlib.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"
#include "p4_pdpi/pd.h"
#include "p4_pdpi/string_encodings/byte_string.h"
#include "platforms/networking/p4/p4_infra/bmv2/bmv2.h"
#include "sai_p4/fixed/ids.h"
#include "sai_p4/instantiations/google/instantiations.h"
#include "sai_p4/instantiations/google/sai_nonstandard_platforms.h"
#include "sai_p4/instantiations/google/sai_p4info.h"
#include "sai_p4/instantiations/google/sai_pd.pb.h"
#include "sai_p4/instantiations/google/test_tools/test_entries.h"
#include "sai_p4/tools/auxiliary_entries_for_v1model_targets.h"

namespace pins {
namespace {

using ::orion::p4::test::Bmv2;
using ::p4::v1::ForwardingPipelineConfig;
using ::p4::v1::PacketMetadata;
using ::p4::v1::SetForwardingPipelineConfigRequest;
using ::p4::v1::StreamMessageResponse;
using ::p4::v1::Update;
using ::p4::v1::WriteRequest;
using ::testing::ElementsAre;
using ::testing::EqualsProto;
using ::testing::IsEmpty;
using ::testing::TestWithParam;
using ::testing::status::IsOkAndHolds;

using PacketStream = grpc::ClientReaderWriter<::p4::bm::PacketStreamRequest,
                                              ::p4::bm::PacketStreamResponse>;

constexpr int kBmv2PortBitwidth = 9;

constexpr sai::NonstandardPlatform kPlatformBmv2 =
    sai::NonstandardPlatform::kBmv2;

using BMv2PacketIOTest = TestWithParam<sai::Instantiation>;

TEST_P(BMv2PacketIOTest, ControllerReceivesPuntPacketIn) {
  constexpr int kIngressPort = 1;
  constexpr int kEgressPort = 42;

  ForwardingPipelineConfig bmv2_config =
      sai::GetNonstandardForwardingPipelineConfig(GetParam(), kPlatformBmv2);
  pdpi::IrP4Info ir_p4info = sai::GetIrP4Info(GetParam());

  // Create and configure BMv2.
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, Bmv2::Create({
                                      .device_id = 1,
                                      .cpu_port = SAI_P4_CPU_PORT,
                                      .drop_port = SAI_P4_DROP_PORT,
                                  }));
  ASSERT_OK(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      &bmv2.P4RuntimeSession(),
      SetForwardingPipelineConfigRequest::VERIFY_AND_COMMIT, bmv2_config));

  // Install table enties for punting packets.
  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::TableEntry> table_entries,
      sai::MakePiEntriesForwardingIpPacketsToGivenPort(
          pdpi::BitsetToP4RuntimeByteString<kBmv2PortBitwidth>(kEgressPort),
          ir_p4info));
  ASSERT_OK_AND_ASSIGN(
      table_entries.emplace_back(),
      sai::MakePiEntryPuntingAllPackets(sai::PuntAction::kTrap, ir_p4info));
  ASSERT_OK(InstallPiTableEntries(&bmv2.P4RuntimeSession(), ir_p4info,
                                  table_entries));
  ASSERT_OK(pdpi::InstallPiEntity(
      &bmv2.P4RuntimeSession(),
      sai::MakeV1modelPacketReplicationEngineEntryRequiredForPunts()));

  ASSERT_OK_AND_ASSIGN(packetlib::Packet input_packet,
                       gutil::ParseTextProto<packetlib::Packet>(R"pb(
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
                             total_length: "0x002e"
                             identification: "0x0000"
                             flags: "0x0"
                             fragment_offset: "0x0000"
                             ttl: "0x20"
                             protocol: "0x11"
                             checksum: "0x50fb"
                             ipv4_source: "192.168.100.2"
                             ipv4_destination: "192.168.100.1"
                           }
                         }
                         headers {
                           udp_header {
                             source_port: "0x0000"
                             destination_port: "0x0000"
                             length: "0x001a"
                             checksum: "0x8d24"
                           }
                         }
                         payload: "Test packet."
                       )pb"));
  ASSERT_OK_AND_ASSIGN(std::string raw_input_packet,
                       packetlib::SerializePacket(input_packet));

  ASSERT_THAT(bmv2.SendPacket(pins::PacketAtPort{
                  .port = kIngressPort,
                  .data = raw_input_packet,
              }),
              IsOkAndHolds(IsEmpty()));

  // Wait for 1 second to make sure packets are fully processed by BMv2.
  absl::SleepFor(absl::Seconds(1));

  StreamMessageResponse expected_response;
  expected_response.mutable_packet()->set_payload(raw_input_packet);
  // Check if the ingress port in the metadata is correct.
  PacketMetadata* ingress_port_field =
      expected_response.mutable_packet()->add_metadata();
  ingress_port_field->set_metadata_id(PACKET_IN_INGRESS_PORT_ID);
  ingress_port_field->set_value(pdpi::BitsetToP4RuntimeByteString(
      std::bitset<kBmv2PortBitwidth>(kIngressPort)));
  // Check if the target egress port in the metadata is correct.
  PacketMetadata* target_egress_port_field =
      expected_response.mutable_packet()->add_metadata();
  target_egress_port_field->set_metadata_id(PACKET_IN_TARGET_EGRESS_PORT_ID);
  target_egress_port_field->set_value(pdpi::BitsetToP4RuntimeByteString(
      std::bitset<kBmv2PortBitwidth>(kEgressPort)));
  // Padding of the packet-in header.
  PacketMetadata* unused_pad =
      expected_response.mutable_packet()->add_metadata();
  unused_pad->set_metadata_id(PACKET_IN_UNUSED_PAD_ID);
  unused_pad->set_value(pdpi::BitsetToP4RuntimeByteString(std::bitset<6>(0)));

  // Check that packet is correctly punted and close the session.
  EXPECT_THAT(bmv2.P4RuntimeSession().ReadStreamChannelResponsesAndFinish(),
              IsOkAndHolds(ElementsAre(EqualsProto(expected_response))));
}

TEST_P(BMv2PacketIOTest, ControllerReceivesCopyPacketIn) {
  constexpr int kIngressPort = 1;
  constexpr int kEgressPort = 42;

  ForwardingPipelineConfig bmv2_config =
      sai::GetNonstandardForwardingPipelineConfig(GetParam(), kPlatformBmv2);
  pdpi::IrP4Info ir_p4info = sai::GetIrP4Info(GetParam());

  // Create and configure BMv2.
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, Bmv2::Create({
                                      .device_id = 1,
                                      .cpu_port = SAI_P4_CPU_PORT,
                                      .drop_port = SAI_P4_DROP_PORT,
                                  }));
  ASSERT_OK(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      &bmv2.P4RuntimeSession(),
      SetForwardingPipelineConfigRequest::VERIFY_AND_COMMIT, bmv2_config));

  // Install table enties for punting packets.
  ASSERT_OK_AND_ASSIGN(
      std::vector<p4::v1::TableEntry> table_entries,
      sai::MakePiEntriesForwardingIpPacketsToGivenPort(
          pdpi::BitsetToP4RuntimeByteString<kBmv2PortBitwidth>(kEgressPort),
          ir_p4info));
  ASSERT_OK_AND_ASSIGN(
      table_entries.emplace_back(),
      sai::MakePiEntryPuntingAllPackets(sai::PuntAction::kCopy, ir_p4info));
  ASSERT_OK(InstallPiTableEntries(&bmv2.P4RuntimeSession(), ir_p4info,
                                  table_entries));
  ASSERT_OK(pdpi::InstallPiEntity(
      &bmv2.P4RuntimeSession(),
      sai::MakeV1modelPacketReplicationEngineEntryRequiredForPunts()));

  ASSERT_OK_AND_ASSIGN(packetlib::Packet input_packet,
                       gutil::ParseTextProto<packetlib::Packet>(R"pb(
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
                             total_length: "0x002e"
                             identification: "0x0000"
                             flags: "0x0"
                             fragment_offset: "0x0000"
                             ttl: "0x20"
                             protocol: "0x11"
                             checksum: "0x50fb"
                             ipv4_source: "192.168.100.2"
                             ipv4_destination: "192.168.100.1"
                           }
                         }
                         headers {
                           udp_header {
                             source_port: "0x0000"
                             destination_port: "0x0000"
                             length: "0x001a"
                             checksum: "0x8d24"
                           }
                         }
                         payload: "Test packet."
                       )pb"));
  ASSERT_OK_AND_ASSIGN(std::string raw_input_packet,
                       packetlib::SerializePacket(input_packet));

  // The output packet that will egress out of kEgressPort.
  packetlib::Packet output_packet = input_packet;
  // The ttl field of the ipv4 header will be updated by the ingress pipeline.
  output_packet.mutable_headers(1)->mutable_ipv4_header()->set_ttl("0x1f");
  // Update the checksum of the ipv4 header because the ttl field is changed.
  output_packet.mutable_headers(1)->mutable_ipv4_header()->set_checksum(
      "0x51fb");
  ASSERT_OK_AND_ASSIGN(std::string raw_output_packet,
                       packetlib::SerializePacket(output_packet));

  ASSERT_THAT(bmv2.SendPacket(pins::PacketAtPort{
                  .port = kIngressPort,
                  .data = raw_input_packet,
              }),
              IsOkAndHolds(ElementsAre(pins::PacketAtPort{
                  .port = kEgressPort,
                  .data = raw_output_packet,
              })));

  // Wait for 1 second to make sure packets are fully processed by BMv2.
  absl::SleepFor(absl::Seconds(1));

  StreamMessageResponse expected_response;
  expected_response.mutable_packet()->set_payload(raw_input_packet);
  // Check if the ingress port in the metadata is correct.
  PacketMetadata* ingress_port_field =
      expected_response.mutable_packet()->add_metadata();
  ingress_port_field->set_metadata_id(PACKET_IN_INGRESS_PORT_ID);
  ingress_port_field->set_value(pdpi::BitsetToP4RuntimeByteString(
      std::bitset<kBmv2PortBitwidth>(kIngressPort)));
  // Check if the target egress port in the metadata is correct.
  PacketMetadata* target_egress_port_field =
      expected_response.mutable_packet()->add_metadata();
  target_egress_port_field->set_metadata_id(PACKET_IN_TARGET_EGRESS_PORT_ID);
  target_egress_port_field->set_value(pdpi::BitsetToP4RuntimeByteString(
      std::bitset<kBmv2PortBitwidth>(kEgressPort)));
  // Padding of the packet-in header.
  PacketMetadata* unused_pad =
      expected_response.mutable_packet()->add_metadata();
  unused_pad->set_metadata_id(PACKET_IN_UNUSED_PAD_ID);
  unused_pad->set_value(pdpi::BitsetToP4RuntimeByteString(std::bitset<6>(0)));

  // Check that packet is correctly punted and close the session.
  EXPECT_THAT(bmv2.P4RuntimeSession().ReadStreamChannelResponsesAndFinish(),
              IsOkAndHolds(ElementsAre(EqualsProto(expected_response))));
}

TEST_P(BMv2PacketIOTest, P4RuntimePacketOutSubmitToIngressOk) {
  constexpr int kEgressPort = 42;

  ForwardingPipelineConfig bmv2_config =
      sai::GetNonstandardForwardingPipelineConfig(GetParam(), kPlatformBmv2);
  pdpi::IrP4Info ir_p4info = sai::GetIrP4Info(GetParam());

  // Create and configure BMv2.
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, Bmv2::Create({
                                      .device_id = 1,
                                      .cpu_port = SAI_P4_CPU_PORT,
                                      .drop_port = SAI_P4_DROP_PORT,
                                  }));
  ASSERT_OK(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      &bmv2.P4RuntimeSession(),
      SetForwardingPipelineConfigRequest::VERIFY_AND_COMMIT, bmv2_config));

  // Install table enties for routing packets.
  ASSERT_OK_AND_ASSIGN(
      const std::vector<p4::v1::TableEntry> kTableEntries,
      sai::MakePiEntriesForwardingIpPacketsToGivenPort(
          pdpi::BitsetToP4RuntimeByteString<kBmv2PortBitwidth>(kEgressPort),
          ir_p4info));
  ASSERT_OK(InstallPiTableEntries(&bmv2.P4RuntimeSession(), ir_p4info,
                                  kTableEntries));

  ASSERT_OK_AND_ASSIGN(packetlib::Packet input_packet,
                       gutil::ParseTextProto<packetlib::Packet>(R"pb(
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
                             total_length: "0x002e"
                             identification: "0x0000"
                             flags: "0x0"
                             fragment_offset: "0x0000"
                             ttl: "0x20"
                             protocol: "0x11"
                             checksum: "0x50fb"
                             ipv4_source: "192.168.100.2"
                             ipv4_destination: "192.168.100.1"
                           }
                         }
                         headers {
                           udp_header {
                             source_port: "0x0000"
                             destination_port: "0x0000"
                             length: "0x001a"
                             checksum: "0x8d24"
                           }
                         }
                         payload: "Test packet."
                       )pb"));
  ASSERT_OK_AND_ASSIGN(const std::string raw_input_packet,
                       packetlib::SerializePacket(input_packet));

  // Assemble PacketOut protobuf message.
  sai::PacketOut packet_out;
  packet_out.set_payload(raw_input_packet);
  sai::PacketOut::Metadata& metadata = *packet_out.mutable_metadata();
  // Setting the `egress_port` field of the packet-out header to an arbitrary
  // number 123, which should have no effect as we are submitting the packet to
  // the ingress pipeline and the eventual egress port for the packet will be
  // decided by the ingress pipeline. The `egress_port` field in the packet-out
  // header will not be used in this case.
  metadata.set_egress_port(
      pdpi::BitsetToP4RuntimeByteString(std::bitset<kBmv2PortBitwidth>(123)));
  metadata.set_submit_to_ingress(pdpi::BitsetToHexString<1>(1));

  // Create packet stream before writing to the stream channel to make sure the
  // packet stream receives the packet sent via the stream channel.
  grpc::ClientContext context;
  std::unique_ptr<PacketStream> packet_stream =
      bmv2.DataplaneStub().PacketStream(&context);

  // There seems to be some race conditions between the BMv2 packet stream gRPC
  // server and p4rt session stream channel gRPC server, causing the packet
  // stream not receiving packets sent in via the p4rt session stream channel.
  // Wait for 1 second to reduce the flakiness.
  // TODO: Solve BMv2 flakiness problem.
  absl::SleepFor(absl::Seconds(1));

  // Assemble PacketOut request and write to stream channel.
  ::p4::v1::StreamMessageRequest request;
  ASSERT_OK_AND_ASSIGN(*request.mutable_packet(),
                       pdpi::PdPacketOutToPi(ir_p4info, packet_out));
  ASSERT_TRUE(bmv2.P4RuntimeSession().StreamChannelWrite(request));

  // Wait for 1 second to make sure packets are fully processed by BMv2.
  absl::SleepFor(absl::Seconds(1));
  packet_stream->WritesDone();

  packetlib::Packet expected_packet = input_packet;
  // The ttl field of the ipv4 header will be updated by the ingress pipeline.
  expected_packet.mutable_headers(1)->mutable_ipv4_header()->set_ttl("0x1f");
  // Update the checksum of the ipv4 header because the ttl field is changed.
  expected_packet.mutable_headers(1)->mutable_ipv4_header()->set_checksum(
      "0x51fb");

  // Check that packet is routed correctly to the egress port.
  ::p4::bm::PacketStreamResponse expected_response;
  expected_response.set_port(kEgressPort);
  expected_response.set_packet(*packetlib::SerializePacket(expected_packet));
  expected_response.set_device_id(1);

  ::p4::bm::PacketStreamResponse packet_response;
  ASSERT_TRUE(packet_stream->Read(&packet_response));
  EXPECT_THAT(packet_response, EqualsProto(expected_response));
  EXPECT_FALSE(packet_stream->Read(&packet_response));
}

TEST_P(BMv2PacketIOTest, P4RuntimePacketOutSubmitToEgressOk) {
  constexpr int kEgressPort = 42;

  ForwardingPipelineConfig bmv2_config =
      sai::GetNonstandardForwardingPipelineConfig(GetParam(), kPlatformBmv2);
  pdpi::IrP4Info ir_p4info = sai::GetIrP4Info(GetParam());

  // Create and configure BMv2.
  ASSERT_OK_AND_ASSIGN(Bmv2 bmv2, Bmv2::Create({
                                      .device_id = 1,
                                      .cpu_port = SAI_P4_CPU_PORT,
                                      .drop_port = SAI_P4_DROP_PORT,
                                  }));
  ASSERT_OK(pdpi::SetMetadataAndSetForwardingPipelineConfig(
      &bmv2.P4RuntimeSession(),
      SetForwardingPipelineConfigRequest::VERIFY_AND_COMMIT, bmv2_config));

  // Although we gonna skip the ingress pipeline, we still install table entries
  // here to ensure the switch is not just doing submit to ingress again. Here
  // we set the egress port of the ingress pipeline to the drop port, so if the
  // switch is just doing submit to ingress, packets gonna be dropped.
  ASSERT_OK_AND_ASSIGN(
      const std::vector<p4::v1::TableEntry> kTableEntries,
      sai::MakePiEntriesForwardingIpPacketsToGivenPort(
          pdpi::BitsetToP4RuntimeByteString(
              std::bitset<kBmv2PortBitwidth>(SAI_P4_DROP_PORT)),
          ir_p4info));

  ASSERT_OK(InstallPiTableEntries(&bmv2.P4RuntimeSession(), ir_p4info,
                                  kTableEntries));

  ASSERT_OK_AND_ASSIGN(packetlib::Packet input_packet,
                       gutil::ParseTextProto<packetlib::Packet>(R"pb(
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
                             total_length: "0x002e"
                             identification: "0x0000"
                             flags: "0x0"
                             fragment_offset: "0x0000"
                             ttl: "0x20"
                             protocol: "0x11"
                             checksum: "0x50fb"
                             ipv4_source: "192.168.100.2"
                             ipv4_destination: "192.168.100.1"
                           }
                         }
                         headers {
                           udp_header {
                             source_port: "0x0000"
                             destination_port: "0x0000"
                             length: "0x001a"
                             checksum: "0x8d24"
                           }
                         }
                         payload: "Test packet."
                       )pb"));
  ASSERT_OK_AND_ASSIGN(const std::string raw_input_packet,
                       packetlib::SerializePacket(input_packet));

  // Assemble PacketOut protobuf message.
  sai::PacketOut packet_out;
  packet_out.set_payload(raw_input_packet);
  sai::PacketOut::Metadata& metadata = *packet_out.mutable_metadata();
  // Setting the `egress_port` field of the packet-out header to `kEgressPort`
  // and expect packet to egress on `kEgressPort`. Because we are submitting the
  // packet to the egress pipeline and the `egress_port` field of the packet-out
  // header should be used as the egress port of the packet in this case.
  metadata.set_egress_port(pdpi::BitsetToP4RuntimeByteString(
      std::bitset<kBmv2PortBitwidth>(kEgressPort)));
  metadata.set_submit_to_ingress(pdpi::BitsetToHexString<1>(0));

  // Create packet stream before writing to the stream channel to make sure the
  // packet stream receives the packet sent via the stream channel.
  grpc::ClientContext context;
  std::unique_ptr<PacketStream> packet_stream =
      bmv2.DataplaneStub().PacketStream(&context);

  // There seems to be some race conditions between the BMv2 packet stream gRPC
  // server and p4rt session stream channel gRPC server, causing the packet
  // stream not receiving packets sent in via the p4rt session stream channel.
  // Wait for 1 second to reduce the flakiness.
  // TODO: Solve BMv2 flakiness problem.
  absl::SleepFor(absl::Seconds(1));

  // Assemble PacketOut request and write to stream channel.
  ::p4::v1::StreamMessageRequest request;
  ASSERT_OK_AND_ASSIGN(*request.mutable_packet(),
                       pdpi::PdPacketOutToPi(ir_p4info, packet_out));
  ASSERT_TRUE(bmv2.P4RuntimeSession().StreamChannelWrite(request));

  // Wait for 1 second to make sure packets are fully processed by BMv2.
  absl::SleepFor(absl::Seconds(1));
  packet_stream->WritesDone();

  ::p4::bm::PacketStreamResponse expected_response;
  // Check that packet is routed correctly to the egress port.
  expected_response.set_port(kEgressPort);
  expected_response.set_packet(raw_input_packet);
  expected_response.set_device_id(1);

  ::p4::bm::PacketStreamResponse packet_response;
  ASSERT_TRUE(packet_stream->Read(&packet_response));
  EXPECT_THAT(packet_response, EqualsProto(expected_response));
  EXPECT_FALSE(packet_stream->Read(&packet_response));
}

INSTANTIATE_TEST_SUITE_P(
    BMv2PacketIOTest, BMv2PacketIOTest,
    testing::ValuesIn(sai::AllSaiInstantiations()),
    [&](const testing::TestParamInfo<sai::Instantiation>& info) {
      return InstantiationToString(info.param);
    });
}  // namespace
}  // namespace pins
