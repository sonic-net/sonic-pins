#include "sai_p4/tools/packetio_tools.h"

#include "absl/strings/string_view.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace sai {
namespace {

using gutil::EqualsProto;
using gutil::IsOkAndHolds;
using gutil::StatusIs;

TEST(MakePiPacketOutMessageTest,
     NoErrorsWhenMakingPacketOutFromMiddleBlockP4Info) {
  const std::string kPacket = "Some packet";
  const std::string kPort = "Some port";
  EXPECT_THAT(
      MakePiPacketOutMessage(sai::GetP4Info(Instantiation::kMiddleblock),
                             PacketOutMetadata{
                                 .submit_to_ingress = true,
                                 .payload = kPacket,
                                 .egress_port = kPort,
                             }),
      IsOkAndHolds(
          EqualsProto(R"pb(payload: "Some packet"
                           metadata { metadata_id: 1 value: "Some port" }
                           metadata { metadata_id: 2 value: "\001" }
                           metadata { metadata_id: 3 value: "\000" })pb")));

  EXPECT_THAT(
      MakePiPacketOutMessage(sai::GetP4Info(Instantiation::kMiddleblock),
                             PacketOutMetadata{
                                 .submit_to_ingress = false,
                                 .payload = kPacket,
                                 .egress_port = kPort,
                             }),
      IsOkAndHolds(
          EqualsProto(R"pb(payload: "Some packet"
                           metadata { metadata_id: 1 value: "Some port" }
                           metadata { metadata_id: 2 value: "\000" }
                           metadata { metadata_id: 3 value: "\000" })pb")));
}

TEST(MakePiPacketOutMessageTest, NoErrorsWhenMakingPacketOutFromFBR) {
  const std::string kPacket = "Some packet";
  const std::string kPort = "Some port";
  EXPECT_THAT(
      MakePiPacketOutMessage(sai::GetP4Info(Instantiation::kFabricBorderRouter),
                             PacketOutMetadata{
                                 .submit_to_ingress = true,
                                 .payload = kPacket,
                                 .egress_port = kPort,
                             }),
      IsOkAndHolds(EqualsProto(
          R"pb(payload: "Some packet"
               metadata { metadata_id: 1 value: "Some port" }
               metadata { metadata_id: 2 value: "\001" }
               metadata { metadata_id: 3 value: "\000" })pb")));

  EXPECT_THAT(
      MakePiPacketOutMessage(sai::GetP4Info(Instantiation::kFabricBorderRouter),
                             PacketOutMetadata{
                                 .submit_to_ingress = false,
                                 .payload = kPacket,
                                 .egress_port = kPort,
                             }),
      IsOkAndHolds(EqualsProto(
          R"pb(payload: "Some packet"
               metadata { metadata_id: 1 value: "Some port" }
               metadata { metadata_id: 2 value: "\000" }
               metadata { metadata_id: 3 value: "\000" })pb")));
}

// Models case where an extra metadata field has been included but the SAI P4
// program does not contain or has not been updated to include the extra field.
TEST(MakePiPacketOutMessageTest,
     ExtraMetadataFieldInP4InfoGivesUnimplementedError) {
  const std::string kPacket = "Some packet";
  const std::string kPort = "Some port";
  p4::config::v1::P4Info p4_info = sai::GetP4Info(Instantiation::kMiddleblock);

  // Zero should never be a valid id, so safe to use here.
  constexpr int new_id = 0;
  for (auto& controller_metadata :
       *p4_info.mutable_controller_packet_metadata()) {
    if (controller_metadata.preamble().name() == "packet_out") {
      p4::config::v1::ControllerPacketMetadata::Metadata* new_metadata =
          controller_metadata.add_metadata();
      new_metadata->set_id(new_id);
      new_metadata->set_name("new_metadata");
      new_metadata->set_bitwidth(7);
    }
  }

  EXPECT_THAT(MakePiPacketOutMessage(p4_info,
                                     PacketOutMetadata{
                                         .submit_to_ingress = true,
                                         .payload = kPacket,
                                         .egress_port = kPort,
                                     }),
              StatusIs(absl::StatusCode::kUnimplemented));
}

}  // namespace
}  // namespace sai
