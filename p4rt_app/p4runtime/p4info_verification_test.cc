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
#include "p4rt_app/p4runtime/p4info_verification.h"

#include "glog/logging.h"
#include "gmock/gmock.h"
#include "google/protobuf/text_format.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "p4_pdpi/utils/ir.h"
#include "sai_p4/instantiations/google/sai_p4info.h"

namespace p4rt_app {
namespace {

using ::google::protobuf::TextFormat;

class P4InfoVerificationTest : public testing::Test {
 protected:
  absl::StatusOr<p4::config::v1::P4TypeInfo> GetExpectedTypes() {
    // constexpr absl::string_view kExpectedTypes =
    constexpr char kExpectedTypes[] =
        R"pb(new_types {
               key: "neighbor_id_t"
               value { translated_type { sdn_string {} } }
             }
             new_types {
               key: "nexthop_id_t"
               value { translated_type { sdn_string {} } }
             }
             new_types {
               key: "port_id_t"
               value { translated_type { sdn_string {} } }
             }
             new_types {
               key: "router_interface_id_t"
               value { translated_type { sdn_string {} } }
             }
             new_types {
               key: "vrf_id_t"
               value { translated_type { sdn_string {} } }
             }
             new_types {
               key: "wcmp_group_id_t"
               value { translated_type { sdn_string {} } }
             })pb";

    p4::config::v1::P4TypeInfo type_info;
    if (!google::protobuf::TextFormat::ParseFromString(kExpectedTypes,
                                                       &type_info)) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Could not parse expected types.";
    }
    return type_info;
  }

  absl::StatusOr<p4::config::v1::ControllerPacketMetadata>
  GetExpectedPacketInMetadata() {
    constexpr char kPacketInMetadata[] =
        R"pb(preamble {
               id: 81826293
               name: "packet_in"
               alias: "packet_in"
               annotations: "@controller_header(\"packet_in\")"
             }
             metadata {
               id: 2
               name: "target_egress_port"
               type_name { name: "port_id_t" }
             }
             metadata {
               id: 1
               name: "ingress_port"
               type_name { name: "port_id_t" }
             })pb";

    p4::config::v1::ControllerPacketMetadata metadata;
    if (!google::protobuf::TextFormat::ParseFromString(kPacketInMetadata,
                                                       &metadata)) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Could not parse packet in metadata.";
    }
    return metadata;
  }

  absl::StatusOr<p4::config::v1::ControllerPacketMetadata>
  GetExpectedPacketOutMetadata() {
    constexpr char kPacketInMetadata[] = R"pb(
      preamble {
        id: 76689799
        name: "packet_out"
        alias: "packet_out"
        annotations: "@controller_header(\"packet_out\")"
      }
      metadata { id: 3 name: "unused_pad" bitwidth: 7 }
      metadata { id: 2 name: "submit_to_ingress" bitwidth: 1 }
      metadata {
        id: 1
        name: "egress_port"
        type_name { name: "port_id_t" }
      })pb";

    p4::config::v1::ControllerPacketMetadata metadata;
    if (!google::protobuf::TextFormat::ParseFromString(kPacketInMetadata,
                                                       &metadata)) {
      return gutil::InvalidArgumentErrorBuilder()
             << "Could not parse packet out metadata.";
    }
    return metadata;
  }
};

TEST_F(P4InfoVerificationTest, SaiP4InfoIsOk) {
  EXPECT_OK(ValidateP4Info(sai::GetP4Info(sai::Instantiation::kMiddleblock)));
}

TEST_F(P4InfoVerificationTest, ExpectedP4InfoValues) {
  p4::config::v1::P4Info p4_info;
  ASSERT_OK_AND_ASSIGN(*p4_info.add_controller_packet_metadata(),
                       GetExpectedPacketInMetadata());
  ASSERT_OK_AND_ASSIGN(*p4_info.add_controller_packet_metadata(),
                       GetExpectedPacketOutMetadata());
  ASSERT_OK_AND_ASSIGN(*p4_info.mutable_type_info(), GetExpectedTypes());
  EXPECT_OK(ValidateP4Info(p4_info));
}

TEST_F(P4InfoVerificationTest, MissingPacketIoMetadata) {
  p4::config::v1::P4Info p4_info;
  ASSERT_OK_AND_ASSIGN(*p4_info.add_controller_packet_metadata(),
                       GetExpectedPacketInMetadata());
  ASSERT_OK_AND_ASSIGN(*p4_info.mutable_type_info(), GetExpectedTypes());

  // Use the expected packet out metadata, but remove the first metadata field.
  ASSERT_OK_AND_ASSIGN(auto packet_out_metadata,
                       GetExpectedPacketOutMetadata());
  ASSERT_GT(packet_out_metadata.metadata_size(), 0);
  packet_out_metadata.mutable_metadata()->erase(
      packet_out_metadata.metadata().begin());
  *p4_info.add_controller_packet_metadata() = packet_out_metadata;

  EXPECT_THAT(ValidateP4Info(p4_info),
              gutil::StatusIs(absl::StatusCode::kInvalidArgument));
}

TEST_F(P4InfoVerificationTest, MissingExpectedTypes) {
  p4::config::v1::P4Info p4_info;
  ASSERT_OK_AND_ASSIGN(*p4_info.add_controller_packet_metadata(),
                       GetExpectedPacketInMetadata());
  ASSERT_OK_AND_ASSIGN(*p4_info.add_controller_packet_metadata(),
                       GetExpectedPacketOutMetadata());

  // Use the expected types fields, but remove the first type.
  ASSERT_OK_AND_ASSIGN(*p4_info.mutable_type_info(), GetExpectedTypes());
  ASSERT_GT(p4_info.type_info().new_types_size(), 0);
  p4_info.mutable_type_info()->mutable_new_types()->erase("neighbor_id_t");

  EXPECT_THAT(ValidateP4Info(p4_info),
              gutil::StatusIs(absl::StatusCode::kInvalidArgument));
}

}  // namespace
}  // namespace p4rt_app
