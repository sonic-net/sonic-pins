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

#include "absl/strings/cord.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "google/protobuf/text_format.h"
#include "google/protobuf/util/message_differencer.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "p4_pdpi/ir.h"
#include "p4_pdpi/ir.pb.h"
#include "p4rt_app/p4runtime/p4info_verification_schema.h"
#include "p4rt_app/p4runtime/p4info_verification_schema.pb.h"
#include "p4rt_app/sonic/app_db_acl_def_table_manager.h"
#include "p4rt_app/utils/status_utility.h"
#include "p4rt_app/utils/table_utility.h"

namespace p4rt_app {
namespace {

using ::google::protobuf::TextFormat;
using ::google::protobuf::util::MessageDifferencer;

// Verifies if the PacketIo metadata info match the expected values.
absl::Status ValidatePacketIo(const p4::config::v1::P4Info& p4info) {
  constexpr char kExpectedPacketIo[] = R"pb(
    controller_packet_metadata {
      preamble {
        id: 81826293
        name: "packet_in"
        alias: "packet_in"
        annotations: "@controller_header(\"packet_in\")"
      }
      metadata {
        id: 1
        name: "ingress_port"
        type_name { name: "port_id_t" }
      }
      metadata {
        id: 2
        name: "target_egress_port"
        type_name { name: "port_id_t" }
      }
    }
    controller_packet_metadata {
      preamble {
        id: 76689799
        name: "packet_out"
        alias: "packet_out"
        annotations: "@controller_header(\"packet_out\")"
      }
      metadata {
        id: 1
        name: "egress_port"
        type_name { name: "port_id_t" }
      }
      metadata { id: 2 name: "submit_to_ingress" bitwidth: 1 }
      metadata { id: 3 name: "unused_pad" bitwidth: 7 }
    }
  )pb";

  p4::config::v1::P4Info expected_p4info;
  if (!TextFormat::ParseFromString(kExpectedPacketIo, &expected_p4info)) {
    return gutil::InternalErrorBuilder() << "Invalid PacketIO validation info.";
  }

  // Ignore ordering of repeated fields when comparing the protobufs.
  MessageDifferencer diff;
  diff.set_repeated_field_comparison(MessageDifferencer::AS_SET);

  // Track any differences for error reporting.
  std::string diff_str;
  diff.ReportDifferencesToString(&diff_str);

  // We only want to compare the controller_packet_metadata repeated fields.
  p4::config::v1::P4Info actual_p4info;
  for (const auto& packet_metadata : p4info.controller_packet_metadata()) {
    *actual_p4info.add_controller_packet_metadata() = packet_metadata;
  }

  // NOTE: expected values should be the first argument so that the diff string
  // correctly reports added and deleted fields.
  if (!diff.Compare(expected_p4info, actual_p4info)) {
    return gutil::InvalidArgumentErrorBuilder()
           << "PacketIO metadata not supported by P4Info. " << diff_str;
  }
  return absl::OkStatus();
}
}  // namespace

absl::Status ValidateP4Info(const p4::config::v1::P4Info& p4info) {
  RETURN_IF_ERROR(ValidatePacketIo(p4info));
  ASSIGN_OR_RETURN(P4InfoVerificationSchema schema, SupportedSchema());
  ASSIGN_OR_RETURN(auto ir_result, pdpi::CreateIrP4Info(p4info),
                   _.SetPayload(kLibraryUrl, absl::Cord("PDPI")));
  RETURN_IF_ERROR(IsSupportedBySchema(ir_result, schema));

  return absl::OkStatus();
}

}  // namespace p4rt_app
