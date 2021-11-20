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

#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "google/protobuf/text_format.h"
#include "google/protobuf/util/message_differencer.h"
#include "gutil/collections.h"
#include "gutil/status.h"

namespace p4rt_app {

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

// Verifies if the P4info types match the expected values.
absl::Status ValidateTypes(const p4::config::v1::P4Info& p4info) {
  constexpr char kExpectedTypes[] = R"pb(
    type_info {
      new_types {
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
      }
    }
  )pb";
  p4::config::v1::P4Info expected_p4info;
  if (!TextFormat::ParseFromString(kExpectedTypes, &expected_p4info)) {
    return gutil::InternalErrorBuilder() << "Invalid Type validation info.";
  }

  // Create local copy of the actual type_info fields so we can have an ordered
  // map to compare with.
  std::map<std::string, p4::config::v1::P4NewTypeSpec> configured_types(
      p4info.type_info().new_types().begin(),
      p4info.type_info().new_types().end());

  // Create local copy of the expected type_info fields so we can have an
  // ordered map to compare with.
  std::map<std::string, p4::config::v1::P4NewTypeSpec> expected_types(
      expected_p4info.type_info().new_types().begin(),
      expected_p4info.type_info().new_types().end());

  auto configured_type_iter = configured_types.begin();
  auto expected_type_iter = expected_types.begin();
  std::vector<std::string> errors;
  while (configured_type_iter != configured_types.end() &&
         expected_type_iter != expected_types.end()) {
    if (configured_type_iter->first == expected_type_iter->first) {
      // For expected fields we also place requirements on the value types.
      if (!MessageDifferencer::Equals(expected_type_iter->second,
                                      configured_type_iter->second)) {
        errors.push_back(
            absl::StrCat(configured_type_iter->first,
                         " does not match the expected type definition ",
                         expected_type_iter->second.ShortDebugString()));
      }
      ++configured_type_iter;
      ++expected_type_iter;
    } else if (configured_type_iter->first < expected_type_iter->first) {
      // The pushed P4Info file can have extra values without it being an issue.
      LOG(WARNING) << "P4Info has extra type: " << configured_type_iter->first;
      ++configured_type_iter;
    } else {
      // The pushed P4Info cannot be missing any of the expected fields.
      errors.push_back(absl::StrCat(expected_type_iter->first, " is missing"));
      ++expected_type_iter;
    }
  }
  if (!errors.empty()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "P4 type not supported by P4Info: "
           << absl::StrJoin(errors, ", ");
  }
  return absl::OkStatus();
}

absl::Status ValidateP4Info(const p4::config::v1::P4Info& p4info) {
  RETURN_IF_ERROR(ValidatePacketIo(p4info));
  RETURN_IF_ERROR(ValidateTypes(p4info));
  return absl::OkStatus();
}

}  // namespace p4rt_app
