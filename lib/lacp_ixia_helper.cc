// Copyright 2025 Google LLC
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
#include "lib/lacp_ixia_helper.h"

#include <string>
#include <string_view>
#include <variant>
#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "gutil/overload.h"
#include "gutil/status.h"
#include "lib/ixia_helper.h"
#include "thinkit/generic_testbed.h"

namespace pins_test::ixia {
namespace {

// Returns a visitor that sets the value of a field in a traffic item, using
// single value if a string is provided, or a value list if a vector is
// provided.
auto GetValueOrListVisitor(std::string_view traffic_item, int field_index,
                           thinkit::GenericTestbed& testbed) {
  return gutil::Overload(
      [=, &testbed](const std::string& value) {
        return SetFieldSingleValue(traffic_item, kLacpStackIndex, field_index,
                                   value, testbed);
      },
      [=, &testbed](const std::vector<std::string>& values) {
        return SetFieldValueList(traffic_item, kLacpStackIndex, field_index,
                                 values, testbed);
      });
}

}  // namespace

absl::StatusOr<std::string> CreateLacpTrafficItem(
    std::string_view vport, const LacpInfo& lacp_info,
    const LacpTrafficItemOptions& options, thinkit::GenericTestbed& testbed) {
  ASSIGN_OR_RETURN(std::string traffic_item, IxiaSession(vport, testbed));
  if (options.packet_count.has_value()) {
    RETURN_IF_ERROR(
        SetFrameCount(traffic_item, *options.packet_count, testbed));
  }
  RETURN_IF_ERROR(
      SetFrameRate(traffic_item, options.packets_per_second, testbed));

  // Because Ixia includes an FCS with the LACP header, we need to replace the
  // default Ethernet header (which includes FCS) with Ethernet II without FCS.
  // This requires first adding the new header first before removing the old
  // one.
  RETURN_IF_ERROR(ixia::AppendProtocolAtStack(
      traffic_item, ixia::kEthernetWithoutFcsName,
      absl::StrCat(ixia::kEthernetStackIndex), testbed));
  RETURN_IF_ERROR(ixia::RemoveProtocolAtIndex(
      traffic_item, ixia::kEthernetStackIndex, testbed));

  // Set Ethernet header fields.
  RETURN_IF_ERROR(SetDestMac(traffic_item, kLacpDestinationMac, testbed));
  RETURN_IF_ERROR(SetSrcMac(traffic_item, lacp_info.source_mac, testbed));

  // Add the LACP header.
  // Ixia handles a lot of default values (assuming not overwritten), like
  // setting the Ethernet header's ethertype to 0x8809 and many LACP fields like
  // subtype to 1.
  RETURN_IF_ERROR(AppendProtocolAtStack(traffic_item, kLacpHeaderName,
                                        absl::StrCat(kEthernetStackIndex),
                                        testbed));

  // Set actor fields.
  RETURN_IF_ERROR(std::visit(
      GetValueOrListVisitor(traffic_item, LacpField::kActorSystemId, testbed),
      lacp_info.actor.system_id));
  RETURN_IF_ERROR(
      std::visit(GetValueOrListVisitor(
                     traffic_item, LacpField::kActorSystemPriority, testbed),
                 lacp_info.actor.system_priority));
  RETURN_IF_ERROR(std::visit(
      GetValueOrListVisitor(traffic_item, LacpField::kActorKey, testbed),
      lacp_info.actor.key));
  RETURN_IF_ERROR(std::visit(
      GetValueOrListVisitor(traffic_item, LacpField::kActorPortId, testbed),
      lacp_info.actor.port_id));
  RETURN_IF_ERROR(
      std::visit(GetValueOrListVisitor(traffic_item,
                                       LacpField::kActorPortPriority, testbed),
                 lacp_info.actor.port_priority));
  RETURN_IF_ERROR(std::visit(
      GetValueOrListVisitor(traffic_item, LacpField::kActorState, testbed),
      lacp_info.actor.state));

  // Set partner fields.
  RETURN_IF_ERROR(std::visit(
      GetValueOrListVisitor(traffic_item, LacpField::kPartnerSystemId, testbed),
      lacp_info.partner.system_id));
  RETURN_IF_ERROR(
      std::visit(GetValueOrListVisitor(
                     traffic_item, LacpField::kPartnerSystemPriority, testbed),
                 lacp_info.partner.system_priority));
  RETURN_IF_ERROR(std::visit(
      GetValueOrListVisitor(traffic_item, LacpField::kPartnerKey, testbed),
      lacp_info.partner.key));
  RETURN_IF_ERROR(std::visit(
      GetValueOrListVisitor(traffic_item, LacpField::kPartnerPortId, testbed),
      lacp_info.partner.port_id));
  RETURN_IF_ERROR(
      std::visit(GetValueOrListVisitor(
                     traffic_item, LacpField::kPartnerPortPriority, testbed),
                 lacp_info.partner.port_priority));
  RETURN_IF_ERROR(std::visit(
      GetValueOrListVisitor(traffic_item, LacpField::kPartnerState, testbed),
      lacp_info.partner.state));

  return traffic_item;
}

}  // namespace pins_test::ixia
