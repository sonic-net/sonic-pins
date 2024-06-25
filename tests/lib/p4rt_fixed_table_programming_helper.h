// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
#ifndef GOOGLE_TESTS_LIB_P4RT_FIXED_TABLE_PROGRAMMING_HELPER_H_
#define GOOGLE_TESTS_LIB_P4RT_FIXED_TABLE_PROGRAMMING_HELPER_H_
#include <optional>
#include <utility>
#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"

namespace gpins {

absl::StatusOr<p4::v1::Update> RouterInterfaceTableUpdate(
    const pdpi::IrP4Info& ir_p4_info, p4::v1::Update::Type type,
    absl::string_view router_interface_id, absl::string_view port,
    absl::string_view src_mac);

absl::StatusOr<p4::v1::Update> NeighborTableUpdate(
    const pdpi::IrP4Info& ir_p4_info, p4::v1::Update::Type type,
    absl::string_view router_interface_id, absl::string_view neighbor_id,
    absl::string_view dst_mac);

absl::StatusOr<p4::v1::Update> NexthopTableUpdate(
    const pdpi::IrP4Info& ir_p4_info, p4::v1::Update::Type type,
    absl::string_view nexthop_id, absl::string_view router_interface_id,
    absl::string_view neighbor_id);

absl::StatusOr<p4::v1::Update> VrfTableUpdate(const pdpi::IrP4Info& ir_p4_info,
                                              p4::v1::Update::Type type,
                                              absl::string_view vrf_id);

// The fixed IP tables (ipv4_table and ipv6_table) allow for mutliple action
// (e.g. drop or set_next_hop). The IpTableOptions object provides a superset of
// all IP table settings, but not all combinations are valid. For example:
//   * if action=kDrop then nexthop_id should not be set
//   * if action=kSetNextHopId then nexthop_id should be set.
struct IpTableOptions {
  enum class Action { kDrop, kSetNextHopId };

  // Match fields not marked optional must be set.
  std::string vrf_id;
  std::optional<std::pair<std::string, int>> dst_addr_lpm;  // LPM

  // Action and Action Parameters.
  Action action = Action::kDrop;
  std::optional<std::string> nexthop_id;
};

absl::StatusOr<p4::v1::Update> Ipv4TableUpdate(
    const pdpi::IrP4Info& ir_p4_info, p4::v1::Update::Type type,
    const IpTableOptions& ip_options);

absl::StatusOr<p4::v1::Update> Ipv6TableUpdate(
    const pdpi::IrP4Info& ir_p4_info, p4::v1::Update::Type type,
    const IpTableOptions& ip_options);

// The L3 admit table can optionally admit packets based on the ingress port.
struct L3AdmitOptions {
  int priority;
  std::pair<std::string, std::string> dst_mac;  // Ternary
  std::optional<std::string> in_port;
};

absl::StatusOr<p4::v1::Update> L3AdmitTableUpdate(
    const pdpi::IrP4Info& ir_p4_info, p4::v1::Update::Type type,
    const L3AdmitOptions& options);

absl::StatusOr<p4::v1::Update> L3AdmitAllTableUpdate(
    const pdpi::IrP4Info& ir_p4_info, p4::v1::Update::Type type);

// WCMP entries should always have a nexthop_id and weight, but can optionally
// set a watch port.
struct WcmpAction {
  std::string nexthop_id;
  int32_t weight;
  std::optional<std::string> watch_port;
};

absl::StatusOr<p4::v1::Update> WcmpGroupTableUpdate(
    const pdpi::IrP4Info& ir_p4_info, p4::v1::Update::Type type,
    absl::string_view wcmp_group_id, const std::vector<WcmpAction>& actions);

}  // namespace gpins

#endif  // GOOGLE_TESTS_LIB_P4RT_FIXED_TABLE_PROGRAMMING_HELPER_H_
