// Copyright (c) 2025, Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "dvaas/test_insights.h"

#include <algorithm>
#include <cstdint>
#include <optional>
#include <queue>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/btree_map.h"
#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/types/span.h"
#include "dvaas/packet_trace.pb.h"
#include "dvaas/test_vector.h"
#include "dvaas/test_vector.pb.h"
#include "gutil/proto.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/packetlib/packetlib.pb.h"

namespace dvaas {

// Action name indicating there is no information about the action applied to
// the packet for the given table (this indicated no packet trace was found).
constexpr absl::string_view kUnknownAction = "unknown";
// Action name indicating a table entry was hit but the action itself is not
// known (due to incomplete trace).
constexpr absl::string_view kHitAction = "hit";
// Action name indicating that no table entry hit in the table.
constexpr absl::string_view kTableMissAction = "miss";
// Action name indicating the table entry contains an action set.
constexpr absl::string_view kActionSet = "action_set";
// Action name indicating the table was not applied on the packet.
constexpr absl::string_view kNotAppliedAction = "not applied";

namespace {

constexpr absl::string_view kPacketFieldNotKnownOrPresent = "-";

// Values for interesting features of input packet.
struct SwitchInputFeatures {
  std::string type{kPacketFieldNotKnownOrPresent};
  std::string port{kPacketFieldNotKnownOrPresent};
  std::string ethernet_source{kPacketFieldNotKnownOrPresent};
  std::string ethernet_destination{kPacketFieldNotKnownOrPresent};
  std::string ethernet_ethertype{kPacketFieldNotKnownOrPresent};
  std::string vlan_id{kPacketFieldNotKnownOrPresent};
  std::string vlan_ethertype{kPacketFieldNotKnownOrPresent};
  std::string ip_src{kPacketFieldNotKnownOrPresent};
  std::string ip_dst{kPacketFieldNotKnownOrPresent};
  std::string ip_ttl{kPacketFieldNotKnownOrPresent};
  std::string ip_dscp{kPacketFieldNotKnownOrPresent};
  std::string ip_protocol{kPacketFieldNotKnownOrPresent};
  std::string entire_packet;
};

inline std::string SwitchInputFeaturesCsvHeader() {
  return absl::StrJoin(
      {
          "input_type",
          "input_port",
          "input_eth_src",
          "input_eth_dst",
          "input_eth_ethertype",
          "input_vlan_id",
          "input_vlan_ethertype",
          "input_ip_src",
          "input_ip_dst",
          "input_ip_ttl",
          "input_ip_dscp",
          "input_ip_protocol",
          "input_packet",
      },
      ",");
}

inline std::string ToCsvRow(const SwitchInputFeatures& features) {
  return absl::StrJoin(
      {
          features.type,
          features.port,
          features.ethernet_source,
          features.ethernet_destination,
          features.ethernet_ethertype,
          features.vlan_id,
          features.vlan_ethertype,
          features.ip_src,
          features.ip_dst,
          features.ip_ttl,
          features.ip_dscp,
          features.ip_protocol,
          features.entire_packet,
      },
      ",");
}

// Values for various features of a single packet test.
// The fields in the struct correspond to columns in the test insights table and
// each instance corresponds to one row in the table.
struct TestInsightsRow {
  int id;
  std::optional<int> functional_cluster_id;
  std::vector<std::string> actions;
  std::string acceptable_outcomes;
  std::optional<std::string> actual_outcome;
  std::optional<bool> test_pass;
  SwitchInputFeatures input_features;
};

absl::StatusOr<SwitchInputFeatures> GetSwitchInputFeatures(
    const SwitchInput& input) {
  SwitchInputFeatures features;
  features.type = input.Type_Name(input.type());
  features.port = input.packet().port();
  features.entire_packet = gutil::PrintShortTextProto(input.packet());

  const packetlib::Packet& packet = input.packet().parsed();
  if (packet.headers().empty())
    return absl::InvalidArgumentError("Packet has no headers");
  if (!packet.headers().at(0).has_ethernet_header())
    return absl::InvalidArgumentError(
        "Packet does not start with an ethernet header");

  const auto& ethernet_header = packet.headers().at(0).ethernet_header();
  features.ethernet_source = ethernet_header.ethernet_source();
  features.ethernet_destination = ethernet_header.ethernet_destination();
  features.ethernet_ethertype = ethernet_header.ethertype();

  if (packet.headers().size() < 2) return features;

  packetlib::Header next_header = packet.headers().at(1);

  if (next_header.has_vlan_header()) {
    const auto& vlan_header = next_header.vlan_header();
    features.vlan_id = vlan_header.vlan_identifier();
    features.vlan_ethertype = vlan_header.ethertype();
    if (packet.headers().size() < 3) return features;
    next_header = packet.headers().at(2);
  }

  if (next_header.has_ipv4_header()) {
    const auto& ipv4_header = next_header.ipv4_header();
    features.ip_src = ipv4_header.ipv4_source();
    features.ip_dst = ipv4_header.ipv4_destination();
    features.ip_ttl = ipv4_header.ttl();
    features.ip_dscp = ipv4_header.dscp();
    features.ip_protocol = ipv4_header.protocol();
  }

  if (next_header.has_ipv6_header()) {
    const auto& ipv6_header = next_header.ipv6_header();
    features.ip_src = ipv6_header.ipv6_source();
    features.ip_dst = ipv6_header.ipv6_destination();
    features.ip_ttl = ipv6_header.hop_limit();
    features.ip_dscp = ipv6_header.dscp();
    features.ip_protocol = ipv6_header.next_header();
  }

  return features;
}

// Topologically sorts the partial orders and returns a total order.
// Precondition: The partial orders are consistent (i.e., no cycles).
absl::StatusOr<std::vector<std::string>> GetTotalOrderFromPartialOrders(
    std::vector<std::vector<std::string>>& partial_orders) {
  struct Node {
    absl::flat_hash_set<std::string> parents, children;
  };
  absl::flat_hash_map<std::string, Node> node_by_name;
  std::vector<std::string> total_order;

  // Build the graph.
  for (const auto& partial_order : partial_orders) {
    for (int64_t i = 1; i < partial_order.size(); ++i) {
      const std::string u = partial_order[i - 1];
      const std::string v = partial_order[i];
      node_by_name[u].children.insert(v);
      node_by_name[v].parents.insert(u);
    }
  }

  // Enqueue nodes with no parent.
  std::queue<std::string> queue;
  for (auto& [name, node] : node_by_name) {
    if (node.parents.empty()) {
      queue.push(name);
    }
  }

  // Process nodes in topological order.
  while (!queue.empty()) {
    std::string u = queue.front();
    queue.pop();
    total_order.push_back(u);

    // Remove `u` as a parent of its children.
    for (const std::string& v : node_by_name[u].children) {
      node_by_name[v].parents.erase(u);
      if (node_by_name[v].parents.empty()) queue.push(v);
    }
  }

  // Check for cycles.
  if (total_order.size() != node_by_name.size()) {
    return absl::FailedPreconditionError("Cycle detected in partial orders");
  }

  return total_order;
}

// Infers the order of table application tables from the given
// packet traces. Tables in `ir_p4info` that are not found in the packet
// traces are ordered lexicographically and appended to the end of the
// returned order.
absl::StatusOr<std::vector<std::string>> InferOrderOfTablesFromPacketTraces(
    absl::Span<const dvaas::PacketTestVector> test_vectors,
    const pdpi::IrP4Info& ir_p4info) {
  // Get SAI tables from P4Info.
  absl::flat_hash_set<std::string> target_tables;
  for (const auto& [table_name, table] : ir_p4info.tables_by_name()) {
    // Avoid BMv2's internal tables.
    if (table.preamble().id() == 0) continue;
    // Avoid v1model auxiliary tables.
    if (table_name == "egress_port_loopback_table") continue;
    if (table_name == "v1model_auxiliary_vlan_membership_table") continue;
    if (table_name == "ingress_clone_table") continue;
    target_tables.insert(table.preamble().name());
  }

  // Infer partial orders from packet traces.
  std::vector<std::vector<std::string>> tables_partial_orders;
  for (const dvaas::PacketTestVector& test_vector : test_vectors) {
    for (const auto& acceptable_output : test_vector.acceptable_outputs()) {
      if (!acceptable_output.has_packet_trace()) continue;
      const dvaas::PacketTrace& packet_trace = acceptable_output.packet_trace();

      std::vector<std::string> tables_partial_order;
      absl::flat_hash_set<std::string> seen_tables;
      for (const auto& event : packet_trace.events()) {
        if (event.has_table_apply()) {
          const auto& table_name = event.table_apply().table_name();
          if (!target_tables.contains(table_name)) continue;
	  if (!seen_tables.insert(table_name).second) {
            // Break potential cycles in the partial table application order
            // inferred from the packet trace. Note that the packet traces
            // contain events for multiple packets (e.g. in case of mirroring,
            // copying, multicast) or packets recirculating through the
            // pipeline. This shows up as repetition of table applications.
            // Therefore, as soon as we encounter a re-application of the same
            // table, we stop considering the rest of the events in the packet
            // trace. This may lose some partial orders but given that
            // information is only used to sort the columns in the test insights
            // table for ease of readability, it is a reasonable heuristic. Also
            // note that there is no risk of wrong partial order inference
            // because the trace events are ordered in a way that there is no
            // interleaving of events corresponding to different packets.
            break;
          }
          tables_partial_order.push_back(table_name);
        }
      }
      tables_partial_orders.push_back(tables_partial_order);
    }
  }
  // Get total order from partial orders.
  ASSIGN_OR_RETURN(const std::vector<std::string> used_tables_total_order,
                   GetTotalOrderFromPartialOrders(tables_partial_orders));

  // Lexicographically sort the unused tables (from `target_tables`) and append
  // them to the end of the total order.
  absl::flat_hash_set<std::string> used_tables(used_tables_total_order.begin(),
                                               used_tables_total_order.end());
  absl::btree_set<std::string> unused_target_tables;
  for (const auto& table : target_tables) {
    if (!used_tables.contains(table)) {
      unused_target_tables.insert(table);
    }
  }
  std::vector<std::string> tables_total_order = used_tables_total_order;
  for (const auto& table : unused_target_tables) {
    tables_total_order.push_back(table);
  }

  return tables_total_order;
}

// For the given list of fully qualified table names, returns the corresponding
// list of table aliases (as defined in `ir_p4info`).
absl::StatusOr<std::vector<std::string>> GetTableAliases(
    const std::vector<std::string>& fully_qualified_table_names,
    const pdpi::IrP4Info& ir_p4info) {
  // Build a map from fully qualified table name to table alias.
  absl::flat_hash_map<std::string, std::string>
      fully_qualified_table_name_to_alias;
  for (const auto& [table_name, table] : ir_p4info.tables_by_name()) {
    fully_qualified_table_name_to_alias[table.preamble().name()] = table_name;
  }

  std::vector<std::string> table_aliases;
  for (const auto& table : fully_qualified_table_names) {
    const auto it = fully_qualified_table_name_to_alias.find(table);
    if (it == fully_qualified_table_name_to_alias.end()) {
      return absl::InternalError("Table alias not found for table: " + table);
    } else {
      table_aliases.push_back(it->second);
    }
  }
  return table_aliases;
}

// For each table, returns the set of actions that were applied according to
// the given packet traces.
absl::btree_map<std::string, absl::btree_set<std::string>> GetTableToActions(
    const std::vector<dvaas::PacketTrace>& packet_traces) {
  absl::btree_map<std::string, absl::btree_set<std::string>> table_to_actions;

  for (const auto& packet_trace : packet_traces) {
    for (const auto& event : packet_trace.events()) {
      if (event.has_table_apply()) {
        const std::string& table_name = event.table_apply().table_name();
        std::string action_name = std::string(kHitAction);
        if (event.table_apply().has_miss()) {
          action_name = std::string(kTableMissAction);
        } else {
          if (event.table_apply().hit().has_table_entry()) {
            const auto& table_entry = event.table_apply().hit().table_entry();
            if (table_entry.has_action()) {
              action_name = table_entry.action().name();
            } else if (table_entry.has_action_set()) {
              absl::btree_set<std::string> action_set;
              for (const auto& action : table_entry.action_set().actions()) {
                action_set.insert(action.action().name());
              }
              action_name = absl::Substitute("$0($1)", kActionSet,
                                             absl::StrJoin(action_set, "/"));
            }
          }
        }
        table_to_actions[table_name].insert(action_name);
      }
    }
  }
  return table_to_actions;
}

// Return a text description of the switch output.
std::string GetSwitchOutputDescription(const SwitchOutput& switch_output) {
  std::string outcome = "drop";
  if (!switch_output.packets().empty() && !switch_output.packet_ins().empty()) {
    outcome = "punt_and_forward";
  } else if (!switch_output.packets().empty()) {
    outcome = "forward";
  } else if (!switch_output.packet_ins().empty()) {
    outcome = "punt";
  }
  return outcome;
}

// Return a text description of the acceptable outcomes.
std::string GetAcceptableOutcomesDescription(
    const dvaas::PacketTestVector& packet_test_vector) {
  absl::btree_set<std::string> acceptable_outcomes;
  for (const auto& acceptable_output :
       packet_test_vector.acceptable_outputs()) {
    acceptable_outcomes.insert(GetSwitchOutputDescription(acceptable_output));
  }
  return absl::StrJoin(acceptable_outcomes, "/");
}

// Returns a list of test insights rows corresponding to the given list of
// packet test vectors.
absl::StatusOr<std::vector<TestInsightsRow>> GetTestInsightsRows(
    absl::Span<const dvaas::PacketTestVector> packet_test_vectors,
     const std::vector<std::string>& ordered_tables) {
  std::vector<TestInsightsRow> rows;

  // Create one row per packet test vector.
  for (const PacketTestVector& packet_test_vector : packet_test_vectors) {
    std::vector<dvaas::PacketTrace> packet_traces;
    for (const auto& acceptable_output :
         packet_test_vector.acceptable_outputs()) {
      if (acceptable_output.has_packet_trace()) {
        packet_traces.push_back(acceptable_output.packet_trace());
      }
    }

    absl::btree_map<std::string, absl::btree_set<std::string>>
        table_to_actions = GetTableToActions(packet_traces);

    std::vector<std::string> ordered_actions;
    for (const auto& table : ordered_tables) {
      if (packet_traces.empty()) {
        ordered_actions.push_back(std::string(kUnknownAction));
      } else {
        const auto it = table_to_actions.find(table);
        if (it == table_to_actions.end()) {
          ordered_actions.push_back(std::string(kNotAppliedAction));
        } else {
          ordered_actions.push_back(absl::StrJoin(it->second, "/"));
        }
      }
    }

    ASSIGN_OR_RETURN(int id, ExtractIdFromTaggedPacketInHex(
                                 packet_test_vector.input().packet().hex()));
    ASSIGN_OR_RETURN(const SwitchInputFeatures input_features,
                     GetSwitchInputFeatures(packet_test_vector.input()));
    rows.push_back({
        .id = id,
        .actions = ordered_actions,
        .acceptable_outcomes =
            GetAcceptableOutcomesDescription(packet_test_vector),
        .input_features = input_features,
    });
  }

  // Cluster the rows. Put rows with same (action, outcomes) in the same
  // cluster.
  struct FunctionalClusterComparator {
    bool operator()(const TestInsightsRow& lhs,
                    const TestInsightsRow& rhs) const {
      if (lhs.actions != rhs.actions) return lhs.actions < rhs.actions;
      return lhs.acceptable_outcomes < rhs.acceptable_outcomes;
    }
  };
  absl::btree_map<TestInsightsRow, int, FunctionalClusterComparator>
      row_to_functional_cluster_id;
  for (auto& row : rows) {
    row_to_functional_cluster_id.insert(
        {row, row_to_functional_cluster_id.size()});
  row.functional_cluster_id = row_to_functional_cluster_id.at(row);
  }

  return rows;
}

}  // namespace

absl::StatusOr<std::string> GetTestInsightsTableAsCsv(
    absl::Span<const dvaas::PacketTestVector> packet_test_vectors,
    const pdpi::IrP4Info& ir_p4info) {
  std::string csv;

  ASSIGN_OR_RETURN(
      const std::vector<std::string> ordered_tables,
      InferOrderOfTablesFromPacketTraces(packet_test_vectors, ir_p4info));

  ASSIGN_OR_RETURN(std::vector<TestInsightsRow> rows,
                   GetTestInsightsRows(packet_test_vectors, ordered_tables));

  // Sort rows, placing rows with the same functional cluster near each other.
  std::sort(rows.begin(), rows.end(),
            [](const TestInsightsRow& lhs, const TestInsightsRow& rhs) {
              if (lhs.functional_cluster_id != rhs.functional_cluster_id)
                return lhs.functional_cluster_id < rhs.functional_cluster_id;
              return lhs.id < rhs.id;
            });

  // Create CSV header.
  ASSIGN_OR_RETURN(std::vector<std::string> ordered_table_aliases,
                   GetTableAliases(ordered_tables, ir_p4info));
  absl::SubstituteAndAppend(&csv,
                            "test vector id,functional cluster,$0, "
                            "acceptable outcomes,$1\n",
                            absl::StrJoin(ordered_table_aliases, ","),
                            SwitchInputFeaturesCsvHeader());
  // Add CSV rows.
  for (const auto& row : rows) {
    absl::SubstituteAndAppend(
        &csv, "$0,$1,$2,$3,$4\n", row.id, *row.functional_cluster_id,
        absl::StrJoin(row.actions, ","), row.acceptable_outcomes,
        ToCsvRow(row.input_features));
  }

  return csv;
}

absl::StatusOr<std::string> GetTestInsightsTableAsCsv(
    const PacketTestOutcomes& test_outcomes, const pdpi::IrP4Info& ir_p4info) {
  std::string csv;

  std::vector<PacketTestVector> packet_test_vectors;
  packet_test_vectors.reserve(test_outcomes.outcomes_size());
  for (const auto& test_outcome : test_outcomes.outcomes()) {
    packet_test_vectors.push_back(test_outcome.test_run().test_vector());
  }

  ASSIGN_OR_RETURN(
      const std::vector<std::string> ordered_tables,
      InferOrderOfTablesFromPacketTraces(packet_test_vectors, ir_p4info));

  ASSIGN_OR_RETURN(std::vector<TestInsightsRow> rows,
                   GetTestInsightsRows(packet_test_vectors, ordered_tables));

  int index = 0;
  for (const PacketTestOutcome& test_outcome : test_outcomes.outcomes()) {
    rows[index].test_pass = !test_outcome.test_result().has_failure();
    rows[index].actual_outcome =
        GetSwitchOutputDescription(test_outcome.test_run().actual_output());
    ++index;
  }

  // Sort rows, placing rows with the same functional cluster near each other.
  std::sort(rows.begin(), rows.end(),
            [](const TestInsightsRow& lhs, const TestInsightsRow& rhs) {
              if (lhs.functional_cluster_id != rhs.functional_cluster_id)
                return lhs.functional_cluster_id < rhs.functional_cluster_id;
              return lhs.id < rhs.id;
            });

  // Create CSV header.
  ASSIGN_OR_RETURN(std::vector<std::string> ordered_table_aliases,
                   GetTableAliases(ordered_tables, ir_p4info));
  absl::SubstituteAndAppend(&csv,
                            "test vector id,functional cluster,$0,"
                            "acceptable outcomes,actual outcome,test "
                            "pass,$1\n",
                            absl::StrJoin(ordered_table_aliases, ","),
                            SwitchInputFeaturesCsvHeader());
  // Add CSV rows.
  for (const auto& row : rows) {
    absl::SubstituteAndAppend(
        &csv, "$0,$1,$2,$3,$4,$5,$6\n", row.id, *row.functional_cluster_id,
        absl::StrJoin(row.actions, ","), row.acceptable_outcomes,
        *row.actual_outcome, (*row.test_pass ? "pass" : "fail"),
        ToCsvRow(row.input_features));
  }

  return csv;
}

}  // namespace dvaas
