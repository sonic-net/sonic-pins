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

#include "p4_pdpi/sequencing.h"

#include <algorithm>
#include <cstdint>
#include <optional>
#include <queue>
#include <string>
#include <utility>
#include <vector>

#include "absl/algorithm/container.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/types/span.h"
#include "boost/graph/adjacency_list.hpp"
#include "glog/logging.h"
#include "gutil/collections.h"
#include "gutil/status.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/sequencing_util.h"

namespace pdpi {
namespace {
using ::p4::v1::Action_Param;
using ::p4::v1::Update;
using ::p4::v1::WriteRequest;

// We require boost::in_degree, which requires bidirectionalS.
using Graph =
    boost::adjacency_list<boost::hash_setS, boost::vecS, boost::bidirectionalS>;
// Boost uses integers to identify vertices.
using Vertex = int;

// Describing a referenced match field (table + match field) as well as the
// value of that match field (in this order).
using ReferencedValue = std::tuple<std::string, std::string, std::string>;
// The mapping of a referenced value to vertices that are being referred to by
// that referenced value.
using ReferencedValueToVertices =
    absl::flat_hash_map<ReferencedValue, absl::flat_hash_set<Vertex>>;

absl::StatusOr<absl::optional<std::string>> GetMatchFieldValue(
    const IrTableDefinition& ir_table_definition, const Update& update,
    const std::string& match_field) {
  ASSIGN_OR_RETURN(
      const auto* match_field_definition,
      gutil::FindPtrOrStatus(ir_table_definition.match_fields_by_name(),
                             match_field),
      _ << "Failed to build dependency graph: Match field with name "
        << match_field << " does not exist.");
  int32_t match_field_id = match_field_definition->match_field().id();
  for (const auto& match : update.entity().table_entry().match()) {
    if (match.field_id() == match_field_id) {
      if (match.has_exact()) {
        return match.exact().value();
      } else if (match.has_optional()) {
        return match.optional().value();
      }
    }
  }
  return absl::nullopt;
}

// Given the ReferencedValue of the current_vertex, record all dependencies.
void RecordDependenciesForReferencedValue(absl::Span<const Update> all_vertices,
                                          Vertex current_vertex,
                                          ReferencedValue referenced_value,
                                          ReferencedValueToVertices& indices,
                                          Graph& graph) {
  for (Vertex referred_update_index : indices[referenced_value]) {
    const Update& referred_update = all_vertices[referred_update_index];
    if ((all_vertices[current_vertex].type() == p4::v1::Update::INSERT ||
         all_vertices[current_vertex].type() == p4::v1::Update::MODIFY) &&
        referred_update.type() == p4::v1::Update::INSERT) {
      boost::add_edge(referred_update_index, current_vertex, graph);
    } else if (all_vertices[current_vertex].type() == p4::v1::Update::DELETE &&
               referred_update.type() == p4::v1::Update::DELETE) {
      boost::add_edge(current_vertex, referred_update_index, graph);
    }
  }
}

// Records and updates the dependency graph for for the given action invocation.
absl::Status RecordDependenciesForActionInvocation(
    absl::Span<const Update> all_vertices, const IrActionDefinition& ir_action,
    absl::Span<const Action_Param* const> params, Vertex current_vertex,
    ReferencedValueToVertices& indices, Graph& graph) {
  for (const Action_Param* const param : params) {
    ASSIGN_OR_RETURN(
        const auto* param_definition,
        gutil::FindPtrOrStatus(ir_action.params_by_id(), param->param_id()),
        _ << "Failed to build dependency graph: Aciton param with ID "
          << param->param_id() << " does not exist.");
    for (const auto& ir_reference : param_definition->references()) {
      ReferencedValue referenced_value = {
          ir_reference.table(), ir_reference.match_field(), param->value()};
      RecordDependenciesForReferencedValue(all_vertices, current_vertex,
                                           referenced_value, indices, graph);
    }
  }
  return absl::OkStatus();
}

// Builds the dependency graph between updates. An edge from u to v indicates
// that v depends on u.
absl::StatusOr<Graph> BuildDependencyGraph(const IrP4Info& info,
                                           absl::Span<const Update> updates) {
  // Graph containing one node per update.
  Graph graph(updates.size());

  // Build indices to map references to the set of updates of that key.
  ReferencedValueToVertices indices;
  for (int update_index = 0; update_index < updates.size(); update_index++) {
    const Update& update = updates[update_index];
    ASSIGN_OR_RETURN(
        const IrTableDefinition* ir_table_definition,
        gutil::FindPtrOrStatus(info.tables_by_id(),
                               update.entity().table_entry().table_id()),
        _ << "Failed to build dependency graph: Table with ID "
          << update.entity().table_entry().table_id() << " does not exist.");
    const std::string& update_table_name =
        ir_table_definition->preamble().alias();
    for (const auto& ir_reference : info.references()) {
      if (update_table_name != ir_reference.table()) continue;
      ASSIGN_OR_RETURN(absl::optional<std::string> value,
                       GetMatchFieldValue(*ir_table_definition, update,
                                          ir_reference.match_field()));
      if (value.has_value()) {
        ReferencedValue reference_value = {
            ir_reference.table(), ir_reference.match_field(), value.value()};
        indices[reference_value].insert(update_index);
      }
    }
  }

  // Build dependency graph.
  for (int update_index = 0; update_index < updates.size(); update_index++) {
    const Update& update = updates[update_index];
    const p4::v1::TableEntry& table_entry = update.entity().table_entry();
    const p4::v1::TableAction& action = table_entry.action();
    ASSIGN_OR_RETURN(
        const IrTableDefinition* ir_table,
        gutil::FindPtrOrStatus(info.tables_by_id(), table_entry.table_id()),
        _ << "Failed to build dependency graph: Table with ID "
          << table_entry.table_id() << " does not exist.");

    // References from match fields to match fields.
    for (const auto& match_field : table_entry.match()) {
      ASSIGN_OR_RETURN(
          const auto* match_field_definition,
          gutil::FindPtrOrStatus(ir_table->match_fields_by_id(),
                                 match_field.field_id()),
          _ << "Failed to build dependency graph: Match field with ID "
            << match_field.field_id() << " does not exist.");
      for (const auto& ir_reference : match_field_definition->references()) {
        switch (match_field_definition->match_field().match_type()) {
          case p4::config::v1::MatchField::EXACT: {
            ReferencedValue referenced_value = {ir_reference.table(),
                                                ir_reference.match_field(),
                                                match_field.exact().value()};
            RecordDependenciesForReferencedValue(
                updates, update_index, referenced_value, indices, graph);
            break;
          }
          case p4::config::v1::MatchField::OPTIONAL: {
            ReferencedValue referenced_value = {ir_reference.table(),
                                                ir_reference.match_field(),
                                                match_field.optional().value()};
            RecordDependenciesForReferencedValue(
                updates, update_index, referenced_value, indices, graph);
            break;
          }
          default: {
            return gutil::InvalidArgumentErrorBuilder()
                   << "Only exact or optional match fields can use @refers_to.";
          }
        }
      }
    }

    // References from action parameters to match fields.
    switch (action.type_case()) {
      case p4::v1::TableAction::kAction: {
        ASSIGN_OR_RETURN(
            const IrActionDefinition* ir_action,
            gutil::FindPtrOrStatus(info.actions_by_id(),
                                   action.action().action_id()),
            _ << "Failed to build dependency graph: Action with ID "
              << action.action().action_id() << " does not exist.");
        RETURN_IF_ERROR(RecordDependenciesForActionInvocation(
            updates, *ir_action, action.action().params(), update_index,
            indices, graph));
        break;
      }
      case p4::v1::TableAction::kActionProfileActionSet: {
        const p4::v1::ActionProfileActionSet& action_profile_set =
            action.action_profile_action_set();

        for (const auto& action_profile :
             action_profile_set.action_profile_actions()) {
          ASSIGN_OR_RETURN(
              const IrActionDefinition* ir_action,
              gutil::FindPtrOrStatus(info.actions_by_id(),
                                     action_profile.action().action_id()),
              _ << "Failed to build dependency graph: Action with ID "
                << action_profile.action().action_id() << " does not exist.");
          RETURN_IF_ERROR(RecordDependenciesForActionInvocation(
              updates, *ir_action, action_profile.action().params(),
              update_index, indices, graph));
        }
        break;
      }
      default: {
        return gutil::UnimplementedErrorBuilder()
               << "Only kAction and kActionProfileActionSet are supported: "
               << action.DebugString();
      }
    }
  }
  return graph;
}
}  // namespace

absl::StatusOr<std::vector<p4::v1::WriteRequest>>
SequencePiUpdatesIntoWriteRequests(const IrP4Info& info,
                                   absl::Span<const Update> updates,
                                   std::optional<int> max_batch_size) {
  if (max_batch_size.has_value() && *max_batch_size <= 0) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Max batch size must be > 0. Max batch size: " << *max_batch_size;
  }

  std::vector<WriteRequest> requests;
  ASSIGN_OR_RETURN(const auto batches, SequencePiUpdatesInPlace(info, updates));
  for (const std::vector<int>& batch : batches) {
    WriteRequest request;
    for (int index : batch) {
      if (max_batch_size.has_value() &&
          request.updates_size() >= *max_batch_size) {
        requests.push_back(std::move(request));
        request = WriteRequest();
      }
      *request.add_updates() = updates[index];
    }
    requests.push_back(std::move(request));
  }
  return requests;
}

absl::StatusOr<std::vector<std::vector<int>>> SequencePiUpdatesInPlace(
    const IrP4Info& info, absl::Span<const Update> updates) {
  ASSIGN_OR_RETURN(Graph graph, BuildDependencyGraph(info, updates));

  std::vector<Vertex> roots;
  for (Vertex vertex : graph.vertex_set()) {
    if (boost::in_degree(vertex, graph) == 0) {
      roots.push_back(vertex);
    }
  }

  std::vector<std::vector<int>> batches;
  while (!roots.empty()) {
    // The roots have no incoming dependency edges, hence can be batched.
    // Sort them so order of input is retained in the output.
    std::sort(roots.begin(), roots.end());
    batches.push_back(roots);

    // Remove edges for old roots and add new roots.
    std::vector<Vertex> new_roots;
    for (Vertex root : roots) {
      for (const auto& edge : graph.out_edge_list(root)) {
        Vertex target = edge.get_target();
        // Is this the final `edge` into `target`?
        if (boost::in_degree(target, graph) == 1) new_roots.push_back(target);
      }
      boost::clear_out_edges(root, graph);
    }
    roots.swap(new_roots);
  }

  // Upon exiting the loop, no dependencies should remain.
  if (boost::num_edges(graph) != 0) {
    return gutil::InvalidArgumentErrorBuilder()
           << "The dependency graph generated during P4 update sequencing is "
              "cyclic. This indicates a cycle in @foreign_key dependencies in "
              "the P4 program.";
  }
  return batches;
}

// The implementation can be reduced to sorting INSERTS using
// SequencePiUpdatesIntoWriteRequests.
absl::Status SortTableEntries(const IrP4Info& info,
                              std::vector<p4::v1::TableEntry>& entries) {
  std::vector<Update> updates;
  updates.reserve(entries.size());
  for (const auto& entry : entries) {
    Update update;
    update.set_type(Update::INSERT);
    *update.mutable_entity()->mutable_table_entry() = std::move(entry);
    updates.push_back(update);
  }
  ASSIGN_OR_RETURN(std::vector<std::vector<int>> batches,
                   SequencePiUpdatesInPlace(info, updates));

  entries.clear();
  for (const std::vector<int>& batch : batches) {
    for (int update_index : batch) {
      entries.push_back(
          std::move(updates[update_index].entity().table_entry()));
    }
  }

  return absl::OkStatus();
}

absl::StatusOr<std::vector<p4::v1::Entity>> GetEntitiesUnreachableFromRoots(
    absl::Span<const p4::v1::Entity> entities,
    absl::FunctionRef<absl::StatusOr<bool>(const p4::v1::Entity&)>
        is_root_entity,
    const IrP4Info& ir_p4info) {
  absl::flat_hash_map<ReferredTableEntry, std::vector<int>>
      potentially_reachable_entries;
  std::vector<int> unreachable_indices;
  // `frontier_indices` stores indices for entries that could potentially refer
  // to other entries, but whose references have not been examined yet.
  std::queue<int> frontier_indices;
  absl::flat_hash_map<ReferenceRelationKey, ReferenceRelation>
      referred_relations = CreateReferenceRelations(ir_p4info);

  for (int i = 0; i < entities.size(); i++) {
    const p4::v1::Entity& entity = entities[i];
    ASSIGN_OR_RETURN(bool is_root_entity, is_root_entity(entity));
    if (is_root_entity) {
      // TODO: b/296443880 - Remove once MRIF entry collection is supported.
      if (entity.has_packet_replication_engine_entry()) {
        continue;
      }
      frontier_indices.push(i);
      continue;
    }
    if (!entity.has_table_entry()) {
      // TODO: b/302346101 - Add support for collection of all entities.
      return absl::UnimplementedError(
          absl::StrCat("Only entities of type table_entry can be garbage "
                       "collected. Entity: ",
                       entity.DebugString()));
    }
    const p4::v1::TableEntry& table_entry = entity.table_entry();
    // If the table that entries[i] belongs to is referred to, entries[i] is
    // potentially reachable. Else, entries[i] is not reachable.
    if (referred_relations.contains(ReferenceRelationKey{
            .referred_table_id = table_entry.table_id()})) {
      ASSIGN_OR_RETURN(ReferredTableEntry referrable_table_entry,
                       CreateReferrableTableEntry(ir_p4info, referred_relations,
                                                  table_entry));
      potentially_reachable_entries[referrable_table_entry].push_back(i);
    } else {
      LOG(WARNING) << "Found non-root entry that could never be reachable. "
                      "This probably indicates some mistake in is_root_entry "
                      "or the ir_p4info. Found entry: "
                   << table_entry.DebugString();
      unreachable_indices.push_back(i);
    }
  }

  // Expand frontier of reachable entries.
  // Pop an entry off the frontier and if that entry refers to some entries in
  // potentially_reachable_entries, move them from
  // `potentially_reachable_entries` to `frontier_indices`.
  while (!frontier_indices.empty()) {
    const ::p4::v1::TableEntry& frontier_entry =
        entities[frontier_indices.front()].table_entry();
    frontier_indices.pop();
    ASSIGN_OR_RETURN(
        std::vector<ReferredTableEntry> entries_referred_to_by_frontier_entry,
        EntriesReferredToByTableEntry(ir_p4info, frontier_entry));
    for (const ReferredTableEntry& referred_to_entry :
         entries_referred_to_by_frontier_entry) {
      if (auto it = potentially_reachable_entries.find(referred_to_entry);
          it != potentially_reachable_entries.end()) {
        absl::c_for_each(it->second, [&frontier_indices](int i) {
          frontier_indices.push(i);
        });
        potentially_reachable_entries.erase(it);
      }
    }
  }
  // By the end of frontier expansion all remaining potentially reachable
  // entries are not reachable.
  for (const auto& [unused, indices] : potentially_reachable_entries) {
    absl::c_for_each(indices, [&unreachable_indices](int i) {
      unreachable_indices.push_back(i);
    });
  }
  std::vector<p4::v1::Entity> unreachable_entities;
  unreachable_entities.reserve(unreachable_indices.size());

  // Returns unreachable entities in the order of their indices.
  std::sort(unreachable_indices.begin(), unreachable_indices.end());
  for (int i = 0; i < unreachable_indices.size(); i++) {
    unreachable_entities.push_back(entities[unreachable_indices[i]]);
  }
  return unreachable_entities;
}

}  // namespace pdpi
