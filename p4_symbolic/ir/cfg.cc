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

#include "p4_symbolic/ir/cfg.h"

#include <memory>
#include <optional>
#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_join.h"
#include "absl/strings/substitute.h"
#include "gutil/status.h"
#include "p4_symbolic/ir/ir.h"

namespace p4_symbolic::ir {

namespace {

// Returns the set of the children of the given `control_name` in the given
// `program`.
absl::StatusOr<absl::btree_set<std::string>> GetChildren(
    const P4Program &program, const std::string &control_name) {
  absl::btree_set<std::string> children;

  if (control_name == EndOfPipeline()) return children;

  if (auto it = program.conditionals().find(control_name);
      it != program.conditionals().end()) {
    for (const auto &branch :
         {it->second.if_branch(), it->second.else_branch()}) {
      children.insert(branch);
    }

  } else if (auto it = program.tables().find(control_name);
             it != program.tables().end()) {
    for (const auto &[_, next_control] :
         it->second.table_implementation().action_to_next_control()) {
      children.insert(next_control);
    }
  } else {
    return absl::InvalidArgumentError(
        absl::Substitute("Unknown control '$0'", control_name));
  }

  return children;
}

// Returns the set of the children state names of the given `state_name` in the
// given parser.
absl::StatusOr<absl::btree_set<std::string>> GetChildren(
    const Parser &parser, const std::string &state_name) {
  absl::btree_set<std::string> children;

  if (state_name == EndOfParser()) return children;

  auto it = parser.parse_states().find(state_name);
  if (it == parser.parse_states().end()) {
    return gutil::InvalidArgumentErrorBuilder()
           << "Unknown parse state: '" << state_name << "'";
  }

  const ParseState &state = it->second;

  for (const auto &transition : state.transitions()) {
    switch (transition.transition_case()) {
      case ParserTransition::kDefaultTransition: {
        children.insert(transition.default_transition().next_state());
        break;
      }
      case ParserTransition::kHexStringTransition: {
        children.insert(transition.hex_string_transition().next_state());
        break;
      }
      default: {
        return gutil::InvalidArgumentErrorBuilder()
               << "Unknown transition: " << transition.ShortDebugString();
      }
    }
  }

  return children;
}

// Returns the LCP of two control paths.
ControlPath LongestCommonPrefix(const ControlPath &l, const ControlPath &r) {
  ControlPath result;
  int index = 0;
  while (index < l.size() && index < r.size() && l[index] == r[index]) {
    result.push_back(l[index]);
    index++;
  }
  return result;
}

}  // namespace

std::string ToString(const CfgNode &node) {
  return absl::Substitute(
      "node: $0\n\tchildren: [$1]\n\tparents: [$2]\n\tpath_from_root: "
      "$3\n\trev_path_from_leaf: $4\n\tmerge_point: $5\n\tcontinue: $6\n",
      node.node_name, absl::StrJoin(node.children, ","),
      absl::StrJoin(node.parents, ","),
      absl::StrJoin(node.contracted_path_from_root, "->"),
      absl::StrJoin(node.contracted_reverse_path_from_leaf, "<-"),
      node.merge_point.has_value() ? node.merge_point.value() : "nullopt",
      node.continue_to_merge_point ? "true" : "false");
}

std::string ControlFlowGraph::ToString() {
  std::string out;
  absl::StrAppend(&out, node_by_name_.size(), " nodes\n");
  for (const auto &[name, cfg_node] : node_by_name_) {
    absl::StrAppend(&out, "[", name, "] ",
                    ::p4_symbolic::ir::ToString(cfg_node));
  }
  return out;
}

absl::StatusOr<OptimizedSymbolicExecutionInfo>
ControlFlowGraph::GetOptimizedSymbolicExecutionInfo(
    absl::string_view node_name) {
  ASSIGN_OR_RETURN(const CfgNode *cfg_node, GetNode(node_name));

  if (!cfg_node->merge_point.has_value()) {
    return absl::InvalidArgumentError(absl::Substitute(
        "Control node '$0' does not have a merge point", cfg_node->node_name));
  }

  OptimizedSymbolicExecutionInfo info;
  info.set_merge_point(*cfg_node->merge_point);
  info.set_continue_to_merge_point(cfg_node->continue_to_merge_point);
  return info;
}

absl::StatusOr<const CfgNode *> ControlFlowGraph::GetNode(
    absl::string_view node_name) {
  return GetMutableNode(node_name);
}

absl::StatusOr<CfgNode *> ControlFlowGraph::GetMutableNode(
    absl::string_view node_name) {
  auto it = node_by_name_.find(node_name);
  if (it == node_by_name_.end()) {
    return absl::NotFoundError(absl::Substitute(
        "Node name '$0' does not correspond to any node in the CFG",
        node_name));
  }

  return &(it->second);
}

absl::StatusOr<CfgNode *> ControlFlowGraph::GetOrAddNode(
    absl::string_view node_name, CfgNodeType node_type) {
  auto it = node_by_name_.find(node_name);

  if (it == node_by_name_.end()) {
    // Create a new node.
    CfgNode cfg_node = {
        .node_name = std::string(node_name),
        .node_type = node_type,
    };
    it =
        node_by_name_.insert(it, {std::string(node_name), std::move(cfg_node)});
  } else if (it->second.node_type != node_type) {
    // Existing node. Returns an error if the node has the same type.
    return gutil::InvalidArgumentErrorBuilder()
           << "Nodes of different types have the same name: " << node_name;
  }

  return &(it->second);
}

absl::Status ControlFlowGraph::ConstructSubgraph(
    const P4Program &program, const std::string &control_name) {
  // Obtain the CFG node of the control and the names of its next states.
  ASSIGN_OR_RETURN(CfgNode * cfg_node,
                   GetOrAddNode(control_name, CfgNodeType::kPipelineControl));
  ASSIGN_OR_RETURN(absl::btree_set<std::string> children,
                   GetChildren(program, control_name));

  // Add edges between the parent and child nodes.
  for (const std::string &child_control_name : children) {
    ASSIGN_OR_RETURN(
        CfgNode * child_cfg_node,
        GetOrAddNode(child_control_name, CfgNodeType::kPipelineControl));
    bool is_new_node = child_cfg_node->parents.empty();
    cfg_node->children.insert(child_control_name);
    child_cfg_node->parents.insert(control_name);

    // If the child is a new node, recursively construct the subgraph.
    if (is_new_node) {
      RETURN_IF_ERROR(ConstructSubgraph(program, child_control_name));
    }
  }

  return absl::OkStatus();
}

absl::Status ControlFlowGraph::ConstructSubgraph(
    const Parser &parser, const std::string &state_name) {
  // Obtain the CFG node of the parse state and the names of its next states.
  ASSIGN_OR_RETURN(CfgNode * cfg_node,
                   GetOrAddNode(state_name, CfgNodeType::kParseState));
  ASSIGN_OR_RETURN(absl::btree_set<std::string> children,
                   GetChildren(parser, state_name));

  // Add edges between the parent and child nodes.
  for (const std::string &child_state_name : children) {
    ASSIGN_OR_RETURN(CfgNode * child_cfg_node,
                     GetOrAddNode(child_state_name, CfgNodeType::kParseState));
    bool is_new_node = child_cfg_node->parents.empty();
    cfg_node->children.insert(child_state_name);
    child_cfg_node->parents.insert(state_name);

    // If the child is a new node, recursively construct the subgraph.
    if (is_new_node) {
      RETURN_IF_ERROR(ConstructSubgraph(parser, child_state_name));
    }
  }

  return absl::OkStatus();
}

absl::Status ControlFlowGraph::SetContractedReversePathFromLeaf(
    CfgNode &cfg_node) {
  ControlPath &reverse_path_from_leaf =
      cfg_node.contracted_reverse_path_from_leaf;

  for (const auto &child : cfg_node.children) {
    // Compute or get child's contracted reverse path from leaf.
    ASSIGN_OR_RETURN(CfgNode * child_cfg_node, GetMutableNode(child));
    const ControlPath &child_reverse_path_from_leaf =
        child_cfg_node->contracted_reverse_path_from_leaf;
    if (child_reverse_path_from_leaf.empty()) {
      RETURN_IF_ERROR(SetContractedReversePathFromLeaf(*child_cfg_node));
      RET_CHECK(!child_reverse_path_from_leaf.empty()) << absl::Substitute(
          "Contracted reverse path from leaf of '$0' is empty",
          child_cfg_node->node_name);
    }

    // Set current node's reverse path from leaf to the longest common
    // prefix of childrens'.
    if (reverse_path_from_leaf.empty()) {
      reverse_path_from_leaf = child_reverse_path_from_leaf;
    } else {
      // This could lead to O(n^3) complexity across graphs with O(n) branching
      // factor. In practice we expect only constant branching, and thus O(n^2)
      // complexity.
      reverse_path_from_leaf = LongestCommonPrefix(
          reverse_path_from_leaf, child_reverse_path_from_leaf);
    }
  }

  // Add self to the end of the reverse path from leaf.
  reverse_path_from_leaf.push_back(cfg_node.node_name);

  return absl::OkStatus();
}

absl::Status ControlFlowGraph::SetContractedPathFromRoot(CfgNode &cfg_node) {
  ControlPath &path_from_root = cfg_node.contracted_path_from_root;

  for (const auto &parent : cfg_node.parents) {
    // Compute or get parent's contracted path from root.
    ASSIGN_OR_RETURN(CfgNode * parent_cfg_node, GetMutableNode(parent));
    const ControlPath &parent_path_from_root =
        parent_cfg_node->contracted_path_from_root;
    if (parent_path_from_root.empty()) {
      RETURN_IF_ERROR(SetContractedPathFromRoot(*parent_cfg_node));
      RET_CHECK(!parent_path_from_root.empty())
          << absl::Substitute("Contracted path from root of '$0' is empty",
                              parent_cfg_node->node_name);
    }

    // Set current node's path from root to the longest common
    // prefix of parents'.
    if (path_from_root.empty()) {
      path_from_root = parent_path_from_root;
    } else {
      path_from_root =
          LongestCommonPrefix(path_from_root, parent_path_from_root);
    }
  }

  // Add self to the end of the path from root.
  path_from_root.push_back(cfg_node.node_name);

  return absl::OkStatus();
}

absl::StatusOr<std::unique_ptr<ControlFlowGraph>> ControlFlowGraph::Create(
    const P4Program &program) {
  // Using `new` to access a non-public constructor.
  auto cfg = absl::WrapUnique(new ControlFlowGraph());

  // Make sure there is exactly one parser.
  if (program.parsers_size() != 1) {
    return absl::InvalidArgumentError(
        absl::StrCat("Invalid number of parsers: ", program.parsers_size()));
  }

  // Build the basic CFG for parsers.
  for (const auto &[_, parser] : program.parsers()) {
    RETURN_IF_ERROR(cfg->ConstructSubgraph(parser, parser.initial_state()));
  }

  // Build the basic CFG.
  for (const auto &[name, pipeline] : program.pipeline()) {
    RETURN_IF_ERROR(
        cfg->ConstructSubgraph(program, pipeline.initial_control()));
  }

  // Compute contracted paths from root and leaf for each node.
  for (auto &[_, cfg_node] : cfg->node_by_name_) {
    if (cfg_node.contracted_reverse_path_from_leaf.empty()) {
      RETURN_IF_ERROR(cfg->SetContractedReversePathFromLeaf(cfg_node));
      RET_CHECK(!cfg_node.contracted_reverse_path_from_leaf.empty())
          << absl::Substitute(
                 "contracted_reverse_path_from_leaf of '$0' is empty",
                 cfg_node.node_name);
    }
    if (cfg_node.contracted_path_from_root.empty()) {
      RETURN_IF_ERROR(cfg->SetContractedPathFromRoot(cfg_node));
      RET_CHECK(!cfg_node.contracted_path_from_root.empty())
          << absl::Substitute("contracted_path_from_root of '$0' is empty",
                              cfg_node.node_name);
    }
  }

  auto get_merge_point =
      [](const ControlPath &contracted_path) -> std::optional<std::string> {
    // For any contracted path (or reverse path) [root/leaf, ..., n_{k-1},
    // n_k] ending in n_{k}, n_{k-1} is the merge point (or reverse merge
    // point) of n_{k} since n_{k-1}. For example, in
    //       c1 - implicit source
    //      /  \
    //    c2    t3
    //    / \   /
    //   t1 t2 /
    //    \ / /
    //     t4 - implicit sink
    // Contracted reverse path from leaf of c2 is [t4, c2] and the merge point
    // of c2 is t4. Also contracted path from root of t2 is [c1, c2, t2] and the
    // reverse merge point of t2 c2.
    // The merge point / rever merge point of nodes with out-degree / in-degree
    // 0 is the implicit sink / source node. We denote that with nullopt (see
    // the assumptions in cfg.h). E.g. the merge point of t4 above is nullopt.
    return contracted_path.size() > 1
               ? std::optional<std::string>(contracted_path.rbegin()[1])
               : std::nullopt;
  };

  // Compute continuation (for optimized symbolic execution) for each node.
  for (auto &[_, cfg_node] : cfg->node_by_name_) {
    // Compute the merge point.
    cfg_node.merge_point =
        get_merge_point(cfg_node.contracted_reverse_path_from_leaf);

    // Determine continue_to_merge_point.
    cfg_node.continue_to_merge_point = false;
    if (cfg_node.merge_point.has_value()) {
      ASSIGN_OR_RETURN(const CfgNode *merge_point_cfg_node,
                       cfg->GetNode(*cfg_node.merge_point));
      std::optional<std::string> merge_point_reverse_merge_point =
          get_merge_point(merge_point_cfg_node->contracted_path_from_root);

      // May continue to the merge point if and only if the reverse merge point
      // (i.e. merge point in reverse direction) of the merge point (if any) of
      // the node is the node itself (i.e. the given node is the latest node
      // prior to the merge point such that all execution paths going through
      // the merge point also go through the current node). This is to prevent
      // executing shared merge points more than once. For example, in the
      // following graph
      //       c1 - implicit source
      //      /  \
      //    c2    t3
      //    / \   /
      //   t1 t2 /
      //    \ / /
      //     t4 - implicit sink
      // The merge points of c1, c2, t1, t2, t3 are t4. We must only continue to
      // t4 from c1 because the reverse merge point of t4 is c1.
      if (merge_point_reverse_merge_point.has_value() &&
          *merge_point_reverse_merge_point == cfg_node.node_name) {
        cfg_node.continue_to_merge_point = true;
      }
    }
  }

  return std::move(cfg);
}

}  // namespace p4_symbolic::ir
