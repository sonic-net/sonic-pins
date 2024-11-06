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

// Defines APIs for constructing control flow graph of a P4 program and
// performing analysis useful for optimized symbolic execution.
// See go/optimized-symbolic-execution.

#ifndef PINS_P4_SYMBOLIC_IR_CFG_H_
#define PINS_P4_SYMBOLIC_IR_CFG_H_

#include <optional>
#include <string>
#include <vector>

#include "absl/container/btree_set.h"
#include "absl/container/flat_hash_set.h"
#include "absl/container/node_hash_map.h"
#include "absl/status/statusor.h"
#include "p4_symbolic/ir/ir.pb.h"

namespace p4_symbolic::ir {

// A subsequence of an execution path in a P4 program. Each element is a control
// name along the path.
using ControlPath = std::vector<std::string>;

// A single node in the control flow graph along with various computed metadata.
// We make the following assuptions in the descriptions and definitions below.
// 1. The collection of CfgNodes form a non-empty DAG.
// 2. The DAG has an implicit and unique root/source node implicitly connected
// to all nodes with (explicit) in-degree 0.
// 3. The DAG has an implicit and unique leaf/sink node that all nodes with
// (explicit) out-degree 0 are implicitly connected to.
// 4. We do not explicitly refer to these two implicit nodes in the code. E.g.
// do not include them in paths that start from or end in them.
struct CfgNode {
  // Same as a the name of the control node in the IR.
  std::string control_name;

  // The children of the current node.
  // Using btree_set (here and below) for deterministic order, though not a
  // necessary condition (e.g. a flat_hash_set would work too).
  absl::btree_set<std::string> children;

  // The parents of the current node.
  absl::btree_set<std::string> parents;

  // A path from the beginning of the execution (root) to the current node in
  // which only nodes common to *all* possible execution paths between the two
  // points are included. In other words, for any branching along the path, only
  // its "merge point" (see the precise definition below) is included.
  // For example, in the following graph
  //               -> n3 -> n4
  //             /             \
  //    n1 -> n2                -> n6 -> n7
  //             \             /
  //               ---> n5 ---
  // The contracted path from root for n4 is n1->n2->n3->n4 and for n7 is
  // n1->n2->n6->n7.
  // We call such paths "contrated" because intuitively branches along the path
  // are contracted. This is related to the notion of "edge contraction" from
  // graph theory: given any path from ni to nj, the contracted path is obtained
  // by contracting all edges along the path that are not shared among all ni ->
  // nj paths. All pairs of nodes in any DAG are guaranteed to have a unique
  // contracted path.
  ControlPath contracted_path_from_root;

  // Same as `contracted_path_from_root` but the path is from the end of
  // execution to the current node (in the reverse direction).
  // In the example above, the contracted reverse path from leaf for n5 is
  // n7<-n6<-n5 and for n1 is n7<-n6<-n2<-n1.
  ControlPath contracted_reverse_path_from_leaf;

  // The name of the first (i.e. closest in topological order) control point
  // where all paths starting from the children ("branches") of the
  // current node to the sink meet. In the example above, the merge point of n1
  // is n2, for n2 it is n6, and for n3 it is n4. In any DAG with a sink node,
  // any node except the sink node is guaranteed to have exactly one merge
  // point.
  // Note: The merge point of nodes with explicit out-degree 0 is the
  // implicit sink node which is not displayed (assumptions 3 and 4 above),
  // hence we use nullopt in that case.
  // Concept of merge point defined here is equivalent to the concept of
  // "immediate post-dominator" in graph theory literature
  // (https://en.wikipedia.org/wiki/Dominator_(graph_theory)).
  // TODO: Rename everything with familiar graph theory concepts.
  std::optional<std::string> merge_point;

  // Whether or not (optimized) symbolic execution should continue to the merge
  // point after executing the subgraph of the current node (up to the merge
  // point). This must be set in a way that each node in the graph is guaranteed
  // to be executed exactly once: true iff the reverse merge point (i.e. merge
  // point in reverse direction) of the merge point (if any) of the node is the
  // node itself (see go/optimized-symbolic-execution for details).
  bool continue_to_merge_point;
};

// Returns a string represting the information stored in the given `cfg_node`.
// Useful for debugging purposes.
std::string ToString(const CfgNode &cfg_node);

// Control Flow Graph (CFG) of a P4 program created from its P4-Symbolic's IR
// representation along with various CFG analyses useful for optimized
// symbolic execution (go/optimized-symbolic-execution).
// Assumption: The CFG of the input P4 program forms a DAG (this is guaranteed
// in BMv2). Also there is at least one node in the DAG (this is guaranteed by
// `EndOfPipeline` node in IR).
class ControlFlowGraph {
 public:
  // Creates a ControlFlowGraph from an input P4 program and perform analysis
  // for optimized symbolic execution.
  // Runtime complexity: O(N*E) where N is the number of CFG
  // nodes and E is the number of edges between the nodes.
  // Note: Our most complex program at the moment has only 44 nodes, so the
  // current complexity is good enough for our purposes (i.e. CFG
  // analysis is not a bottleneck). We can revisit the algorithm if this becomes
  // a bottleneck.
  static absl::StatusOr<std::unique_ptr<ControlFlowGraph>> Create(
      const P4Program &program);

  // Returns information used in optimized symbolic execution for the node
  // correspnding to the given `control_name` in the graph, or error if no such
  // node exists. Expects input to correspond to a node with an (explicit)
  // merge point (i.e. a node with non-zero out-degree), otherwise returns
  // error.
  absl::StatusOr<OptimizedSymbolicExecutionInfo>
  GetOptimizedSymbolicExecutionInfo(absl::string_view control_name);

  // Returns a string represting the constructred CFG. Useful for debugging
  // purposes.
  std::string ToString();

  // Disallow copy and move (for pointer stability during and after Create.
  // Useful for debugging but not a necessary condition).
  ControlFlowGraph(const ControlFlowGraph &) = delete;
  ControlFlowGraph(ControlFlowGraph &&) = delete;
  ControlFlowGraph &operator=(const ControlFlowGraph &) = delete;
  ControlFlowGraph &operator=(ControlFlowGraph &&) = delete;

 private:
  // Map of each control name to its correspodning CfgNode.
  // Must use node_hash_map for pointer stability.
  // Note: Pointer stability is a necessariy condition in this case, otherwise
  // ConstructSubgraph as well as any code depending on pointers/references to
  // CfgNodes in node_by_name_ would break.
  absl::node_hash_map<std::string, CfgNode> node_by_name_;

  // Can only be constructed through a call to Create.
  ControlFlowGraph() = default;

  // Returns a non-null immutable pointer to the node correspnding to the given
  // `control_name` in the graph, or error if no such node exists.
  absl::StatusOr<const CfgNode *> GetNode(absl::string_view control_name);

  // Returns a reference to the node correspnding to the given `control_name` in
  // the graph. If such a node does not exist, creates and returns a new node
  // with the given name.
  CfgNode &GetOrAddNode(absl::string_view control_name);

  // Returns a non-null mutable pointer to the node correspnding to the given
  // `control_name` in the graph, or error if no such node exists.
  absl::StatusOr<CfgNode *> GetMutableNode(absl::string_view control_name);

  // Recursively constructs the subgraph corresponding to the given
  // `control_name`. Updates the children and parents of the involved
  // nodes.
  absl::Status ConstructSubgraph(const P4Program &program,
                                 const std::string &control_name);

  // Recursively computes the contracted reverse path from the (implicit) leaf
  // to the given `cfg_node`. Sets the `contracted_reverse_path_from_leaf` field
  // in the involved nodes (if not already set).
  absl::Status SetContractedReversePathFromLeaf(CfgNode &cfg_node);

  // Recursively computes the contracted path from the (implicit) root to the
  // given `cfg_node`. Sets the `contracted_path_from_root` field in the
  // involved nodes (if not already set).
  absl::Status SetContractedPathFromRoot(CfgNode &cfg_node);
};

}  // namespace p4_symbolic::ir

#endif  // PINS_P4_SYMBOLIC_IR_CFG_H_
