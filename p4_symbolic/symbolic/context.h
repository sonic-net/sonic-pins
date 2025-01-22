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

#ifndef PINS_P4_SYMBOLIC_SYMBOLIC_CONTEXT_H_
#define PINS_P4_SYMBOLIC_SYMBOLIC_CONTEXT_H_

#include <memory>
#include <string>

#include "absl/container/btree_map.h"
#include "p4_symbolic/symbolic/guarded_map.h"
#include "p4_symbolic/symbolic/table_entry.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {

// Maps the name of a header field in the p4 program to its concrete value.
using ConcretePerPacketState = absl::btree_map<std::string, std::string>;

// The symbolic counterpart of ConcretePerPacketState.
// Maps the name of a header field in the p4 program to its symbolic value.
// This can be used to constrain p4 program fields inside assertions.
// This is automatically constructed from the header type definitions
// the p4 program has.
// Assume the p4 program has a header instance named "standard_metadata" of type
// "standard_metadata_t", which has field "ingress_port" of type "bit<9>" in it.
// Then, we will have:
//     SymbolicMetadata["standard_metadata.ingress_port"] =
//         <symbolic bit vector of size 9>
// An instance of this type is passed around and mutated by the functions
// responsible for symbolically evaluating the program.
using SymbolicPerPacketState = SymbolicGuardedMap;

// Expresses a concrete match for a corresponding concrete packet with a
// table in the program.
struct ConcreteTableMatch {
  bool matched;  // false if no entry in this table was matched, true otherwise.
  // If matched is false, this is set to -1.
  // If matched is true, this is the index of the matched table entry, or -1 if
  // the default entry was matched.
  int entry_index;
  std::string to_string() const;
};

// Exposes a symbolic handle for a match between the symbolic packet and
// a symbolic table.
// This allows encoding of constraints on which (if any) entries are matched,
// and the value of the match.
// e.g. for some table "<table_name>":
// (<symbolic_table_match>.entry_index == i) iff
//  <entries>[<table_name>][i] was matched/hit.
struct SymbolicTableMatch {
  z3::expr matched;
  z3::expr entry_index;
};

// `SymbolicTableMatch`es by table name.
using SymbolicTableMatches = absl::btree_map<std::string, SymbolicTableMatch>;

// Specifies the expected trace in the program that the corresponding
// concrete packet is expected to take.
struct ConcreteTrace {
  absl::btree_map<std::string, ConcreteTableMatch> matched_entries;
  // Can be extended more in the future to include useful
  // flags about dropping the packet, taking specific code (e.g. if)
  // branches, vrf, other interesting events, etc.
  bool dropped;     // true if the packet was dropped.
  bool got_cloned;  // true if the packet got cloned.
  std::string to_string() const;
};

// Provides symbolic handles for the trace the symbolic packet is constrained
// to take in the program.
struct SymbolicTrace {
  SymbolicTrace(z3::context &z3_context)
      : dropped(z3_context), got_cloned(z3_context) {}

  // Full table name to its symbolic match.
  // TODO: Rename to matches_by_table_name.
  SymbolicTableMatches matched_entries;
  z3::expr dropped;
  z3::expr got_cloned;
};

// The result of solving with some assertion.
// This contains an input test packet with its predicted flow in the program,
// and the predicted output.
struct ConcreteContext {
  std::string ingress_port;
  std::string egress_port;
  ConcretePerPacketState ingress_headers;
  ConcretePerPacketState parsed_headers;
  ConcretePerPacketState egress_headers;
  ConcreteTrace trace;  // Expected trace in the program.

  std::string to_string() const;
  std::string to_string(bool verbose) const;
};

// The symbolic context within our analysis.
// Exposes symbolic handles for the fields of the input packet,
// and its trace in the program.
// Assertions are defined on a symbolic context.
class SymbolicContext {
 public:
  SymbolicContext()
      : z3_context(std::make_unique<z3::context>()),
        ingress_port(*z3_context),
        egress_port(*z3_context),
        trace(*z3_context) {}

  // The Z3 context for the symbolic evaluation.
  // Note that this has to precede other z3 objects so that they will be
  // destroyed before z3_context during destruction. The `unique_ptr` wrapper is
  // required because `z3::context` has an implicitly-deleted move constructor.
  std::unique_ptr<z3::context> z3_context;
  z3::expr ingress_port;
  z3::expr egress_port;
  SymbolicPerPacketState ingress_headers;
  SymbolicPerPacketState parsed_headers;
  SymbolicPerPacketState egress_headers;
  TableEntries table_entries;
  SymbolicTrace trace;
};

}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // PINS_P4_SYMBOLIC_SYMBOLIC_CONTEXT_H_
