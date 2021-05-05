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

// Contains the entry point to our symbolic interpretation code, as well
// as helpers for debugging and finding concrete packets and their context.

#ifndef P4_SYMBOLIC_SYMBOLIC_SYMBOLIC_H_
#define P4_SYMBOLIC_SYMBOLIC_SYMBOLIC_H_

#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/btree_map.h"
#include "absl/strings/str_cat.h"
#include "gutil/status.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/ir/table_entries.h"
#include "p4_symbolic/symbolic/guarded_map.h"
#include "p4_symbolic/symbolic/values.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {

// Maps the name of a header field in the p4 program to its concrete value.
using ConcretePerPacketState = absl::btree_map<std::string, std::string>;

// The symbolic counterpart of ConcretePerPacketState.
// Maps the name of a header field in the p4 program to its symbolic value.
// This can be used to constrain p4 program fields inside assertions.
// This is automatically constructred from the header type definitions
// the p4 program has.
// Assume the p4 program has a header instance named "standard_metadata" of type
// "standard_metadata_t", which has field "ingress_port" of type "bit<9>" in it.
// Then, we will have:
//    SymbolicMetadata["standard_metadata.ingress_port"] =
//         <symbolic bit vector of size 9>
// An instace of this type is passed around and mutated by the functions
// responsible for symbolically evaluating the program.
using SymbolicPerPacketState = SymbolicGuardedMap;

// V1model's `mark_to_drop` primitive sets the `egress_spec` field to this
// value to indicate the packet should be dropped at the end of ingress/egress
// processing. See v1model.p4 for details.
z3::expr EgressSpecDroppedValue();
absl::StatusOr<z3::expr> IsDropped(const SymbolicPerPacketState &state);

// Expresses a concrete match for a corresponding concrete packet with a
// table in the program.
struct ConcreteTableMatch {
  bool matched;  // false if no entry in this table was matched, true otherwise.
  // If matched is false, this is set to -1.
  // If matched is true, this is the index of the matched table entry, or -1 if
  // the default entry was matched.
  int entry_index;
  std::string to_string() const {
    if (!matched) {
      return "was not matched!";
    }
    return absl::StrCat("was matched on entry ", entry_index);
  }
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
  bool dropped;  // true if the packet was dropped.
  std::string to_string() const {
    auto result = absl::StrCat("dropped = ", dropped);
    for (const auto &[table, match] : matched_entries) {
      result = absl::StrCat(result, "\n", table, " => ", match.to_string());
    }
    return result;
  }
};

// Provides symbolic handles for the trace the symbolic packet is constrained
// to take in the program.
struct SymbolicTrace {
  // Full table name to its symbolic match.
  // TODO: Rename to matches_by_table_name.
  SymbolicTableMatches matched_entries;
  z3::expr dropped;
};

// Specifies the concrete data inside a packet.
// This is a friendly helper struct, all information in this struct
// is extracted from ConcretePerPacketState.
struct ConcretePacket {
  std::string eth_src;
  std::string eth_dst;
  std::string eth_type;

  std::string ipv4_src;
  std::string ipv4_dst;
  std::string ipv6_dst_upper;
  std::string ipv6_dst_lower;
  std::string protocol;
  std::string dscp;
  std::string ttl;

  std::string icmp_type;

  std::string to_string() const {
    return absl::StrCat("eth_src = ", eth_src, "\n", "eth_dst = ", eth_dst,
                        "\n", "eth_type = ", eth_type, "\n",
                        "ipv4_src = ", ipv4_src, "\n", "ipv4_dst = ", ipv4_dst,
                        "\n", "ipv6_dst_upper = ", ipv6_dst_upper, "\n",
                        "ipv6_dst_lower = ", ipv6_dst_lower, "\n",
                        "protocol = ", protocol, "\n", "dscp = ", dscp, "\n",
                        "ttl = ", ttl, "\n", "icmp_type = ", icmp_type);
  }
};

// A helper struct containing symbolic expressions for every field in a packet.
// All expressions in this struct are extracted from SymbolicPerPacketState.
// We explicitly give these fields name in this struct to simplify how the
// client code can impose constraints on them in assertions.
struct SymbolicPacket {
  z3::expr eth_src;   // 48 bit.
  z3::expr eth_dst;   // 48 bit.
  z3::expr eth_type;  // 16 bit.

  z3::expr ipv4_src;        // 32 bit, valid if eth_type = 0x0800
  z3::expr ipv4_dst;        // 32 bit, valid if eth_type = 0x0800
  z3::expr ipv6_dst_upper;  // 64 bit, valid if eth_type = 0x86dd
  z3::expr ipv6_dst_lower;  // 64 bit, valid if eth_type = 0x86dd
  z3::expr protocol;        // 8 bit, valid if eth_type is ip
  z3::expr dscp;            // 6 bit, valid if eth_type is ip
  z3::expr ttl;             // 8 bit, valid if eth_type is ip

  z3::expr icmp_type;  // 8 bit, valid if eth_type is ip
};

// The result of solving with some assertion.
// This contains an input test packet with its predicted flow in the program,
// and the predicted output.
struct ConcreteContext {
  std::string ingress_port;
  std::string egress_port;
  ConcretePacket ingress_packet;  // Input packet into the program/switch.
  ConcretePacket egress_packet;   // Expected output packet.
  ConcretePerPacketState ingress_headers;
  ConcretePerPacketState egress_headers;
  ConcreteTrace trace;  // Expected trace in the program.

  std::string to_string() const { return to_string(false); }
  std::string to_string(bool verbose) const {
    auto result = absl::StrCat(
        "ingress_port = ", ingress_port, "\n", "egress_port = ", egress_port,
        "\n\n", "ingress_packet:\n", ingress_packet.to_string(), "\n\n",
        "egress_packet:\n", egress_packet.to_string(), "\n\n", "trace:\n",
        trace.to_string());
    if (verbose) {
      auto ingress_string = absl::StrCat("ingress_headers", ":");
      auto egress_string = absl::StrCat("egress_headers", ":");
      for (const auto &[name, ingress_value] : ingress_headers) {
        ingress_string =
            absl::StrCat(ingress_string, "\n", name, " = ", ingress_value);
      }
      for (const auto &[name, egress_value] : egress_headers) {
        egress_string =
            absl::StrCat(egress_string, "\n", name, " = ", egress_value);
      }
      result =
          absl::StrCat(result, "\n\n", ingress_string, "\n\n", egress_string);
    }
    return result;
  }
};

// The symbolic context within our analysis.
// Exposes symbolic handles for the fields of the input packet,
// and its trace in the program.
// Assertions are defined on a symbolic context.
struct SymbolicContext {
  z3::expr ingress_port;
  z3::expr egress_port;
  SymbolicPerPacketState ingress_headers;
  SymbolicPerPacketState egress_headers;
  SymbolicTrace trace;
};

// The dataplane configuration of the switch.
// Used as input to our symbolic pipeline.
struct Dataplane {
  ir::P4Program program;
  // Maps the full name of a table to a list of its entries.
  ir::TableEntries entries;
};

// The overall state of our symbolic solver/interpreter.
// This is returned by our main analysis/interpration function, and is used
// to find concrete test packets and for debugging.
// This is internal to our solver code. External code that uses our solver
// is not expected to access any of these fields or modify them.
// Only one instance of this struct will be constructed per P4 program
// evaluation, which can be then used to solve for particular assertions
// many times.
struct SolverState {
  // The IR represnetation of the p4 program being analyzed.
  ir::P4Program program;
  // Maps the name of a table to a list of its entries.
  ir::TableEntries entries;
  // The symbolic context of our interpretation/analysis of the program,
  // including symbolic handles on packet headers and its trace.
  SymbolicContext context;
  // Having the z3 solver defined here allows Z3 to remember interesting
  // deductions it made while solving for one particular assertion, and re-use
  // them during solving with future assertions.
  std::unique_ptr<z3::solver> solver;
  // Store the p4 runtime translator state for use by .Solve(...).
  values::P4RuntimeTranslator translator;
};

// An assertion is a user defined function that takes a symbolic context
// as input, and returns constraints on symbolic handles exposed by that
// context. For example:
// z3::expr portIsOne(const SymbolicContext &ctx) {
//   return ctx.ingress_port == 1;
// }
using Assertion = std::function<z3::expr(const SymbolicContext &)>;

// Symbolically evaluates/interprets the given program against the given
// entries for every table in that program, and the available physical ports
// on the switch.
absl::StatusOr<std::unique_ptr<SolverState>> EvaluateP4Pipeline(
    const Dataplane &data_plane, const std::vector<int> &physical_ports);

// Finds a concrete packet and flow in the program that satisfies the given
// assertion and meets the structure constrained by solver_state.
absl::StatusOr<std::optional<ConcreteContext>> Solve(
    const std::unique_ptr<SolverState> &solver_state,
    const Assertion &assertion);

// Dumps the underlying SMT program for debugging.
std::string DebugSMT(const std::unique_ptr<SolverState> &solver_state,
                     const Assertion &assertion);

}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_SYMBOLIC_H_
