// Copyright 2021 Google LLC
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
#ifndef P4_FUZZER_CONSTRAINTS_UTIL_H_
#define P4_FUZZER_CONSTRAINTS_UTIL_H_

#include <cstdio>
#include <utility>

#include "absl/container/flat_hash_map.h"
#include "absl/hash/hash.h"
#include "absl/types/variant.h"
#include "cudd.h"
#include "cuddObj.hh"
#include "gutil/status.h"
#include "p4_constraints/ast.pb.h"
#include "p4_constraints/backend/constraint_info.h"

namespace p4_fuzzer {

// Used internally by MatchKeyToBddVariableMapping for custom hashing. Should
// not be used outside of MatchKeyToBddVariableMapping member functions.
// MatchFieldBit {.name = foo, .bit = k} represents the kth least significant
// bit of match field `foo`.
struct MatchFieldBit {
  std::string name;
  int bit;

  inline bool operator==(const MatchFieldBit& other) const {
    return (other.name == name) && (other.bit == bit);
  }

  template <typename H>
  friend H AbslHashValue(H h, const MatchFieldBit& key) {
    return H::combine(std::move(h), key.name, key.bit);
  }
};

using BddVariable = int;

// A symbolic bit is either a concrete bit (bool) or a boolean variable
// (BddVariable).
using SymbolicBit = absl::variant<bool, BddVariable>;

// We use SymbolicBitVectors to encode P4 constants (int, bit<W>) as well as
// table keys. Bits are ordered from least significant to most significant.
using SymbolicBitVector = std::vector<SymbolicBit>;

// Stores a bijection  between BDD variables and the match field bits they
// represent.
class MatchKeyToBddVariableMapping {
 public:
  // Returns BDD variables equal to the number of bits used by the key. The BDD
  // variables are ordered from the least significant bit to the most
  // significant bit.
  absl::StatusOr<std::vector<BddVariable>> GetOrAllocateBddVariablesForKey(
      const p4_constraints::ast::Expression& expr);

 private:
  absl::StatusOr<BddVariable> GetOrAllocateBddVariable(
      const MatchFieldBit& field_bit);

  // Inserts a new entry that maps a MatchFieldBit to a BddVariable and vice
  // versa.
  absl::Status AddEntry(const MatchFieldBit& field_bit, BddVariable bdd_var);

  absl::flat_hash_map<MatchFieldBit, BddVariable> key_to_bdd_;
  absl::flat_hash_map<BddVariable, MatchFieldBit> bdd_to_key_;

  BddVariable bdd_var_latest_ = 0;
};

// Takes a well-typed, boolean p4_constraints::ast::Expression
// (https://github.com/p4lang/p4-constraints), and converts it to a binary
// decision diagram (BDD). Returns the BDD, or an error in case the expression
// is either invalid or not supported. The mapping specifies which BDD variable
// corresponds to which match field (and bit inside the match field). This can
// be used to construct a table entry using solutions to BDD expressions.
absl::StatusOr<BDD> ExpressionToBDD(const p4_constraints::ast::Expression& expr,
                                    Cudd* mgr,
                                    MatchKeyToBddVariableMapping* mapping);

// Prints a BDD to stdout as a graph in dot file format.
void PrintBDDAsDotFile(const BDD& bdd, Cudd* mgr);

// Symbolic representation of a p4-constraint as a BDD, together with a map from
// BDD variables to the table key bits they represent.
struct SymbolicConstraint {
  BDD bdd;

  // Maps each Bdd variable to the match field bit it represents.
  const MatchKeyToBddVariableMapping mapping;
};

// Maps table ids to SymbolicConstraints. Does not contain entries for tables
// that have no constraints.
using BDDInfo = absl::flat_hash_map<uint32_t, SymbolicConstraint>;

// Takes a p4_constraints::ConstraintInfo instance parsed from a P4Info file and
// returns a map from table ids to BDDs representing their constraints. Tables
// with no constraints are not included.
absl::StatusOr<BDDInfo> ConstraintToBddInfo(
    const p4_constraints::ConstraintInfo& constraints, Cudd* mgr);

}  // namespace p4_fuzzer

#endif  // P4_FUZZER_CONSTRAINTS_UTIL_H_
