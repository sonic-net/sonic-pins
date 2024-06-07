#include "p4_fuzzer/constraints_util.h"

#include <bitset>
#include <cstdio>

#include "absl/status/status.h"
#include "absl/strings/numbers.h"
#include "absl/strings/str_cat.h"
#include "cudd.h"
#include "cuddObj.hh"
#include "glog/logging.h"
#include "gmpxx.h"
#include "p4_constraints/ast.pb.h"
#include "p4_constraints/backend/constraint_info.h"

namespace p4_fuzzer {
namespace {

using p4_constraints::ast::Expression;
using p4_constraints::ast::Type;

// Takes an arbitrary length GMP integer (mpz_class). Returns a symbolic bit
// vector corresponding to the GMP integer.
SymbolicBitVector SymbolicBitVectorFromGMPInteger(mpz_class mpz,
                                                  const int bitwidth) {
  const mpz_class one = mpz_class(1);
  const mpz_class domain_size = one << bitwidth;  // 2^bitwidth
  mpz %= domain_size;

  // We want the mathematical mod. The % operator can return negative values.
  if (mpz < mpz_class(0)) {
    mpz += domain_size;
  }

  SymbolicBitVector bit_vector;
  for (int i = 0; i < bitwidth; i++) {
    bit_vector.push_back((mpz & one) == one);
    mpz /= 2;
  }

  return bit_vector;
}

// Converts an integer from a string to an mpz_class.
absl::StatusOr<mpz_class> ParseInteger(const std::string& int_str) {
  mpz_class integer;
  const char* chars = int_str.c_str();
  size_t char_count = strlen(chars);
  constexpr int most_significant_first = 1;
  constexpr size_t char_size = sizeof(char);
  static_assert(char_size == 1, "expected sizeof(char) == 1");
  constexpr int endian = 0;    // system default
  constexpr size_t nails = 0;  // don't skip any bits
  mpz_import(integer.get_mpz_t(), char_count, most_significant_first, char_size,
             endian, nails, chars);
  return integer;
}

// Converts an ast::Expression that is not of type bool (such as an
// integer constant) to a SymbolicBitVectors. Returns an error
// if the given expression is invalid or is of type bool.
absl::StatusOr<SymbolicBitVector> TranslateNonBooleanExpression(
    const p4_constraints::ast::Expression& expr,
    MatchKeyToBddVariableMapping* mapping) {
  switch (expr.expression_case()) {
    case Expression::kTypeCast: {
      const Expression& inner = expr.type_cast().type_cast();
      if (expr.type().type_case() != Type::kExact ||
          expr.type_cast().type().type_case() != Type::kFixedUnsigned ||
          expr.type_cast().type_cast().type().type_case() !=
              Type::kArbitraryInt) {
        // TODO: support other types of casts.
        return absl::UnimplementedError(
            "Only casts from int to bit<w> supported.");
      }

      mpz_class integer(inner.integer_constant());

      return SymbolicBitVectorFromGMPInteger(
          integer, expr.type_cast().type().fixed_unsigned().bitwidth());
    }

    case Expression::kKey: {
      ASSIGN_OR_RETURN(std::vector<BddVariable> bdd_vars,
                       mapping->GetOrAllocateBddVariablesForKey(expr));
      // We need to convert the returned array of BddVariables into a
      // SymbolicBitVector so it can work nicely with non-boolean expressions
      // (e.g in operators such as Equals(), see above).
      SymbolicBitVector bit_vec;
      for (BddVariable bdd_var : bdd_vars) {
        bit_vec.push_back(bdd_var);
      }

      return bit_vec;
    }

    default:
      break;
  }

  return absl::InvalidArgumentError(absl::StrCat(
      "Expected non-boolean expression, but got: ", expr.DebugString()));
}

// Constructs a BDD that represents the equality of two same-sized
// SymbolicBitVectors.
absl::StatusOr<BDD> Equals(const SymbolicBitVector& left,
                           const SymbolicBitVector& right, Cudd* mgr) {
  if (left.size() != right.size()) {
    return absl::InvalidArgumentError(
        "SymbolicBitVectors must be of the same size");
  }

  BDD result = mgr->bddOne();

  for (int i = 0; i < left.size(); i++) {
    const bool* left_bool = absl::get_if<bool>(&left[i]);
    const bool* right_bool = absl::get_if<bool>(&right[i]);

    const BddVariable* left_var = absl::get_if<BddVariable>(&left[i]);
    const BddVariable* right_var = absl::get_if<BddVariable>(&right[i]);

    if (left_bool != nullptr && right_bool != nullptr) {
      result &= (*left_bool == *right_bool) ? mgr->bddOne() : mgr->bddZero();
    } else if (left_var != nullptr && right_bool != nullptr) {
      BDD left_bdd = mgr->bddVar(*left_var);
      result &= (*right_bool) ? left_bdd : !left_bdd;
    } else if (left_bool != nullptr && right_var != nullptr) {
      BDD right_bdd = mgr->bddVar(*right_var);
      result &= (*left_bool) ? right_bdd : !right_bdd;
    } else if (left_var != nullptr && right_var != nullptr) {
      BDD left_bdd = mgr->bddVar(*left_var);
      BDD right_bdd = mgr->bddVar(*right_var);
      result &= ((left_bdd & right_bdd) | ((!left_bdd) & (!right_bdd)));
    } else {
      return absl::InternalError("Impossible");
    }
  }

  return result;
}

// Converts a given ast::Expression to a BDD. `mapping` encodes which match
// field each BDD variable belongs to (and vice versa).
absl::StatusOr<BDD> TranslateBooleanExpression(
    const p4_constraints::ast::Expression& expr, Cudd* mgr,
    MatchKeyToBddVariableMapping* mapping) {
  switch (expr.expression_case()) {
    case Expression::kBinaryExpression: {
      switch (expr.binary_expression().binop()) {
        case p4_constraints::ast::BinaryOperator::EQ:
        case p4_constraints::ast::BinaryOperator::NE: {
          // TODO: also handle the case where the left and/or right
          // expressions are boolean.
          ASSIGN_OR_RETURN(SymbolicBitVector left,
                           TranslateNonBooleanExpression(
                               expr.binary_expression().left(), mapping));
          ASSIGN_OR_RETURN(SymbolicBitVector right,
                           TranslateNonBooleanExpression(
                               expr.binary_expression().right(), mapping));
          ASSIGN_OR_RETURN(BDD bdd, Equals(left, right, mgr));

          if (expr.binary_expression().binop() ==
              p4_constraints::ast::BinaryOperator::EQ) {
            return bdd;
          }

          if (expr.binary_expression().binop() ==
              p4_constraints::ast::BinaryOperator::NE) {
            return !bdd;
          }
        }
          [[fallthrough]];

        default:
          // TODO: add support for binary operators &&, || and ->.
          return absl::UnimplementedError(
              "Only == and != supported currently.");
      }
    }

    default:
      break;
  }

  return absl::InvalidArgumentError(
      absl::StrCat("Unsupported expression: ", expr.DebugString()));
}

}  // namespace

absl::Status MatchKeyToBddVariableMapping::AddEntry(
    const MatchFieldBit& field_bit, BddVariable bdd_var) {
  auto [iter, inserted] = key_to_bdd_.insert({field_bit, bdd_var});
  auto [second_iter, second_inserted] =
      bdd_to_key_.insert({bdd_var, field_bit});

  if (!second_inserted || !inserted) {
    return absl::InternalError(
        absl::StrCat("Unable to add entry: ", field_bit.name, ",",
                     field_bit.bit, ",", bdd_var));
  }

  return absl::OkStatus();
}

absl::StatusOr<BddVariable>
MatchKeyToBddVariableMapping::GetOrAllocateBddVariable(
    const MatchFieldBit& field_bit) {
  auto search = key_to_bdd_.find(field_bit);

  if (search != key_to_bdd_.end()) {
    return search->second;
  }

  BddVariable bdd_var = bdd_var_latest_;
  ++bdd_var_latest_;

  RETURN_IF_ERROR(AddEntry(field_bit, bdd_var));

  return bdd_var;
}

absl::StatusOr<std::vector<BddVariable>>
MatchKeyToBddVariableMapping::GetOrAllocateBddVariablesForKey(
    const p4_constraints::ast::Expression& expr) {
  if (expr.expression_case() != Expression::kKey) {
    return absl::InvalidArgumentError("Must take expression of type key");
  }

  if (expr.type().type_case() != Type::kExact) {
    return absl::UnimplementedError("Only exact type supported currently.");
  }

  int bitwidth = expr.type().exact().bitwidth();

  std::vector<BddVariable> vars;
  for (int i = 0; i < bitwidth; i++) {
    ASSIGN_OR_RETURN(
        BddVariable bdd_var,
        GetOrAllocateBddVariable(MatchFieldBit{.name = expr.key(), .bit = i}));
    vars.push_back(bdd_var);
  }

  return vars;
}

absl::StatusOr<BDD> ExpressionToBDD(const p4_constraints::ast::Expression& expr,
                                    Cudd* mgr,
                                    MatchKeyToBddVariableMapping* mapping) {
  return TranslateBooleanExpression(expr, mgr, mapping);
}

void PrintBDDAsDotFile(const BDD& bdd, Cudd* mgr) {
  mgr->DumpDot(/*nodes =*/std::vector<ADD>{bdd.Add()});
}

absl::StatusOr<BDDInfo> ConstraintToBddInfo(
    const p4_constraints::ConstraintInfo& constraints, Cudd* mgr) {
  BDDInfo bdd_info;

  for (auto& [id, table_info] : constraints) {
    if (!table_info.constraint.has_value()) {
      continue;
    }

    const auto& expr = table_info.constraint.value();

    MatchKeyToBddVariableMapping mapping;
    ASSIGN_OR_RETURN(BDD bdd, ExpressionToBDD(expr, mgr, &mapping));

    auto [_, inserted] =
        bdd_info.insert({id, SymbolicConstraint{bdd, mapping}});

    if (!inserted) {
      return absl::InternalError(absl::StrCat(
          "Duplicate constraint for table ID ", id, ": ", expr.DebugString()));
    }
  }

  return bdd_info;
}

}  // namespace p4_fuzzer
