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
// limitations under the License

#include "p4_symbolic/symbolic/solver_state.h"

#include <ostream>
#include <sstream>
#include <string>

namespace p4_symbolic {
namespace symbolic {

std::string SolverState::GetSolverSMT() {
  if (!solver) return "";
  return solver->to_smt2();
}

std::string SolverState::GetHeadersAndSolverConstraintsSMT() {
  std::ostringstream result;
  for (const auto &[field_name, expression] : context.ingress_headers) {
    result << "(ingress) " << field_name << ": " << expression << std::endl;
  }
  result << std::endl;
  for (const auto &[field_name, expression] : context.parsed_headers) {
    result << "(parsed) " << field_name << ": " << expression << std::endl;
  }
  result << std::endl;
  for (const auto &[field_name, expression] : context.egress_headers) {
    result << "(egress) " << field_name << ": " << expression << std::endl;
  }
  result << std::endl << "(solver constraints)" << std::endl << GetSolverSMT();
  return result.str();
}

}  // namespace symbolic
}  // namespace p4_symbolic
