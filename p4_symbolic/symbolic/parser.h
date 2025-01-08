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

#ifndef PINS_P4_SYMBOLIC_SYMBOLIC_PARSER_H_
#define PINS_P4_SYMBOLIC_SYMBOLIC_PARSER_H_

#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/context.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {
namespace parser {

// Returns a Z3 bit-vector representing the `parser_error` field value of the
// given `error_name`.
absl::StatusOr<z3::expr> GetErrorCodeExpression(const ir::P4Program &program,
                                                const std::string &error_name,
                                                z3::context &z3_context);

// Evaluates all parsers in the P4 program and returns a map of symbolic headers
// that captures the effect of parser execution given the `ingress_headers`.
//
// Returns error if a header field is not a free bit-vector variable upon
// extracting its header, which could mean the header is extracted twice. We
// require extracting to the same header happens at most once to avoid loops.
//
// If a parser error occurs, the `standard_metadata.parser_error` field will be
// set to the corresponding error code and the function returns immediately. The
// current implementation may only result in 2 types of parser error, NoError
// and NoMatch.
absl::StatusOr<SymbolicPerPacketState> EvaluateParsers(
    const ir::P4Program &program, const SymbolicPerPacketState &ingress_headers,
    z3::context &z3_context);

} // namespace parser
} // namespace symbolic
} // namespace p4_symbolic

#endif // PINS_P4_SYMBOLIC_SYMBOLIC_PARSER_H_
