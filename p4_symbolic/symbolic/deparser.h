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

#ifndef P4_SYMBOLIC_SYMBOLIC_DEPARSER_H_
#define P4_SYMBOLIC_SYMBOLIC_DEPARSER_H_

#include <string>

#include "absl/status/statusor.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "z3++.h"

namespace p4_symbolic {

// Deparses the ingress packet from the given symbolic solver `state` into a
// byte string, using values according to the given `model`.
absl::StatusOr<std::string> DeparseIngressPacket(
    const symbolic::SolverState& state, const z3::model& model);

// Deparses the egress packet from the given symbolic solver `state` into a byte
// string, using values according to the given `model`.
absl::StatusOr<std::string> DeparseEgressPacket(
    const symbolic::SolverState& state, const z3::model& model);

}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_DEPARSER_H_
