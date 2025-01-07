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

#ifndef P4_SYMBOLIC_SYMBOLIC_V1MODEL_H_
#define P4_SYMBOLIC_SYMBOLIC_V1MODEL_H_

#include <vector>

#include "p4_symbolic/ir/ir.h"
#include "p4_symbolic/symbolic/context.h"
#include "p4_symbolic/symbolic/values.h"

namespace p4_symbolic {
namespace symbolic {
namespace v1model {

// Initializes the ingress headers to appropriate values.
absl::Status InitializeIngressHeaders(const ir::P4Program &program,
                                      SymbolicPerPacketState &ingress_headers);

// Symbolically evaluates the parser, ingress, and egress pipelines of the given
// P4 program with the given entries, assuming the program is written against V1
// model.
absl::Status EvaluateV1model(const ir::Dataplane &data_plane,
                             const std::vector<int> &physical_ports,
                             SymbolicContext &context,
                             values::P4RuntimeTranslator &translator);

}  // namespace v1model
}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_V1MODEL_H_
