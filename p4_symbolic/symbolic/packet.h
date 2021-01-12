// Copyright 2020 Google LLC
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

// Contains helpers for creating, extracting, and managing concerete and
// symbolic packet structs.

#ifndef P4_SYMBOLIC_SYMBOLIC_PACKET_H_
#define P4_SYMBOLIC_SYMBOLIC_PACKET_H_

#include "gutil/status.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "z3++.h"

namespace p4_symbolic {
namespace symbolic {
namespace packet {

// Extract the packet fields from their p4 program counterparts.
SymbolicPacket ExtractSymbolicPacket(SymbolicPerPacketState state);

// Extract a concrete packet by evaluating every field's corresponding
// expression in the model.
ConcretePacket ExtractConcretePacket(SymbolicPacket packet, z3::model model);

}  // namespace packet
}  // namespace symbolic
}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_SYMBOLIC_PACKET_H_
