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

// Hardcodes the behavior of an interesting p4 parser that is part
// of the p4 program we are interested in.
// The hardcoded behavior sets the validity of certain header fields
// based on the fields in the packet, and sets the default values
// for local_metadata fields.

#ifndef GOOGLE_P4_SYMBOLIC_SAI_PARSER_H_
#define GOOGLE_P4_SYMBOLIC_SAI_PARSER_H_

#include <vector>

#include "gutil/status.h"
#include "p4_symbolic/symbolic/symbolic.h"

namespace p4_symbolic {

// Generates constraints encoding the behavior of the SAI parser.
// NOTE: The parser logic is currently hard-coded and not parsed from the
// program.
absl::StatusOr<std::vector<z3::expr>> EvaluateSaiParser(
    const symbolic::SymbolicPerPacketState &state);

}  // namespace p4_symbolic

#endif  // GOOGLE_P4_SYMBOLIC_SAI_PARSER_H_
