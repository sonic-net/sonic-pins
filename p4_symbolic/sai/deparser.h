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
#ifndef PINS_P4_SYMBOLIC_SAI_DEPARSER_H_
#define PINS_P4_SYMBOLIC_SAI_DEPARSER_H_

#include "absl/status/statusor.h"
#include "gutil/status.h"
#include "p4_pdpi/string_encodings/bit_string.h"
#include "p4_symbolic/sai/fields.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "z3++.h"

namespace p4_symbolic {

// Deparses the given packet into a byte string, using values according to the
// given model.
absl::StatusOr<std::string>
SaiDeparser(const symbolic::SymbolicPerPacketState &packet,
            const z3::model &model);
absl::StatusOr<std::string> SaiDeparser(const SaiFields &packet,
                                        const z3::model &model);

} // namespace p4_symbolic
#endif // PINS_P4_SYMBOLIC_SAI_DEPARSER_H_
