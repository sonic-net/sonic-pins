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

#ifndef PINS_P4_SYMBOLIC_SAI_TEST_UTIL_H_
#define PINS_P4_SYMBOLIC_SAI_TEST_UTIL_H_

#include <memory>
#include <vector>

#include "absl/status/statusor.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_symbolic/symbolic/symbolic.h"
#include "sai_p4/instantiations/google/instantiations.h"

namespace p4_symbolic {

// Symbolically evaluates the SAI P4 program for the given instantiation with
// the given table entries. If `physical_ports` is non-empty, any solution is
// guaranteed to only use ports from the list.
absl::StatusOr<std::unique_ptr<symbolic::SolverState>> EvaluateSaiPipeline(
    sai::Instantiation instantiation,
    const std::vector<p4::v1::TableEntry>& entries,
    const std::vector<int>& physical_ports = {});

}  // namespace p4_symbolic

#endif  // PINS_P4_SYMBOLIC_SAI_TEST_UTIL_H_
