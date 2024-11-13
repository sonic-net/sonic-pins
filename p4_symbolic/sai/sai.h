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
#ifndef PINS_P4_SYMBOLIC_SAI_TEST_UTIL_H_
#define PINS_P4_SYMBOLIC_SAI_TEST_UTIL_H_

#include <memory>
#include <vector>

#include "absl/status/statusor.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_symbolic/sai/fields.h"
#include "p4_symbolic/symbolic/symbolic.h"

namespace p4_symbolic {

constexpr char kPortIdTypeName[] = "port_id_t";

// Symbolically evaluates the SAI P4 program for the given forwarding pipeline
// config with the given table entries. If `physical_ports` is non-empty, any
// solution is guaranteed to only use ports from the list. Note that the set of
// `physical_ports` should be consistent with the numeric values used in the
// static translation of "port_id_t" in `translation_per_type`, otherwise
// returns an error.
absl::StatusOr<std::unique_ptr<symbolic::SolverState>> EvaluateSaiPipeline(
    const p4::v1::ForwardingPipelineConfig& config,
    const std::vector<p4::v1::TableEntry>& entries,
    const std::vector<int>& physical_ports = {},
    const symbolic::StaticTranslationPerType& translation_per_type = {});

absl::StatusOr<std::string> ExtractLocalMetadataIngressPortFromModel(
    const symbolic::SolverState& solver_state);

}  // namespace p4_symbolic

#endif  // PINS_P4_SYMBOLIC_SAI_TEST_UTIL_H_
