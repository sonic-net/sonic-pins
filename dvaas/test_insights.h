// Copyright (c) 2025, Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#ifndef PINS_DVAAS_TEST_INSIGHTS_H_
#define PINS_DVAAS_TEST_INSIGHTS_H_

#include <string>

#include "absl/status/statusor.h"
#include "absl/types/span.h"
#include "dvaas/packet_trace.pb.h"
#include "dvaas/test_vector.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"

namespace dvaas {

// Returns a CSV table of test vector insights for the given packet test
// vectors. Each row corresponds to a one packet test vector. Columns include
// various features of the test packet, including actions applied per table,
// acceptable outcomes, etc.
absl::StatusOr<std::string> GetTestInsightsTableAsCsv(
    absl::Span<const dvaas::PacketTestVector> packet_test_vectors,
    const pdpi::IrP4Info& ir_p4info);

// Returns a CSV table of test outcome insights for the given packet test
// outcomes. Each row corresponds to a one packet test outcome. Columns include
// various features of the test packet, including actions applied per table,
// acceptable outcomes, actual outcome, validation result, etc.
absl::StatusOr<std::string> GetTestInsightsTableAsCsv(
    const PacketTestOutcomes& packet_test_outcomes,
    const pdpi::IrP4Info& ir_p4info);

}  // namespace dvaas

#endif  // PINS_DVAAS_TEST_INSIGHTS_H_
