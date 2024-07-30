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

#ifndef PINS_DVAAS_test_run_validation_H_
#define PINS_DVAAS_test_run_validation_H_

#include <string>
#include <vector>

#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/types/span.h"
#include "dvaas/output_writer.h"
#include "dvaas/test_vector.pb.h"
#include "google/protobuf/descriptor.h"

namespace dvaas {

// Validates the given `test_vector` and returns the result.
// Validation compares the actual output packets against the expected output
// packets modulo `ignored_fields` and `ignored_metadata, where:
// * `ignored_fields` must belong to packetlib::Packet, and
// * `ignored_metadata` must be the names of Packet In metadata fields.
PacketTestValidationResult ValidateTestRun(
    const PacketTestRun& test_run,
    const absl::flat_hash_set<std::string>& ignored_packet_in_metadata = {},
    const std::vector<const google::protobuf::FieldDescriptor*>&
        ignored_fields = {});

// Like `ValidateTestRun`, but for a collection of `test_runs`. Also
// writes the results to a test artifact using `write_failures`.
absl::Status ValidateTestRuns(
    const PacketTestRuns& test_runs,
    std::vector<const google::protobuf::FieldDescriptor*> ignored_fields,
    const absl::flat_hash_set<std::string>& ignored_metadata,
    const OutputWriterFunctionType& write_failures);

}  // namespace dvaas

#endif  // PINS_DVAAS_test_run_validation_H_
