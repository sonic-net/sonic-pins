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

#ifndef PINS_DVAAS_TEST_VECTOR_STATS_H_
#define PINS_DVAAS_TEST_VECTOR_STATS_H_

#include <string>

#include "dvaas/test_vector.pb.h"

namespace dvaas {

struct TestVectorStats {
  int num_vectors = 0;
  int num_vectors_passed = 0;
  // Can be higher than `num_vectors_passed`, e.g. because the outputs
  // could have incorrect header field values.
  int num_vectors_with_correct_number_of_outputs = 0;
  int num_vectors_forwarding = 0;
  int num_vectors_punting = 0;
  int num_vectors_dropping = 0;

  int num_packets_forwarded = 0;
  int num_packets_punted = 0;
};

TestVectorStats ComputeTestVectorStats(const PacketTestOutcomes &test_outcomes);

std::string ExplainTestVectorStats(const TestVectorStats &stats);

} // namespace dvaas

#endif // PINS_DVAAS_TEST_VECTOR_STATS_H_
