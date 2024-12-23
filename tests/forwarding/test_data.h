// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#ifndef PINS_TESTS_FORWARDING_TEST_DATA_H_
#define PINS_TESTS_FORWARDING_TEST_DATA_H_

#include "sai_p4/instantiations/google/sai_pd.pb.h"

// TODO Move it to the sai_pd library when it is available.
namespace sai_pd {

// Returns a vector of N generic table entries. It is up to the implementation
// to pick the table, match fields, action, etc, but the function guarantees the
// entries are valid. Useful for testing when the exact table entry doesn't
// matter.
std::vector<sai::TableEntry>
CreateUpTo255GenericTableEntries(int num_table_entries);

} // namespace sai_pd

#endif // PINS_TESTS_FORWARDING_TEST_DATA_H_
