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

#ifndef PINS_SAI_P4_TOOLS_P4INFO_TOOLS_H_
#define PINS_SAI_P4_TOOLS_P4INFO_TOOLS_H_

#include "p4/config/v1/p4info.pb.h"
#include "sai_p4/instantiations/google/instantiations.h"

namespace sai {

// Replaces all @sai_hash_seed() annotations with value 0 to the provided seed.
// Returns true if any hash seed was set.
bool SetSaiHashSeed(p4::config::v1::P4Info &p4info, uint32_t seed);

// Modifies all action profiles to use the sum_of_members semantics and sets
// their various sizes accordingly using the minimum guaranteed size library.
// Returns true if any field was changed.
bool ApplySumOfMembersSemanticsForActionProfiles(
    p4::config::v1::P4Info& p4info);

// Modifies all action profiles to use the sum_of_weights semantics and sets
// their various sizes accordingly using the minimum guaranteed size library.
// Since our ToRs generally have smaller guarantees, the `is_tor` boolean
// accounts for that when getting the correct value from the library.
// Returns true if any field was changed.
bool ApplySumOfWeightsSemanticsForActionProfiles(
    sai::Instantiation instantiation, p4::config::v1::P4Info& p4info);

}  // namespace sai

#endif // PINS_SAI_P4_TOOLS_P4INFO_TOOLS_H_
