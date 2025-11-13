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

namespace sai {

// Replaces all @sai_hash_seed() annotations with value 0 to the provided seed.
// Returns true if any hash seed was set.
bool SetSaiHashSeed(p4::config::v1::P4Info &p4info, uint32_t seed);

// Parameters for applying sum of weights WCMP capacity.
struct SumOfWeightsCapacity {
  int total_weight;
  int max_group_size;
};

// Parameters for applying sum of members WCMP capacity.
struct SumOfMembersCapacity {
  int total_members;
  int max_group_size;
  int max_member_weight;
};

// Overrides the current WCMP capacity settings with the requested settings.
// Returns true if the override was applied or if the existing P4Info matches
// the overridden settings.
bool OverrideWcmpCapacity(p4::config::v1::P4Info& p4_info,
                          const SumOfMembersCapacity& capacity);
bool OverrideWcmpCapacity(p4::config::v1::P4Info& p4_info,
                          const SumOfWeightsCapacity& capacity);

}  // namespace sai

#endif // PINS_SAI_P4_TOOLS_P4INFO_TOOLS_H_
