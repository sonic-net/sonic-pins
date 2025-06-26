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

#include "sai_p4/tools/p4info_tools.h"

#include <string>
#include <vector>

#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_pdpi/utils/annotation_parser.h"
#include "sai_p4/instantiations/google/minimum_guaranteed_sizes.h"

namespace sai {

bool SetSaiHashSeed(p4::config::v1::P4Info& p4info, uint32_t seed) {
  bool set_any_hash = false;
  for (auto& action : *p4info.mutable_actions()) {
    for (auto& annotation : *action.mutable_preamble()->mutable_annotations()) {
      absl::StatusOr<std::string> result = pdpi::GetAnnotationBody(
          "sai_hash_seed", std::vector<std::string>({annotation}));
      if (result.ok() && *result == "0") {
        annotation.assign(absl::StrCat("@sai_hash_seed(", seed, ")"));
        set_any_hash = true;
      }
    }
  }
  return set_any_hash;
}

bool ApplySumOfMembersSemanticsForActionProfiles(
    p4::config::v1::P4Info& p4info) {
  int size = WCMP_GROUP_SUM_OF_MEMBERS_SIZE;
  int max_group_size = WCMP_GROUP_SELECTOR_SUM_OF_MEMBERS_MAX_GROUP_SIZE;
  int max_member_weight = WCMP_GROUP_SELECTOR_SUM_OF_MEMBERS_MAX_MEMBER_WEIGHT;
  bool modified_any_field = false;
  for (auto& action_profile : *p4info.mutable_action_profiles()) {
    // If nothing needs to change, then skip the action profile.
    if (action_profile.size() == size &&
        action_profile.max_group_size() == max_group_size &&
        action_profile.has_sum_of_members() &&
        action_profile.sum_of_members().max_member_weight() ==
            max_member_weight) {
      continue;
    }
    action_profile.set_size(size);
    action_profile.set_max_group_size(max_group_size);
    action_profile.mutable_sum_of_members()->set_max_member_weight(
        max_member_weight);

    modified_any_field = true;
  }
  return modified_any_field;
}

bool ApplySumOfWeightsSemanticsForActionProfiles(
    bool is_tor, p4::config::v1::P4Info& p4info) {
  int size, max_group_size;
  if (is_tor) {
    size = WCMP_GROUP_SUM_OF_WEIGHTS_SIZE_TOR;
    max_group_size = WCMP_GROUP_SELECTOR_SUM_OF_WEIGHTS_MAX_GROUP_SIZE_TOR;
  } else {
    size = WCMP_GROUP_SUM_OF_WEIGHTS_SIZE_NON_TOR;
    max_group_size = WCMP_GROUP_SELECTOR_SUM_OF_WEIGHTS_MAX_GROUP_SIZE_NON_TOR;
  }
  bool modified_any_field = false;
  for (auto& action_profile : *p4info.mutable_action_profiles()) {
    // If nothing needs to change, then skip the action profile.
    if (action_profile.size() == size &&
        action_profile.max_group_size() == max_group_size &&
        action_profile.has_sum_of_weights()) {
      continue;
    }
    action_profile.set_size(size);
    action_profile.set_max_group_size(max_group_size);
    action_profile.mutable_sum_of_weights();

    modified_any_field = true;
  }
  return modified_any_field;
}

}  // namespace sai
