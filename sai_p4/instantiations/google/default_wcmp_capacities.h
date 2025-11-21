#ifndef PINS_SAI_P4_INSTANTIATIONS_GOOGLE_DEFAULT_WCMP_CAPACITIES_H_
#define PINS_SAI_P4_INSTANTIATIONS_GOOGLE_DEFAULT_WCMP_CAPACITIES_H_

// This file contains default WCMP capacity settings that can be used with the
// p4info_tools libraries.

#include "sai_p4/instantiations/google/minimum_guaranteed_sizes.h"
#include "sai_p4/tools/p4info_tools.h"

namespace sai {
constexpr SumOfWeightsCapacity kTorWeightCapacity{
    .total_weight = WCMP_GROUP_SUM_OF_WEIGHTS_SIZE_TOR,
    .max_group_size = WCMP_GROUP_SELECTOR_SUM_OF_WEIGHTS_MAX_GROUP_SIZE_TOR,
};

constexpr SumOfWeightsCapacity kNonTorWeightCapacity{
    .total_weight = WCMP_GROUP_SUM_OF_WEIGHTS_SIZE_NON_TOR,
    .max_group_size = WCMP_GROUP_SELECTOR_SUM_OF_WEIGHTS_MAX_GROUP_SIZE_NON_TOR,
};

constexpr SumOfMembersCapacity kDefaultMembersCapacity{
    .total_members = WCMP_GROUP_SUM_OF_MEMBERS_SIZE,
    .max_group_size = WCMP_GROUP_SELECTOR_SUM_OF_MEMBERS_MAX_GROUP_SIZE,
    .max_member_weight = WCMP_GROUP_SELECTOR_SUM_OF_MEMBERS_MAX_MEMBER_WEIGHT,
};

constexpr SumOfMembersCapacity kPodMembersCapacity{
    .total_members = WCMP_GROUP_SUM_OF_MEMBERS_SIZE_VIRGO,
    .max_group_size = WCMP_GROUP_SELECTOR_SUM_OF_MEMBERS_MAX_GROUP_SIZE_VIRGO,
    .max_member_weight =
        WCMP_GROUP_SELECTOR_SUM_OF_MEMBERS_MAX_MEMBER_WEIGHT_VIRGO,
};

}  // namespace sai

#endif  // PINS_SAI_P4_INSTANTIATIONS_GOOGLE_DEFAULT_WCMP_CAPACITIES_H_
