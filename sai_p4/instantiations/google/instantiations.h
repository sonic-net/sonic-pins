#ifndef GOOGLE_SAI_P4_INSTANTIATIONS_GOOGLE_GOOGLE_INSTANTIATIONS_H_
#define GOOGLE_SAI_P4_INSTANTIATIONS_GOOGLE_GOOGLE_INSTANTIATIONS_H_

#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "glog/logging.h"

namespace sai {

// Describes the role of a switch.
// Switches in the same role use the same P4 program (though the P4Info may be
// slightly modified further for each switch within a role, e.g. to configure
// the hashing seed).
enum class Instantiation {
  kMiddleblock,
};

// Returns all switch roles.
inline std::vector<Instantiation> AllInstantiations() {
  return {
      Instantiation::kMiddleblock,
  };
}

// Returns the name of the given switch role.
inline std::string InstantiationToString(Instantiation role) {
  switch (role) {
    case Instantiation::kMiddleblock:
      return "middleblock";
  }
  LOG(DFATAL) << "invalid Instantiation: " << static_cast<int>(role);
  return "";
}

// Returns the name of the given switch role.
inline absl::StatusOr<Instantiation> StringToInstantiation(
    const std::string& instantiation_name) {
  for (auto instantiation : AllInstantiations()) {
    if (instantiation_name == InstantiationToString(instantiation)) {
      return instantiation;
    }
  }
  return absl::InvalidArgumentError(
      absl::StrCat("invalid Instantiation: ", instantiation_name));
}

inline std::ostream& operator<<(std::ostream& os, Instantiation instantiation) {
  return os << InstantiationToString(instantiation);
}

}  // namespace sai

#endif  // GOOGLE_SAI_P4_INSTANTIATIONS_GOOGLE_GOOGLE_INSTANTIATIONS_H_
