#ifndef PINS_INFRA_SAI_P4_INSTANTIATIONS_GOOGLE_GOOGLE_INSTANTIATIONS_H_
#define PINS_INFRA_SAI_P4_INSTANTIATIONS_GOOGLE_GOOGLE_INSTANTIATIONS_H_

#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "glog/logging.h"

namespace sai {

// Describes the role of a switch.
// Switches in the same role use the same P4 program (though the P4Info may be
// slightly modified further for each switch within a role, e.g. to configure
// the hashing seed).
enum class Instantiation {
  kFabricBorderRouter,
  kMiddleblock,
  kWbb,
};

// Returns all switch roles.
inline std::vector<Instantiation> AllInstantiations() {
  return {
      Instantiation::kFabricBorderRouter,
      Instantiation::kMiddleblock,
      Instantiation::kWbb,
  };
}

// Returns the name of the given switch role.
inline std::string InstantiationToString(Instantiation role) {
  switch (role) {
    case Instantiation::kFabricBorderRouter:
      return "fabric_border_router";
    case Instantiation::kMiddleblock:
      return "middleblock";
    case Instantiation::kWbb:
      return "wbb";
  }
  LOG(DFATAL) << "invalid Instantiation: " << static_cast<int>(role);
  return "";
}

// Returns the name of the given switch role.
inline absl::StatusOr<Instantiation> StringToInstantiation(
    absl::string_view instantiation_name) {
  for (auto instantiation : AllInstantiations()) {
    if (instantiation_name == InstantiationToString(instantiation)) {
      return instantiation;
    }
  }
  return absl::InvalidArgumentError(
      absl::StrCat("invalid Instantiation: ", instantiation_name));
}

// Parses an Instantiation from the command line flag value
// `instantiation_text`. Returns true and sets `*instantiation` on success;
// returns false and sets `*error` on failure.
// See https://abseil.io/docs/cpp/guides/flags#validating-flag-values for more
// information.
bool AbslParseFlag(absl::string_view instantiation_text,
                   Instantiation* instantiation, std::string* error);

// Returns a textual flag value corresponding to the given instantiation.
std::string AbslUnparseFlag(Instantiation instantiation);

inline std::ostream& operator<<(std::ostream& os, Instantiation instantiation) {
  return os << InstantiationToString(instantiation);
}

}  // namespace sai

#endif  // PINS_INFRA_SAI_P4_INSTANTIATIONS_GOOGLE_GOOGLE_INSTANTIATIONS_H_
