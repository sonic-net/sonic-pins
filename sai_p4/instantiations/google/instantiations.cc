#include "sai_p4/instantiations/google/instantiations.h"

#include "absl/strings/substitute.h"

namespace sai {

bool AbslParseFlag(absl::string_view instantiation_text,
                   Instantiation* instantiation, std::string* error) {
  if (auto instantiation_status = StringToInstantiation(instantiation_text);
      instantiation_status.ok()) {
    *instantiation = *instantiation_status;
    return true;
  } else {
    *error =
        absl::Substitute("'$0' not a sai::Instantiation", instantiation_text);
    return false;
  }
}

// Returns a textual flag value corresponding to the given instantiation.
std::string AbslUnparseFlag(Instantiation instantiation) {
  return InstantiationToString(instantiation);
}

}  // namespace sai
