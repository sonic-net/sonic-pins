#ifndef PINS_SAI_P4_INSTANTIATIONS_GOOGLE_CLOS_STAGE_H_
#define PINS_SAI_P4_INSTANTIATIONS_GOOGLE_CLOS_STAGE_H_

#include <optional>
#include <ostream>
#include <string>
#include <vector>

#include "absl/log/log.h"
#include "sai_p4/instantiations/google/instantiations.h"
namespace sai {

// Enum representing the stage of the CLOS network. Applies to middleblock
// instantiations.
enum class ClosStage {
  kStage2,
  kStage3,
};

inline std::vector<ClosStage> AllStages() {
  return {
      ClosStage::kStage2,
      ClosStage::kStage3,
  };
}

inline std::string ClosStageToString(ClosStage stage) {
  switch (stage) {
  case ClosStage::kStage2:
    return "Stage2";
  case ClosStage::kStage3:
    return "Stage3";
  }
  LOG(DFATAL) << "invalid ClosStage: " << static_cast<int>(stage);
  return "";
}

inline std::ostream &operator<<(std::ostream &os, ClosStage stage) {
  return os << ClosStageToString(stage);
}

// Returns true if the given `instantiation` is used in different CLOS stages.
bool DiffersByClosStage(Instantiation instantiation);

// Returns an error if the given `instantiation` and CLOS `stage` pair are
// incompatible.
absl::Status
AssertInstantiationAndClosStageAreCompatible(Instantiation instantiation,
                                             std::optional<ClosStage> stage);

bool AbslParseFlag(absl::string_view stage_txt, ClosStage *stage,
                   std::string *error);

std::string AbslUnparseFlag(ClosStage stage);

} // namespace sai

#endif // PINS_SAI_P4_INSTANTIATIONS_GOOGLE_CLOS_STAGE_H_
