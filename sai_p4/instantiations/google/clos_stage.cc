#include "sai_p4/instantiations/google/clos_stage.h"

#include <optional>

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/substitute.h"
#include "glog/logging.h"
#include "sai_p4/instantiations/google/instantiations.h"

namespace sai {

bool DiffersByClosStage(Instantiation instantiation) {
  switch (instantiation) {
    case Instantiation::kMiddleblock:
    case Instantiation::kFabricBorderRouter:
      return true;
    case Instantiation::kWbb:
      return false;
  }
  LOG(DFATAL) << absl::StrCat("invalid instantiation '$0'",
                              static_cast<int>(instantiation));
  return false;
}

absl::Status AssertInstantiationAndClosStageAreCompatible(
    Instantiation instantiation, std::optional<ClosStage> stage) {
  // If an instantiation admits different CLOS stages, then a CLOS stage must be
  // given.
  if (sai::DiffersByClosStage(instantiation) && !stage.has_value()) {
    return absl::InvalidArgumentError(
        absl::Substitute("Instantiation '$0' exists for different CLOS stages, "
                         "but no CLOS stage was given.",
                         sai::InstantiationToString(instantiation)));
  }
  // Otherwise, a CLOS stage may not be given.
  if (!sai::DiffersByClosStage(instantiation) && stage.has_value()) {
    return absl::InvalidArgumentError(absl::Substitute(
        "Instantiation '$0' does not exist for different CLOS stages, "
        "but CLOS stage $1 was given.",
        sai::InstantiationToString(instantiation),
        sai::ClosStageToString(*stage)));
  }
  return absl::OkStatus();
}
}  // namespace sai
