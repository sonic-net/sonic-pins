#include "sai_p4/instantiations/google/clos_stage.h"

#include <optional>
#include <string>

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "sai_p4/instantiations/google/instantiations.h"

namespace sai {

bool DiffersByClosStage(Instantiation instantiation) {
  switch (instantiation) {
    case Instantiation::kMiddleblock:
    case Instantiation::kFabricBorderRouter:
      return true;
    case Instantiation::kTor:
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

bool AbslParseFlag(absl::string_view stage_txt, ClosStage* stage,
                   std::string* error) {
  if (stage_txt == "Stage2") {
    *stage = ClosStage::kStage2;
    return true;
  }
  if (stage_txt == "Stage3") {
    *stage = ClosStage::kStage3;
    return true;
  }
  *error = absl::StrCat("Invalid CLOS stage: ", stage_txt);
  return false;
}

std::string AbslUnparseFlag(ClosStage stage) {
  return ClosStageToString(stage);
}

}  // namespace sai
