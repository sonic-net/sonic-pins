#include "sai_p4/capabilities.h"

#include <utility>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "google/protobuf/any.pb.h"
#include "gutil/gutil/status.h"
#include "p4/v1/p4runtime.pb.h"
#include "sai_p4/capabilities.pb.h"

namespace sai {

using ::p4::v1::CapabilitiesResponse;

absl::Status AddExperimentalResourceCapabilities(
    ExperimentalResourceCapabilities capabilities,
    CapabilitiesResponse& response) {
  if (!response.mutable_experimental()->PackFrom(std::move(capabilities))) {
    return absl::InvalidArgumentError(
        "Failed to pack ExperimentalResourceCapabilities into "
        "CapabilitiesResponse.");
  }
  return absl::OkStatus();
}

absl::StatusOr<ExperimentalResourceCapabilities>
GetExperimentalResourceCapabilities(const CapabilitiesResponse& response) {
  ExperimentalResourceCapabilities capabilities;
  if (!response.has_experimental() ||
      !response.experimental().UnpackTo(&capabilities)) {
    return absl::NotFoundError(absl::StrCat(
        "ExperimentalResourceCapabilities not found in CapabilitiesResponse: ",
        response.DebugString()));
  }
  return capabilities;
};

absl::StatusOr<WcmpGroupLimitations> GetWcmpGroupLimitations(
    const CapabilitiesResponse& response) {
  ASSIGN_OR_RETURN(ExperimentalResourceCapabilities capabilities,
                   GetExperimentalResourceCapabilities(response));
  return capabilities.wcmp_group_limitations();
}

}  // namespace sai
