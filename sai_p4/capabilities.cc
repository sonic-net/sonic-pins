#include "sai_p4/capabilities.h"

#include <utility>

#include "absl/status/status.h"
#include "google/protobuf/any.pb.h"
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

ExperimentalResourceCapabilities GetExperimentalResourceCapabilities(
    const CapabilitiesResponse& response) {
  ExperimentalResourceCapabilities capabilities;
  response.experimental().UnpackTo(&capabilities);
  return capabilities;
};

WcmpGroupLimitations GetWcmpGroupLimitations(
    const CapabilitiesResponse& response) {
  ExperimentalResourceCapabilities capabilities =
      GetExperimentalResourceCapabilities(response);
  return capabilities.wcmp_group_limitations();
}

}  // namespace sai
