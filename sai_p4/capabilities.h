#ifndef PINS_SAI_P4_CAPABILITIES_H_
#define PINS_SAI_P4_CAPABILITIES_H_

#include "absl/status/status.h"
#include "p4/v1/p4runtime.pb.h"
#include "sai_p4/capabilities.pb.h"

namespace sai {

// Adds `experimental_resource_capabilities` to `response`. Returns an error if
// `experimental_resource_capabilities` cannot be added into `response`.
absl::Status AddExperimentalResourceCapabilities(
    ExperimentalResourceCapabilities capabilities,
    p4::v1::CapabilitiesResponse& response);

// If `response` contains a `ExperimentalResourceCapabilities`, returns it.
// Otherwise, returns an empty `ExperimentalResourceCapabilities`.
ExperimentalResourceCapabilities GetExperimentalResourceCapabilities(
    const p4::v1::CapabilitiesResponse& response);

// If `response` contains a `WcmpGroupLimitations`, returns it.
// Otherwise, returns an empty `WcmpGroupLimitations`.
WcmpGroupLimitations GetWcmpGroupLimitations(
    const p4::v1::CapabilitiesResponse& response);

}  // namespace sai

#endif  // PINS_SAI_P4_CAPABILITIES_H_
