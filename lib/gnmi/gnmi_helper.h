#ifndef GOOGLE_LIB_GNMI_GNMI_HELPER_H_
#define GOOGLE_LIB_GNMI_GNMI_HELPER_H_

#include <cstddef>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "proto/gnmi/gnmi.pb.h"

namespace pins_test {

inline constexpr char kOpenconfigStr[] = "openconfig";

enum class GnmiSetType : char { kUpdate, kReplace, kDelete };

// Builds gNMI Set Request for a given OC path, set type and set value.
// The path should be in the following format below.
// "interfaces/interface[Ethernet0]/config/mtu".
// The set value should be in the format ex: {\"mtu\":2000}.
absl::StatusOr<gnmi::SetRequest> BuildGnmiSetRequest(
    absl::string_view oc_path, GnmiSetType set_type,
    absl::string_view json_val = {});

// Builds gNMI Get Request for a given OC path.
// The path should be in the following format below.
// "interfaces/interface[Ethernet0]/config/mtu".
absl::StatusOr<gnmi::GetRequest> BuildGnmiGetRequest(
    absl::string_view oc_path, gnmi::GetRequest::DataType req_type);

// Parses Get Response to retrieve specific tag value.
absl::StatusOr<std::string> ParseGnmiGetResponse(
    const gnmi::GetResponse& response, absl::string_view match_tag);

}  // namespace pins_test
#endif  // GOOGLE_LIB_GNMI_GNMI_HELPER_H_
