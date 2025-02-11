#ifndef PINS_TESTS_GNMI_UTIL_H_
#define PINS_TESTS_GNMI_UTIL_H_

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "proto/gnmi/gnmi.grpc.pb.h"

namespace pins_test {

absl::Status SetAdminStatus(gnmi::gNMI::StubInterface* gnmi_stub,
                            absl::string_view if_name,
                            absl::string_view if_status);

}  // namespace pins_test

#endif  // PINS_TESTS_GNMI_UTIL_H_
