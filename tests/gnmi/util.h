#ifndef PINS_TESTS_GNMI_UTIL_H_
#define PINS_TESTS_GNMI_UTIL_H_

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "thinkit/generic_testbed.h"

namespace pins_test {

absl::Status SetAdminStatus(gnmi::gNMI::StubInterface* gnmi_stub,
                            absl::string_view if_name,
                            absl::string_view if_status,
                            absl::Duration timeout = absl::Seconds(15));

absl::Status FlapLink(gnmi::gNMI::StubInterface &gnmi_stub,
                      thinkit::GenericTestbed &generic_testbed,
                      absl::string_view sut_interface,
                      const thinkit::InterfaceInfo& host_interface_info,
                      bool is_ixia_testbed = false);

}  // namespace pins_test

#endif  // PINS_TESTS_GNMI_UTIL_H_
