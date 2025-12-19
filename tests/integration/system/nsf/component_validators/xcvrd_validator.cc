#include "tests/integration/system/nsf/component_validators/xcvrd_validator.h"

#include <string>
#include <vector>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_split.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "gutil/status.h"
#include "lib/gnmi/gnmi_helper.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "tests/integration/system/nsf/util.h"
#include "tests/thinkit_gnmi_interface_util.h"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

namespace pins_test {

namespace {

absl::Status ValidateXcvrdWarmboot(const Testbed& testbed,
                                   thinkit::SSHClient& ssh_client) {
  return absl::OkStatus();
}
}  // namespace

absl::Status XcvrdValidator::OnNsfReboot(absl::string_view version,
                                         const Testbed& testbed,
                                         thinkit::SSHClient& ssh_client) {
  return ValidateXcvrdWarmboot(testbed, ssh_client);
}

}  // namespace pins_test
