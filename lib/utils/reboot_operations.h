#ifndef PINS_LIB_UTILS_REBOOT_OPERATIONS_H_
#define PINS_LIB_UTILS_REBOOT_OPERATIONS_H_

#include "absl/status/status.h"
#include "absl/time/time.h"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

namespace pins_test {

constexpr absl::Duration kDefaultDownTimeout = absl::Seconds(75);

// Reboots the switch using SSH and waits for the switch to go down.
absl::Status RebootSwitchWithSsh(
    thinkit::Switch& thinkit_switch, thinkit::SSHClient& ssh_client,
    absl::Duration down_timeout = kDefaultDownTimeout);

}  // namespace pins_test

#endif  // PINS_LIB_UTILS_REBOOT_OPERATIONS_H_
