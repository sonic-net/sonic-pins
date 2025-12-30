#include "lib/utils/reboot_operations.h"

#include "absl/status/status.h"
#include "absl/time/time.h"
#include "lib/validator/validator_lib.h"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

namespace pins_test {
namespace {

constexpr absl::Duration kRebootSshTimeout = absl::Seconds(10);

}  // namespace

absl::Status RebootSwitchWithSsh(thinkit::Switch& thinkit_switch,
                                 thinkit::SSHClient& ssh_client,
                                 absl::Duration down_timeout) {
  // Ignoring the error check of SSH reboot as it is non deterministic.
  ssh_client
      .RunCommand(thinkit_switch.ChassisName(), "reboot", kRebootSshTimeout)
      .IgnoreError();
  return WaitForNot(
      [&](absl::Duration timeout) {
        return SSHable(thinkit_switch, ssh_client, timeout);
      },
      down_timeout);
}

}  // namespace pins_test
