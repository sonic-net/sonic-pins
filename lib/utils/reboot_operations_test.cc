#include "lib/utils/reboot_operations.h"

#include <string>

#include "absl/status/status.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/gutil/status_matchers.h"
#include "thinkit/mock_ssh_client.h"
#include "thinkit/mock_switch.h"

namespace pins_test {
namespace {

using ::gutil::StatusIs;
using ::testing::_;
using ::testing::Return;
using ::testing::ReturnRefOfCopy;

TEST(RebootOperationsTest, RebootSwitchWithSshIgnoresRebootFail) {
  thinkit::MockSwitch mock_switch;
  EXPECT_CALL(mock_switch, ChassisName)
      .WillRepeatedly(ReturnRefOfCopy(std::string("chassis")));

  thinkit::MockSSHClient mock_ssh_client;
  EXPECT_CALL(mock_ssh_client, RunCommand("chassis", "echo foo", _))
      .WillOnce(Return("foo\n"))
      .WillOnce(Return(absl::UnavailableError("can't connect")));
  EXPECT_CALL(mock_ssh_client, RunCommand("chassis", "reboot", _))
      .WillOnce(Return(absl::UnavailableError("can't connect")));

  EXPECT_OK(RebootSwitchWithSsh(mock_switch, mock_ssh_client));
}

TEST(RebootOperationsTest, RebootSwitchWithSshDoesntGoDown) {
  thinkit::MockSwitch mock_switch;
  EXPECT_CALL(mock_switch, ChassisName)
      .WillRepeatedly(ReturnRefOfCopy(std::string("chassis")));

  thinkit::MockSSHClient mock_ssh_client;
  EXPECT_CALL(mock_ssh_client, RunCommand("chassis", "echo foo", _))
      .WillRepeatedly(Return("foo\n"));
  EXPECT_CALL(mock_ssh_client, RunCommand("chassis", "reboot", _))
      .WillOnce(Return(absl::UnavailableError("can't connect")));

  EXPECT_THAT(RebootSwitchWithSsh(mock_switch, mock_ssh_client,
                                  /*down_timeout=*/absl::Seconds(1)),
              StatusIs(absl::StatusCode::kDeadlineExceeded));
}

}  // namespace
}  // namespace pins_test
