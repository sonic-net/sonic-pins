// Copyright (c) 2024, Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "lib/validator/validator_lib.h"

#include <cstdint>
#include <functional>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/match.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/status_matchers.h"
#include "thinkit/switch.h"

namespace pins_test {
namespace {

using ::gutil::StatusIs;
using ::testing::HasSubstr;
using ::testing::MockFunction;

constexpr char kSwitch[] = "switch";
constexpr absl::Duration kDefaultTimeout = absl::Seconds(5);

class EmptySwitch : public thinkit::Switch {
 public:
  const std::string& ChassisName() override { return empty_string_; }
  uint32_t DeviceId() override { return 0; }

 private:
  std::string empty_string_;
};

TEST(ValidatorLib, UnimplementedGrpcIsConsideredPassing) {
  EmptySwitch empty_switch;
  EXPECT_OK(P4rtAble(empty_switch));
  EXPECT_OK(GnmiAble(empty_switch));
  EXPECT_OK(GnoiAble(empty_switch));
}

TEST(PingableTest, SwitchPingable) {
  EXPECT_OK(Pingable(kSwitch, kDefaultTimeout, /*run_ping_command=*/
                     [](const std::string& ping_command)
                         -> absl::StatusOr<std::string> { return "4/4/0%"; }));
}

TEST(PingableTest, SwitchUnpingable) {
  EXPECT_THAT(
      Pingable(kSwitch, kDefaultTimeout, /*run_ping_command=*/
               [](const std::string& ping_command)
                   -> absl::StatusOr<std::string> { return "4/0/100%"; }),
      StatusIs(absl::StatusCode::kUnavailable,
               HasSubstr("switch is not Pingable.")));
}

TEST(PingableTest, SwitchUnstable) {
  EXPECT_THAT(
      Pingable(kSwitch, kDefaultTimeout, /*run_ping_command=*/
               [](const std::string& ping_command)
                   -> absl::StatusOr<std::string> { return "4/2/50%"; }),
      StatusIs(absl::StatusCode::kDeadlineExceeded,
               HasSubstr("switch Pingable state is not stable.")));
}

TEST(PingableTest, SwitchAddressNotFound) {
  EXPECT_THAT(
      Pingable(
          kSwitch, kDefaultTimeout, /*run_ping_command=*/
          [](const std::string& ping_command) -> absl::StatusOr<std::string> {
            return "address not found";
          }),
      StatusIs(absl::StatusCode::kNotFound,
               HasSubstr("switch address not found.")));
}

TEST(PingableTest, SwitchV4PingableV6Unpingable) {
  EXPECT_OK(Pingable(
      kSwitch, kDefaultTimeout, /*run_ping_command=*/
      [](const std::string& ping_command) -> absl::StatusOr<std::string> {
        if (absl::StrContains(ping_command, "fping6")) {
          return "4/0/100%";
        } else {
          return "4/4/0%";
        }
      }));
}

TEST(PingableTest, SwitchV4PingableV6AddressNotFound) {
  EXPECT_OK(Pingable(
      kSwitch, kDefaultTimeout, /*run_ping_command=*/
      [](const std::string& ping_command) -> absl::StatusOr<std::string> {
        if (absl::StrContains(ping_command, "fping6")) {
          return "address not found";
        } else {
          return "4/4/0%";
        }
      }));
}

TEST(PingableTest, SwitchV4PingableV6Unstable) {
  EXPECT_OK(Pingable(
      kSwitch, kDefaultTimeout, /*run_ping_command=*/
      [](const std::string& ping_command) -> absl::StatusOr<std::string> {
        if (absl::StrContains(ping_command, "fping6")) {
          return "4/2/50%";
        } else {
          return "4/4/0%";
        }
      }));
}

TEST(PingableTest, SwitchV4UnpingableV6AddressNotFound) {
  EXPECT_THAT(
      Pingable(
          kSwitch, kDefaultTimeout, /*run_ping_command=*/
          [](const std::string& ping_command) -> absl::StatusOr<std::string> {
            if (absl::StrContains(ping_command, "fping6")) {
              return "address not found";
            } else {
              return "4/0/100%";
            }
          }),
      StatusIs(absl::StatusCode::kUnavailable,
               HasSubstr("switch is not Pingable.")));
}

TEST(PingableTest, SwitchV4UnpingableV6Unstable) {
  EXPECT_THAT(
      Pingable(
          kSwitch, kDefaultTimeout, /*run_ping_command=*/
          [](const std::string& ping_command) -> absl::StatusOr<std::string> {
            if (absl::StrContains(ping_command, "fping6")) {
              return "4/2/50%";
            } else {
              return "4/0/100%";
            }
          }),
      StatusIs(absl::StatusCode::kDeadlineExceeded,
               HasSubstr("switch Pingable state is not stable.")));
}

TEST(PingableTest, SwitchV4UnstableV6AddressNotFound) {
  EXPECT_THAT(
      Pingable(
          kSwitch, kDefaultTimeout, /*run_ping_command=*/
          [](const std::string& ping_command) -> absl::StatusOr<std::string> {
            if (absl::StrContains(ping_command, "fping6")) {
              return "address not found";
            } else {
              return "4/2/50%";
            }
          }),
      StatusIs(absl::StatusCode::kDeadlineExceeded,
               HasSubstr("switch Pingable state is not stable.")));
}

TEST(PingableTest, SwitchV4UnpingableV6Pingable) {
  EXPECT_OK(Pingable(
      kSwitch, kDefaultTimeout, /*run_ping_command=*/
      [](const std::string& ping_command) -> absl::StatusOr<std::string> {
        if (absl::StrContains(ping_command, "fping6")) {
          return "4/4/0%";
        } else {
          return "4/0/100%";
        }
      }));
}

TEST(PingableTest, SwitchV4AddressNotFoundV6Pingable) {
  EXPECT_OK(Pingable(
      kSwitch, kDefaultTimeout, /*run_ping_command=*/
      [](const std::string& ping_command) -> absl::StatusOr<std::string> {
        if (absl::StrContains(ping_command, "fping6")) {
          return "4/4/0%";
        } else {
          return "address not found";
        }
      }));
}

TEST(PingableTest, SwitchV4UnstableV6Pingable) {
  EXPECT_OK(Pingable(
      kSwitch, kDefaultTimeout, /*run_ping_command=*/
      [](const std::string& ping_command) -> absl::StatusOr<std::string> {
        if (absl::StrContains(ping_command, "fping6")) {
          return "4/4/0%";
        } else {
          return "4/2/50%";
        }
      }));
}

TEST(PingableTest, SwitchV4AddressNotFoundV6Unpingable) {
  EXPECT_THAT(
      Pingable(
          kSwitch, kDefaultTimeout, /*run_ping_command=*/
          [](const std::string& ping_command) -> absl::StatusOr<std::string> {
            if (absl::StrContains(ping_command, "fping6")) {
              return "4/0/100%";
            } else {
              return "address not found";
            }
          }),
      StatusIs(absl::StatusCode::kUnavailable,
               HasSubstr("switch is not Pingable.")));
}

TEST(PingableTest, SwitchV4UnstableV6Unpingable) {
  EXPECT_THAT(
      Pingable(
          kSwitch, kDefaultTimeout, /*run_ping_command=*/
          [](const std::string& ping_command) -> absl::StatusOr<std::string> {
            if (absl::StrContains(ping_command, "fping6")) {
              return "4/0/100%";
            } else {
              return "4/2/50%";
            }
          }),
      StatusIs(absl::StatusCode::kDeadlineExceeded,
               HasSubstr("switch Pingable state is not stable.")));
}

TEST(PingableTest, SwitchV4AddressNotFoundV6Unstable) {
  EXPECT_THAT(
      Pingable(
          kSwitch, kDefaultTimeout, /*run_ping_command=*/
          [](const std::string& ping_command) -> absl::StatusOr<std::string> {
            if (absl::StrContains(ping_command, "fping6")) {
              return "4/2/50%";
            } else {
              return "address not found";
            }
          }),
      StatusIs(absl::StatusCode::kDeadlineExceeded,
               HasSubstr("switch Pingable state is not stable.")));
}

TEST(WaitForConditionTest, SucceedsInOneTry) {
  int call_count = 0;
  auto succeed = [&call_count] {
    ++call_count;
    return absl::OkStatus();
  };
  EXPECT_OK(WaitForCondition(succeed, absl::Milliseconds(1)));
  EXPECT_EQ(call_count, 1);
}

TEST(WaitForConditionTest, RunsAtLeastOnce) {
  auto succeed = [] { return absl::OkStatus(); };
  EXPECT_OK(WaitForCondition(succeed, absl::ZeroDuration()));
}

TEST(WaitForConditionTest, SucceedsOnNthTry) {
  int call_count = 0;
  auto past_deadline = [&call_count] {
    if (++call_count >= 5) return absl::OkStatus();
    return absl::InternalError("Failed");
  };
  EXPECT_OK(WaitForCondition(past_deadline, absl::Milliseconds(100)));
  EXPECT_EQ(call_count, 5);
}

TEST(WaitForConditionTest, FailsAfterDeadline) {
  auto fail = [] { return absl::InternalError("Failed"); };
  constexpr absl::Duration kTimeout = absl::Milliseconds(10);

  absl::Time start = absl::Now();
  EXPECT_THAT(WaitForCondition(fail, kTimeout),
              gutil::StatusIs(absl::StatusCode::kDeadlineExceeded,
                              testing::HasSubstr("Failed")));
  EXPECT_GT(absl::Now() - start, kTimeout);
}

TEST(WaitForConditionTest, PassesParametersToCondition) {
  auto ok_if = [](bool condition) {
    return condition ? absl::OkStatus() : absl::InternalError("Failed");
  };
  EXPECT_OK(WaitForCondition(ok_if, absl::ZeroDuration(), true));
  EXPECT_FALSE(WaitForCondition(ok_if, absl::ZeroDuration(), false).ok());
}

TEST(WaitForConditionTest, WorksWithNonTimeoutCondition) {
  auto ok_if = [](bool condition) {
    return condition ? absl::OkStatus() : absl::InternalError("Failed");
  };
  EXPECT_OK(WaitForCondition(ok_if, absl::ZeroDuration(), true));
  EXPECT_FALSE(WaitForCondition(ok_if, absl::ZeroDuration(), false).ok());
}

MATCHER(IsStrictlyDescending, "") {
  for (int i = 1; i < arg.size(); ++i) {
    if (arg.at(i) >= arg.at(i - 1)) {
      return false;
    }
  }
  return true;
}

TEST(WaitForConditionTest, PassesTimeoutToCondition) {
  std::vector<absl::Duration> timeouts;
  auto record_timeout = [&timeouts](absl::Duration timeout) {
    timeouts.push_back(timeout);
    return absl::InternalError("Failed");
  };
  EXPECT_FALSE(WaitForCondition(record_timeout, absl::Milliseconds(10)).ok());
  EXPECT_GT(timeouts.size(), 1);
  EXPECT_THAT(timeouts, IsStrictlyDescending());
}

TEST(WaitForConditionTest, NotWorks) {
  int call_count = 0;
  auto succeed = [&call_count](absl::string_view) {
    ++call_count;
    return call_count < 5 ? absl::OkStatus() : absl::InternalError("Failed");
  };
  EXPECT_OK(WaitForNot(succeed, absl::Milliseconds(50), ""));
  EXPECT_EQ(call_count, 5);
}

TEST(WaitForConditionTest, ReturnsMoreUsefulMessageAfterTimeout) {
  int call_count = 0;
  auto timeout_after_one_call = [&call_count](absl::Duration timeout) {
    if (call_count > 0) {
      absl::SleepFor(timeout);
      return absl::DeadlineExceededError("Useless Message");
    }
    ++call_count;
    return absl::InvalidArgumentError("A Useful Message");
  };
  EXPECT_THAT(WaitForCondition(timeout_after_one_call, absl::Milliseconds(10)),
              gutil::StatusIs(absl::StatusCode::kDeadlineExceeded,
                              testing::HasSubstr("A Useful Message")));
}

TEST(OnFailureTest, DoesntRunOnSuccess) {
  MockFunction<void()> mock_function;
  EXPECT_CALL(mock_function, Call()).Times(0);
  EXPECT_OK(OnFailure(absl::OkStatus(), mock_function.AsStdFunction()));
}

TEST(OnFailureTest, RunsOnFailure) {
  MockFunction<void()> mock_function;
  EXPECT_CALL(mock_function, Call()).Times(1);
  EXPECT_THAT(
      OnFailure(absl::InternalError("Failed"), mock_function.AsStdFunction()),
      StatusIs(absl::StatusCode::kInternal));
}

}  // namespace
}  // namespace pins_test
