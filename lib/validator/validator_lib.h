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

#ifndef PINS_LIB_VALIDATOR_VALIDATOR_LIB_H_
#define PINS_LIB_VALIDATOR_VALIDATOR_LIB_H_

#include <cstdint>
#include <functional>
#include <list>
#include <string>
#include <utility>

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/str_join.h"
#include "absl/strings/string_view.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "absl/types/span.h"
#include "lib/ssh/ssh_wrapper_client.h"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

namespace pins_test {
namespace internal {
absl::StatusOr<std::string> RunPingCommand(const std::string &ping_command);
} // namespace internal

constexpr absl::Duration kDefaultTimeout = absl::Seconds(60);

// Checks if the switch can be pinged.
// Will wait up to `timeout` for the switch to respond to the ping.
absl::Status
Pingable(absl::string_view chassis_name,
         absl::Duration timeout = kDefaultTimeout,
         std::function<absl::StatusOr<std::string>(const std::string &)>
             run_ping_command = internal::RunPingCommand);

absl::Status Pingable(thinkit::Switch &thinkit_switch,
                      absl::Duration timeout = kDefaultTimeout);

// Checks if ssh access to the switch is working.
// Will wait up to `timeout` for the switch to respond to SSH.
absl::Status SSHable(absl::string_view chassis_name,
                     thinkit::SSHClient &ssh_client,
                     absl::Duration timeout = kDefaultTimeout);

absl::Status SSHable(thinkit::Switch &thinkit_switch,
                     thinkit::SSHClient &ssh_client,
                     absl::Duration timeout = kDefaultTimeout);

// Checks if a P4Runtime session could be established.
// Will wait up to `timeout` for the RPC to return. Performs one request.
absl::Status P4rtAble(thinkit::Switch &thinkit_switch,
                      absl::Duration timeout = kDefaultTimeout);

// Checks if a gNMI get all interface request can be sent and a response
// received.
// Will wait up to `timeout` for the RPC to return. Peforms one request.
absl::Status GnmiAble(thinkit::Switch &thinkit_switch,
                      absl::Duration timeout = kDefaultTimeout);

// Checks if a gNOI system get time request can be sent and a response
// received.
// Will wait up to `timeout` for the RPC to return. Peforms one request.
absl::Status GnoiAble(thinkit::Switch &thinkit_switch,
                      absl::Duration timeout = kDefaultTimeout);

// Checks if "oper-status" of all interfaces are "UP". If the interfaces are
// provided, checks only those interfaces.
// Will wait up to `timeout` for the RPC to return. Performs one request.
absl::Status PortsUp(thinkit::Switch &thinkit_switch,
                     absl::Span<const std::string> interfaces = {},
                     bool with_healthz = true,
                     absl::Duration timeout = kDefaultTimeout);

// Checks if "oper-status" of all interfaces are "DOWN". If the interfaces are
// provided, checks only those interfaces.
// Will wait up to `timeout` for the RPC to return. Performs one request.
absl::Status PortsDown(thinkit::Switch &thinkit_switch,
                       absl::Span<const std::string> interfaces = {},
                       bool with_healthz = true,
                       absl::Duration timeout = kDefaultTimeout);

// Checks if "oper-status" of all interfaces are "NOT_PRESENT". If the
// interfaces are provided, checks only those interfaces.
// Will wait up to `timeout` for the RPC to return. Performs one request.
absl::Status PortsNotPresent(thinkit::Switch &thinkit_switch,
                             absl::Span<const std::string> interfaces = {},
                             bool with_healthz = true,
                             absl::Duration timeout = kDefaultTimeout);

inline absl::Status AllPortsUp(thinkit::Switch &thinkit_switch,
                               bool with_healthz = true,
                               absl::Duration timeout = kDefaultTimeout) {
  return PortsUp(thinkit_switch,
                 /*interfaces=*/{}, with_healthz, timeout);
}

// Checks to make sure no alarms are set.
// Will wait up to `timeout` for the RPC to return. Performs one request.
absl::Status NoAlarms(thinkit::Switch& thinkit_switch,
                      absl::Duration timeout = kDefaultTimeout);

// Checks if switch is SSHable, gNXI/P4RT are responding, and containers are up.
absl::Status SwitchUp(thinkit::Switch& thinkit_switch,
                      thinkit::SSHClient& ssh_client,
                      thinkit::SshWrapperClient& ssh_wrapper_client,
                      absl::Duration timeout);

// Checks if the switch is ready by running the following validations:
// Pingable, P4rtAble, GnmiAble, GnoiAble.
absl::Status SwitchReady(thinkit::Switch &thinkit_switch,
                         absl::Span<const std::string> interfaces = {},
                         absl::Duration timeout = kDefaultTimeout);

// Checks if the switch is ready by running the following validations:
// Pingable, SSHable, P4rtAble, GnmiAble, GnoiAble, [PortsUp].
absl::Status SwitchReadyWithSsh(thinkit::Switch &thinkit_switch,
                                thinkit::SSHClient &ssh_client,
                                absl::Span<const std::string> interfaces = {},
                                bool check_interfaces_state = true,
                                bool with_healthz = true,
                                absl::Duration timeout = kDefaultTimeout);

// Runs an additional routine if the status is a failure. This function
// transparently forwards the status.
absl::Status OnFailure(absl::Status status,
                       const std::function<void()> &on_failure);

// Waits for the expected condition to return success. The condition will be
// checked until either the timeout is expired (in which case an error status is
// returned) or the condition returns ok.
//
// Examples:
//   std::vector<std::string> interfaces = ...;
//   ASSERT_OK(WaitForCondition(SwitchReady, absl::Minutes(5), interfaces));
//
//   ASSERT_OK(WaitForCondition(P4rtAble, absl::Seconds(10)));
template <typename Func, typename... Args>
absl::Status WaitForCondition(Func &&condition, absl::Duration timeout,
                              Args &&...args) {
  absl::Time deadline = absl::Now() + timeout;
  constexpr int kMaxResults = 2;
  absl::Status final_status = absl::OkStatus();
  uint64_t number_of_function_invocations = 0;
  std::list<std::string> latest_results;
  do {
    number_of_function_invocations++;
    if constexpr (std::is_invocable_r_v<absl::Status, Func, Args...,
                                        absl::Duration>) {
      final_status = std::invoke(condition, std::forward<Args>(args)...,
                                 /*timeout=*/deadline - absl::Now());
    } else {
      final_status = std::invoke(condition, std::forward<Args>(args)...);
    }
    latest_results.push_back(absl::StrCat(absl::FormatTime(absl::Now()), ": ",
                                          final_status.message()));
    if (latest_results.size() > kMaxResults)
      latest_results.pop_front();
  } while (!final_status.ok() && absl::Now() < deadline);
  if (final_status.ok())
    return final_status;

  return absl::DeadlineExceededError(absl::StrCat(
      "Failed to reach the requested condition after ",
      absl::FormatDuration(timeout), " with ", number_of_function_invocations,
      " function invocations. Latest results:\n",
      absl::StrJoin(latest_results, "\n")));
}

// Waits for the expected condition to return an error. The inverse of
// WaitForCondition.
template <typename Func, typename... Args>
absl::Status WaitForNot(Func &&condition, absl::Duration timeout,
                        Args &&...args) {
  absl::Time deadline = absl::Now() + timeout;
  absl::Status final_status;
  uint64_t number_of_function_invocations = 0;
  do {
    number_of_function_invocations++;
    if constexpr (std::is_invocable_r_v<absl::Status, Func, Args...,
                                        absl::Duration>) {
      final_status = std::invoke(condition, std::forward<Args>(args)...,
                                 /*timeout=*/deadline - absl::Now());
    } else {
      final_status = std::invoke(condition, std::forward<Args>(args)...);
    }
  } while (final_status.ok() && absl::Now() < deadline);
  if (!final_status.ok()) {
    // deadline - absl::Now() is the remaining time left in the timeout, so
    // timeout - (deadline - absl::Now()) is the time it took to reach the not
    // ok condition.
    LOG(INFO) << "Condition became not ok after "
              << timeout - (deadline - absl::Now()) << " with "
              << number_of_function_invocations << " function invocations:\n"
              << final_status;
    return absl::OkStatus();
  }

  return absl::DeadlineExceededError(absl::StrCat(
      "Condition still ok after ", absl::FormatDuration(timeout), " with ",
      number_of_function_invocations, " function invocations."));
}

} // namespace pins_test

#endif // PINS_LIB_VALIDATOR_VALIDATOR_LIB_H_
