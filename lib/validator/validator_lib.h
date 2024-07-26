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

#include "absl/status/status.h"
#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

namespace pins_test {

constexpr absl::Duration kDefaultTimeout = absl::Seconds(60);

// Checks if the switch can be pinged.
absl::Status Pingable(absl::string_view chassis_name,
                      absl::Duration timeout = kDefaultTimeout);

absl::Status Pingable(thinkit::Switch& thinkit_switch,
                      absl::Duration timeout = kDefaultTimeout);

// Checks if ssh access to the switch is working.
absl::Status SSHable(absl::string_view chassis_name,
                     thinkit::SSHClient& ssh_client,
                     absl::Duration timeout = kDefaultTimeout);

absl::Status SSHable(thinkit::Switch& thinkit_switch,
                     thinkit::SSHClient& ssh_client,
                     absl::Duration timeout = kDefaultTimeout);

// Checks if a P4Runtime session could be established.
absl::Status P4rtAble(thinkit::Switch& thinkit_switch);

// Checks if a gNMI get all interface request can be sent and a response
// received.
absl::Status GnmiAble(thinkit::Switch& thinkit_switch,
                      absl::Duration timeout = kDefaultTimeout);

// Checks if a gNOI system get time request can be sent and a response
// received.
absl::Status GnoiAble(thinkit::Switch& thinkit_switch,
                      absl::Duration timeout = kDefaultTimeout);

// Checks if "oper-status" of all interfaces are "UP". If the interfaces is
// provided, checks only those interfaces.
absl::Status PortsUp(thinkit::Switch& thinkit_switch,
                     absl::Span<const std::string> interfaces = {},
                     absl::Duration timeout = kDefaultTimeout);

// Checks to make sure no alarms are set.
absl::Status NoAlarms(thinkit::Switch& thinkit_switch,
                      absl::Duration timeout = kDefaultTimeout);

// Checks if the switch is ready by running the following validations:
// Pingable, P4rtAble, GnmiAble, GnoiAble, PortsUp.
absl::Status SwitchReady(thinkit::Switch& thinkit_switch,
                         absl::Span<const std::string> interfaces = {},
                         absl::Duration timeout = kDefaultTimeout);

// Checks if the switch is ready by running the following validations:
// Pingable, SSHable, P4rtAble, GnmiAble, GnoiAble, PortsUp.
absl::Status SwitchReadyWithSsh(thinkit::Switch& thinkit_switch,
                                thinkit::SSHClient& ssh_client,
                                absl::Span<const std::string> interfaces = {},
                                absl::Duration timeout = kDefaultTimeout);

}  // namespace pins_test

#endif  // PINS_LIB_VALIDATOR_VALIDATOR_LIB_H_
