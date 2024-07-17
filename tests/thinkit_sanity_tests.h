// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#ifndef GOOGLE_TESTS_THINKIT_SANITY_TESTS_H_
#define GOOGLE_TESTS_THINKIT_SANITY_TESTS_H_

#include "thinkit/ssh_client.h"
#include "thinkit/switch.h"

namespace pins_test {

// Tests that commands can be run on the switch through SSH.
void TestSSHCommand(thinkit::SSHClient& ssh_client, thinkit::Switch& sut);

// Tests that P4 Sessions can be established with the switch.
void TestP4Session(thinkit::Switch& sut);

}  // namespace pins_test

#endif  // GOOGLE_TESTS_THINKIT_SANITY_TESTS_H_
