// Copyright (c) 2020, Google Inc.
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

#ifndef THINKIT_MIRROR_TESTBED_H_
#define THINKIT_MIRROR_TESTBED_H_

#include <string>
#include <vector>

#include "thinkit/switch.h"
#include "thinkit/test_environment.h"

namespace thinkit {

// The MirrorTestbed interface represents a testbed topology with two
// P4RT-capable switches connected back-to-back.
class MirrorTestbed {
 public:
  virtual ~MirrorTestbed() {}

  // Returns the control switch (switch connected to the SUT (system under
  // test)).
  virtual Switch& ControlSwitch() = 0;

  // Returns the SUT (system under test) switch.
  virtual Switch& Sut() = 0;

  // Returns the SUT (or Control Switch) interfaces that are connected to
  // Control Switch (or SUT) and have the same name as the peer
  // interface that they are connected to (e.g. Ethernet0).
  //
  // Note: The default implementation returns an empty list. Typically the list
  // of interfaces returned from this method is used by libraries (eg.
  // gnmi_helper) that consider an "empty list" as "all interfaces", so this is
  // a decent default behaviour.
  virtual std::vector<std::string> GetConnectedInterfaces() { return {}; };

  // Returns the test environment.
  virtual TestEnvironment& Environment() = 0;
};

}  // namespace thinkit

#endif  // THINKIT_MIRROR_TESTBED_H_
