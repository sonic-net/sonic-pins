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

#ifndef PINS_DVAAS_MIRROR_TESTBED_CONFIG_H_
#define PINS_DVAAS_MIRROR_TESTBED_CONFIG_H_

#include <memory>

#include "absl/status/status.h"
#include "dvaas/switch_api.h"
#include "lib/gnmi/openconfig.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "thinkit/mirror_testbed_fixture.h"

namespace dvaas {

// Can be used to change the configuration of the switches in a given testbed to
// prepare them for forwarding related tests (e.g. Arriba, DVaaS, Ouroboros) and
// restoring the testbed to its original configuration after the test.
class MirrorTestbedConfigurator {
public:
  // Creates and returns MirrorTestbedConfigurator object from the given
  // testbed. Establishes connections to SUT and control switch.
  static absl::StatusOr<MirrorTestbedConfigurator>
  Create(std::shared_ptr<thinkit::MirrorTestbedInterface> testbed_interface);

  // Prepares the testbed for forwarding related tests by:
  //    - Setting up control switch ports to be a mirror of SUT.
  //      TODO: Remove the above functionality after the bug is
  //      resolved.
  //    - Ensure that all enabled ports are up.
  //    - Keeping the original config for later restoration.
  //
  // Pre-condition: The control switch must be in its original config (i.e.
  // original_control_interfaces_ must be empty), otherwise an error will be
  // returned.
  absl::Status ConfigureForForwardingTest();

  // Restores the testbed to the original configuration it had before the call
  // to `ConfigureForForwardingTest`.
  //
  // Pre-condition: `ConfigureForForwardingTest` must already be called with no
  // call to `RestoreToOriginalConfiguration` after that (i.e.
  // original_control_interfaces_ must be non-empty), otherwise an error will be
  // returned.
  absl::Status RestoreToOriginalConfiguration();

  // Returns APIs to SUT.
  // Invariant: All pointers in the returned SwitchApi are non-empty.
  SwitchApi &SutApi() { return sut_api_; }
  // Returns APIs to control switch.
  // Invariant: All pointers in the returned SwitchApi are non-empty.
  SwitchApi &ControlSwitchApi() { return control_switch_api_; }

  // Movable only. Can only be created through `Create`.
  MirrorTestbedConfigurator(MirrorTestbedConfigurator &&) = default;
  MirrorTestbedConfigurator &operator=(MirrorTestbedConfigurator &&) = default;
  MirrorTestbedConfigurator(const MirrorTestbedConfigurator &) = delete;
  MirrorTestbedConfigurator &
  operator=(const MirrorTestbedConfigurator &) = delete;

private:
  // May only be called by `Create`.
  MirrorTestbedConfigurator(
      std::shared_ptr<thinkit::MirrorTestbedInterface> &testbed_interface)
      : testbed_interface_(testbed_interface) {}

  // The testbed to be configured.
  std::shared_ptr<thinkit::MirrorTestbedInterface> testbed_interface_;

  // APIs to SUT and control switch.
  // Invariant: Pointers in both SwitchApis are not null.
  SwitchApi sut_api_;
  SwitchApi control_switch_api_;

  // Keeps the original interfaces configured on the control switch before call
  // to `ConfigureForForwardingTest`. Successful call to
  // `ConfigureForForwardingTest` sets its value. Successful call to
  // `RestoreToOriginalConfiguration` resets it to nullopt.
  std::optional<pins_test::openconfig::Interfaces> original_control_interfaces_;
};

} // namespace dvaas

#endif // PINS_DVAAS_MIRROR_TESTBED_CONFIG_H_
