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
#include <optional>

#include "absl/container/btree_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "dvaas/port_id_map.h"
#include "dvaas/switch_api.h"
#include "lib/gnmi/openconfig.pb.h"
#include "lib/p4rt/p4rt_port.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "thinkit/mirror_testbed.h"
#include "thinkit/mirror_testbed_fixture.h"

namespace dvaas {

// Can be used to change the configuration of the switches in a given testbed to
// prepare them for forwarding related tests (e.g. Arriba, DVaaS, Ouroboros) and
// restoring the testbed to its original configuration after the test.
class MirrorTestbedConfigurator {
 public:
  struct Params {
    // If not nullopt, configures the interfaces on SUT to make sure for any
    // P4RT port id in `used_p4rt_port_ids`, there is exactly one enabled
    // ethernet interface with that id. Existing SUT table entries get wiped out
    // during the process.
    std::optional<absl::btree_set<pins_test::P4rtPortId>>
        p4rt_port_ids_to_configure = std::nullopt;

    // If true, sets up control switch ports to be a mirror of SUT
    // Must be true if `used_p4rt_port_ids` is non-nullopt. Existing control
    // switch table entries get wiped out during the process.
    bool mirror_sut_ports_ids_to_control_switch = false;

    // Optionally, can be used to override the default assumption that each SUT
    // port is connected to a control switch port with the same OpenConfig
    // interface name.
    // NOTE: Not required for valid mirror testbeds. This is a workaround for
    // non-standard testbeds only.
    std::optional<MirrorTestbedP4rtPortIdMap> original_port_map;

    // If true, wait for all enabled ports to be up on SUT and control switch.
    bool wait_for_all_enabled_interfaces_to_be_up = true;
  };

  // Creates and returns MirrorTestbedConfigurator object from the given
  // testbed. Establishes connections to SUT and control switch.
  // Note: The returned configurator object does not take ownership of the given
  // testbed, and the caller is responsible for ensuring it outlives the created
  // configurator.
  static absl::StatusOr<MirrorTestbedConfigurator> Create(
      thinkit::MirrorTestbed* testbed);

  // Prepares the testbed for forwarding related tests by:
  //    - Configuring the SUT and control switch according to the `params`.
  //    - Ensuring that all enabled ports are up.
  //    - Keeping the original config for later restoration.
  //
  // Pre-condition: The control switch must be in its original config (i.e.
  // original_control_interfaces_ must be empty), otherwise an error will be
  // returned.
  absl::Status ConfigureForForwardingTest(const Params& params);

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

  // The port mapping of the testbed after `ConfigureForForwardingTest` is
  // called successfully. Returns an error if the testbed is not configured.
  absl::StatusOr<MirrorTestbedP4rtPortIdMap> GetConfiguredPortMap();

  // Movable only. Can only be created through `Create`.
  MirrorTestbedConfigurator(MirrorTestbedConfigurator &&) = default;
  MirrorTestbedConfigurator &operator=(MirrorTestbedConfigurator &&) = default;
  MirrorTestbedConfigurator(const MirrorTestbedConfigurator &) = delete;
  MirrorTestbedConfigurator &
  operator=(const MirrorTestbedConfigurator &) = delete;

private:
  // May only be called by `Create`.
  MirrorTestbedConfigurator(thinkit::MirrorTestbed* testbed)
      : testbed_(*testbed) {}

  // The testbed to be configured.
  thinkit::MirrorTestbed& testbed_;

  // APIs to SUT and control switch.
  // Invariant: Pointers in both SwitchApis are not null.
  SwitchApi sut_api_;
  SwitchApi control_switch_api_;

  // Keeps the original interfaces configured on the SUT and control switch
  // before call to `ConfigureForForwardingTest`. Successful call to
  // `ConfigureForForwardingTest` sets their value. Successful call to
  // `RestoreToOriginalConfiguration` resets them to nullopt.
  std::optional<pins_test::openconfig::Interfaces> original_sut_interfaces_;
  std::optional<pins_test::openconfig::Interfaces> original_control_interfaces_;

  // The port mapping of the testbed after configuration. Successful call to
  // `ConfigureForForwardingTest` with a non-nullopt `params.original_port_map`
  // set its value. Successful call to `RestoreToOriginalConfiguration` resets
  // its value.
  std::optional<MirrorTestbedP4rtPortIdMap> configured_port_map_;
};

} // namespace dvaas

#endif // PINS_DVAAS_MIRROR_TESTBED_CONFIG_H_
