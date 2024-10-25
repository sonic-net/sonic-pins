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

#include "dvaas/mirror_testbed_config.h"

#include "absl/status/status.h"
#include "gutil/status.h"
#include "lib/gnmi/gnmi_helper.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "tests/lib/switch_test_setup_helpers.h"
#include "thinkit/mirror_testbed_fixture.h"

namespace dvaas {

absl::StatusOr<MirrorTestbedConfigurator> MirrorTestbedConfigurator::Create(
    std::shared_ptr<thinkit::MirrorTestbedInterface> testbed_interface) {
  MirrorTestbedConfigurator configured_testbed(testbed_interface);

  thinkit::MirrorTestbed& testbed = testbed_interface->GetMirrorTestbed();

  ASSIGN_OR_RETURN(configured_testbed.sut_api_.p4rt,
                   pdpi::P4RuntimeSession::Create(testbed.Sut()));
  ASSIGN_OR_RETURN(configured_testbed.sut_api_.gnmi,
                   testbed.Sut().CreateGnmiStub());
  ASSIGN_OR_RETURN(configured_testbed.control_switch_api_.p4rt,
                   pdpi::P4RuntimeSession::Create(testbed.ControlSwitch()));
  ASSIGN_OR_RETURN(configured_testbed.control_switch_api_.gnmi,
                   testbed.ControlSwitch().CreateGnmiStub());

  return configured_testbed;
}

absl::Status MirrorTestbedConfigurator::ConfigureForForwardingTest() {
  // The testbed must not have been configured before.
  if (original_control_interfaces_.has_value()) {
    return absl::FailedPreconditionError(
        "Configure function called on an already configured testbed.");
  }

  // Store the original control switch gNMI interface config before changing
  // it.
  ASSIGN_OR_RETURN(original_control_interfaces_,
                   pins_test::GetInterfacesAsProto(*control_switch_api_.gnmi,
                                                   gnmi::GetRequest::CONFIG));

  thinkit::MirrorTestbed& testbed = testbed_interface_->GetMirrorTestbed();

  // Set up control switch to be a mirror of SUT.
  RETURN_IF_ERROR(pdpi::ClearTableEntries(control_switch_api_.p4rt.get()));
  // Mirror testbed ports.
  RETURN_IF_ERROR(pins_test::MirrorSutP4rtPortIdConfigToControlSwitch(testbed));

  // Ensure that all enabled ports are up.
  RETURN_IF_ERROR(pins_test::WaitForEnabledInterfacesToBeUp(testbed.Sut()))
          .SetPrepend()
      << "expected enabled interfaces on SUT to be up: ";
  RETURN_IF_ERROR(
      pins_test::WaitForEnabledInterfacesToBeUp(testbed.ControlSwitch()))
          .SetPrepend()
      << "expected enabled interfaces on control switch to be up: ";

  return absl::OkStatus();
}

absl::Status MirrorTestbedConfigurator::RestoreToOriginalConfiguration() {
  // The testbed must have been configured before.
  if (!original_control_interfaces_.has_value()) {
    return absl::FailedPreconditionError(
        "The testbed has not been configured for forwarding test before.");
  }

  // Restore the original control switch gNMI interface config's P4RT IDs.
  RETURN_IF_ERROR(pins_test::SetInterfaceP4rtIds(
      *control_switch_api_.gnmi, *original_control_interfaces_));

  // Remove the kept interfaces.
  original_control_interfaces_.reset();

  return absl::OkStatus();
}

}  // namespace dvaas
