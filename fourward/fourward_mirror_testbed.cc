// Copyright 2026 Google LLC
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

#include "fourward/fourward_mirror_testbed.h"

#include <cstdint>
#include <memory>
#include <string>
#include <utility>

#include "absl/status/statusor.h"
#include "fourward/fake_gnmi_service.h"
#include "fourward/fourward_switch.h"
#include "fourward/packet_bridge.h"
#include "gutil/status.h"

namespace dvaas {

absl::StatusOr<std::unique_ptr<FourwardMirrorTestbed>>
FourwardMirrorTestbed::Create(uint32_t sut_device_id,
                              uint32_t control_device_id) {
  ASSIGN_OR_RETURN(FourwardSwitch sut_switch,
                   FourwardSwitch::Create(sut_device_id));
  ASSIGN_OR_RETURN(FourwardSwitch control_switch,
                   FourwardSwitch::Create(control_device_id));
  ASSIGN_OR_RETURN(std::unique_ptr<FakeGnmiServer> sut_gnmi,
                   FakeGnmiServer::Create());
  ASSIGN_OR_RETURN(std::unique_ptr<FakeGnmiServer> control_gnmi,
                   FakeGnmiServer::Create());

  std::string sut_address = sut_switch.ChassisName();
  std::string control_address = control_switch.ChassisName();

  SwitchWithGnmi sut_adapter(std::move(sut_switch), sut_gnmi->Address());
  SwitchWithGnmi control_adapter(std::move(control_switch),
                                 control_gnmi->Address());

  std::unique_ptr<PacketBridge> bridge =
      std::make_unique<PacketBridge>(sut_address, control_address);

  // Can't use make_unique due to private constructor.
  return std::unique_ptr<FourwardMirrorTestbed>(new FourwardMirrorTestbed(
      std::move(sut_adapter), std::move(control_adapter),
      std::move(sut_gnmi), std::move(control_gnmi), std::move(bridge)));
}

}  // namespace dvaas
