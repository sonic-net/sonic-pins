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

// thinkit::MirrorTestbed backed by two FourwardSwitch instances (each owning a
// 4ward P4Runtime server and a fake gNMI server) and a PacketBridge connecting
// them.

#ifndef PINS_FOURWARD_FOURWARD_MIRROR_TESTBED_H_
#define PINS_FOURWARD_FOURWARD_MIRROR_TESTBED_H_

#include <cstdint>
#include <memory>
#include <utility>

#include "absl/status/statusor.h"
#include "fourward/fourward_switch.h"
#include "fourward/packet_bridge.h"
#include "thinkit/bazel_test_environment.h"
#include "thinkit/mirror_testbed.h"

namespace dvaas {

// A thinkit::MirrorTestbed with two FourwardSwitch instances and a
// PacketBridge connecting them.
class FourwardMirrorTestbed : public thinkit::MirrorTestbed {
 public:
  // Creates a testbed with two FourwardSwitch instances (each including a fake
  // gNMI server) and a PacketBridge between them.
  static absl::StatusOr<std::unique_ptr<FourwardMirrorTestbed>> Create(
      uint32_t sut_device_id = 1, uint32_t control_device_id = 2);

  thinkit::Switch& Sut() override { return sut_; }
  thinkit::Switch& ControlSwitch() override { return control_; }
  thinkit::TestEnvironment& Environment() override { return env_; }

  PacketBridge& Bridge() { return *bridge_; }

 private:
  FourwardMirrorTestbed(FourwardSwitch sut, FourwardSwitch control,
                        std::unique_ptr<PacketBridge> bridge)
      : sut_(std::move(sut)),
        control_(std::move(control)),
        bridge_(std::move(bridge)),
        env_(/*mask_known_failures=*/false) {}

  FourwardSwitch sut_;
  FourwardSwitch control_;
  std::unique_ptr<PacketBridge> bridge_;
  thinkit::BazelTestEnvironment env_;
};

}  // namespace dvaas

#endif  // PINS_FOURWARD_FOURWARD_MIRROR_TESTBED_H_
