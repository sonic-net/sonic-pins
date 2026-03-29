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

// thinkit::MirrorTestbed backed by two 4ward P4RuntimeServer instances,
// in-process fake gNMI servers, and a PacketBridge connecting them.

#ifndef PINS_FOURWARD_FOURWARD_MIRROR_TESTBED_H_
#define PINS_FOURWARD_FOURWARD_MIRROR_TESTBED_H_

#include <cstdint>
#include <memory>
#include <string>
#include <utility>

#include "absl/status/statusor.h"
#include "fourward/fake_gnmi_service.h"
#include "fourward/fourward_switch.h"
#include "fourward/packet_bridge.h"
#include "github.com/openconfig/gnmi/proto/gnmi/gnmi.grpc.pb.h"
#include "grpcpp/create_channel.h"
#include "grpcpp/security/credentials.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "thinkit/bazel_test_environment.h"
#include "thinkit/mirror_testbed.h"

namespace dvaas {

// A thinkit::MirrorTestbed with two 4ward P4RuntimeServer instances,
// in-process fake gNMI servers, and a PacketBridge connecting them.
class FourwardMirrorTestbed : public thinkit::MirrorTestbed {
 public:
  // Creates a testbed with two 4ward servers, two fake gNMI servers,
  // and a PacketBridge between them.
  static absl::StatusOr<std::unique_ptr<FourwardMirrorTestbed>> Create(
      uint32_t sut_device_id = 1, uint32_t control_device_id = 2);

  thinkit::Switch& Sut() override { return sut_adapter_; }
  thinkit::Switch& ControlSwitch() override { return control_adapter_; }
  thinkit::TestEnvironment& Environment() override { return env_; }

  PacketBridge& Bridge() { return *bridge_; }

 private:
  // Thin adapter that adds gNMI support to FourwardSwitch by connecting
  // to a FakeGnmiServer.
  class SwitchWithGnmi : public thinkit::Switch {
   public:
    SwitchWithGnmi(FourwardSwitch fourward_switch,
                   std::string gnmi_address)
        : switch_(std::move(fourward_switch)),
          gnmi_address_(std::move(gnmi_address)) {}

    const std::string& ChassisName() override { return switch_.ChassisName(); }
    uint32_t DeviceId() override { return switch_.DeviceId(); }

    absl::StatusOr<std::unique_ptr<p4::v1::P4Runtime::StubInterface>>
    CreateP4RuntimeStub() override {
      return switch_.CreateP4RuntimeStub();
    }

    absl::StatusOr<std::unique_ptr<gnmi::gNMI::StubInterface>>
    CreateGnmiStub() override {
      std::shared_ptr<grpc::Channel> channel = grpc::CreateChannel(
          gnmi_address_, grpc::InsecureChannelCredentials());
      return gnmi::gNMI::NewStub(channel);
    }

   private:
    FourwardSwitch switch_;
    std::string gnmi_address_;
  };

  FourwardMirrorTestbed(SwitchWithGnmi sut, SwitchWithGnmi control,
                        std::unique_ptr<FakeGnmiServer> sut_gnmi,
                        std::unique_ptr<FakeGnmiServer> control_gnmi,
                        std::unique_ptr<PacketBridge> bridge)
      : sut_adapter_(std::move(sut)),
        control_adapter_(std::move(control)),
        sut_gnmi_(std::move(sut_gnmi)),
        control_gnmi_(std::move(control_gnmi)),
        bridge_(std::move(bridge)),
        env_(/*mask_known_failures=*/false) {}

  SwitchWithGnmi sut_adapter_;
  SwitchWithGnmi control_adapter_;
  std::unique_ptr<FakeGnmiServer> sut_gnmi_;
  std::unique_ptr<FakeGnmiServer> control_gnmi_;
  std::unique_ptr<PacketBridge> bridge_;
  thinkit::BazelTestEnvironment env_;
};

}  // namespace dvaas

#endif  // PINS_FOURWARD_FOURWARD_MIRROR_TESTBED_H_
