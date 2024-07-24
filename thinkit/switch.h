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

#ifndef THINKIT_SWITCH_H_
#define THINKIT_SWITCH_H_

#include <cstdint>
#include <memory>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "cert/cert.grpc.pb.h"
#include "diag/diag.grpc.pb.h"
#include "factory_reset/factory_reset.grpc.pb.h"
#include "os/os.grpc.pb.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "system/system.grpc.pb.h"

namespace thinkit {

// The Switch interface represents a P4RT-capable switch that can be connected
// to in a blackbox fashion.
class Switch {
 public:
  virtual ~Switch() {}

  // Returns the chassis name of the switch. This should be a reachable
  // hostname to the switch.
  virtual const std::string& ChassisName() = 0;

  // Returns the P4Runtime device ID of the switch.
  virtual uint32_t DeviceId() = 0;

  // Creates and returns a stub to the P4Runtime service.
  virtual absl::StatusOr<std::unique_ptr<p4::v1::P4Runtime::Stub>>
  CreateP4RuntimeStub() {
    return absl::UnimplementedError(
        absl::StrCat(__func__, " is not implemented."));
  }

  // Creates and returns a stub to the gNMI service.
  virtual absl::StatusOr<std::unique_ptr<gnmi::gNMI::Stub>>
  CreateGnmiStub() {
    return absl::UnimplementedError(
        absl::StrCat(__func__, " is not implemented."));
  }

  // Creates and returns a stub to the gNOI Factory Reset service.
  virtual absl::StatusOr<
      std::unique_ptr<gnoi::factory_reset::FactoryReset::Stub>>
  CreateGnoiFactoryResetStub() {
    return absl::UnimplementedError(
        absl::StrCat(__func__, " is not implemented."));
  }

  // Creates and returns a stub to the gNOI System service.
  virtual absl::StatusOr<std::unique_ptr<gnoi::system::System::Stub>>
  CreateGnoiSystemStub() {
    return absl::UnimplementedError(
        absl::StrCat(__func__, " is not implemented."));
  }

  // Creates and returns a stub to the gNOI Diag service.
  virtual absl::StatusOr<std::unique_ptr<gnoi::diag::Diag::Stub>>
  CreateGnoiDiagStub() {
    return absl::UnimplementedError(
        absl::StrCat(__func__, " is not implemented."));
  }

  // Creates and returns a stub to the gNOI Certificate service.
  virtual absl::StatusOr<
      std::unique_ptr<gnoi::certificate::CertificateManagement::Stub>>
  CreateGnoiCertificateStub() {
    return absl::UnimplementedError(
        absl::StrCat(__func__, " is not implemented."));
  }

  // Creates and returns a stub to the gNOI OS service.
  virtual absl::StatusOr<std::unique_ptr<gnoi::os::OS::Stub>>
  CreateGnoiOsStub() {
    return absl::UnimplementedError(
        absl::StrCat(__func__, " is not implemented."));
  }
};

}  // namespace thinkit

#endif  // THINKIT_SWITCH_H_
