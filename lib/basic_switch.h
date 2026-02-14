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

#ifndef PINS_LIB_BASIC_SWITCH_H_
#define PINS_LIB_BASIC_SWITCH_H_

#include <cstdint>
#include <memory>
#include <string>
#include <string_view>
#include <utility>

#include "absl/status/statusor.h"
#include "cert/cert.grpc.pb.h"
#include "diag/diag.grpc.pb.h"
#include "factory_reset/factory_reset.grpc.pb.h"
#include "grpc/grpc_security_constants.h"
#include "grpcpp/security/credentials.h"
#include "grpcpp/support/channel_arguments.h"
#include "grpcpp/support/stub_options.h"
#include "os/os.grpc.pb.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
#include "proto/gnmi/gnmi.grpc.pb.h"
#include "system/system.grpc.pb.h"
#include "thinkit/switch.h"

namespace pins_test {

// SwitchServices contains the addresses of all of the gRPC services that
// interact with the switch interfaces.
struct SwitchServices {
  std::string p4runtime_address;
  std::string gnmi_address;
  std::string gnoi_address;
};

class LocalTcp {
public:
  std::shared_ptr<grpc::ChannelCredentials> Credentials() {
    return grpc::experimental::LocalCredentials(LOCAL_TCP);
  }
};

// A simple stub creation policy that creates a custom channel to the address
// using the `CredentialsPolicy` passed in. This policy has one function
// `std::shared_ptr<grpc::ChannelCredentials> Credentials()`.
template <class CredentialsPolicy>
class CreateGrpcStub : private CredentialsPolicy {
public:
  template <class... Args>
  explicit CreateGrpcStub(Args &&...args)
      : CredentialsPolicy(std::forward<Args>(args)...) {}

  template <class NewStubFunction>
  auto Create(NewStubFunction &&new_stub, const std::string &address,
              std::string_view /*chassis*/, std::string_view /*stub_type*/,
              grpc::ChannelArguments channel_arguments = {}) {
    return new_stub(grpc::CreateCustomChannel(address,
                                              CredentialsPolicy::Credentials(),
                                              channel_arguments),
                    grpc::StubOptions());
  }
};

// BasicSwitch implements ThinKit's Switch interface by creating stubs to
// addresses of the various gRPC services that connect to the switch. The
// template parameter allows the user to provide a policy class to create new
// gRPC stubs for every gRPC service. This policy class should have a function
// called `Create` that uses the first parameter, which will be passed the
// `NewStub` function of a given gRPC service, to create a stub with the desired
// channel/credentials. Any arguments after `SwitchServices services` will be
// forwarded to this policy class.
//
// e.g.
// class CreateMyGrpcStub {
//  public:
//   template <class NewStubFunction>
//   auto Create(NewStubFunction&& new_stub, const std::string& address,
//               std::string_view /*chassis*/, std::string_view /*stub_type*/,
//               grpc::ChannelArguments channel_arguments = {}) {
//     return new_stub(grpc::CreateCustomChannel(...), ...);
//   }
// };
// BasicSwitch<CreateMyGrpcStub> my_switch(...);
// absl::make_unique<BasicSwitch<CreateGrpcStub<LocalTcp>>>(...);
template <class CreateStubPolicy>
class BasicSwitch : public thinkit::Switch, private CreateStubPolicy {
public:
  template <class... Args>
  BasicSwitch(std::string chassis_name, uint32_t device_id,
              SwitchServices services, Args &&...args)
      : CreateStubPolicy(std::forward<Args>(args)...),
        chassis_name_(std::move(chassis_name)), device_id_(device_id),
        services_(std::move(services)) {}

  const std::string &ChassisName() override { return chassis_name_; };

  uint32_t DeviceId() override { return device_id_; }

  absl::StatusOr<std::unique_ptr<p4::v1::P4Runtime::StubInterface>>
  CreateP4RuntimeStub() override {
    return CreateStubPolicy::Create(
        p4::v1::P4Runtime::NewStub, services_.p4runtime_address, chassis_name_,
        "P4 Runtime", pdpi::GrpcChannelArgumentsForP4rt());
  }

  absl::StatusOr<std::unique_ptr<gnmi::gNMI::StubInterface>>
  CreateGnmiStub() override {
    return CreateStubPolicy::Create(gnmi::gNMI::NewStub, services_.gnmi_address,
                                    chassis_name_, "gNMI");
  }

  absl::StatusOr<
      std::unique_ptr<::gnoi::factory_reset::FactoryReset::StubInterface>>
  CreateGnoiFactoryResetStub() override {
    return CreateStubPolicy::Create(
        ::gnoi::factory_reset::FactoryReset::NewStub, services_.gnoi_address,
        chassis_name_, "gNOI Factory Reset");
  }

  absl::StatusOr<std::unique_ptr<::gnoi::system::System::StubInterface>>
  CreateGnoiSystemStub() override {
    return CreateStubPolicy::Create(::gnoi::system::System::NewStub,
                                    services_.gnoi_address, chassis_name_,
                                    "gNOI System");
  }

  absl::StatusOr<std::unique_ptr<::gnoi::diag::Diag::StubInterface>>
  CreateGnoiDiagStub() override {
    return CreateStubPolicy::Create(::gnoi::diag::Diag::NewStub,
                                    services_.gnoi_address, chassis_name_,
                                    "gNOI Diag");
  }

  absl::StatusOr<std::unique_ptr<
      ::gnoi::certificate::CertificateManagement::StubInterface>>
  CreateGnoiCertificateStub() override {
    return CreateStubPolicy::Create(
        ::gnoi::certificate::CertificateManagement::NewStub,
        services_.gnoi_address, chassis_name_, "gNOI Certificate");
  }

  absl::StatusOr<std::unique_ptr<::gnoi::os::OS::StubInterface>>
  CreateGnoiOsStub() override {
    return CreateStubPolicy::Create(::gnoi::os::OS::NewStub,
                                    services_.gnoi_address, chassis_name_,
                                    "gNOI OS");
  }

private:
  std::string chassis_name_;
  uint32_t device_id_;
  SwitchServices services_;
};

} // namespace pins_test

#endif // PINS_LIB_BASIC_SWITCH_H_
