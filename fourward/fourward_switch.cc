#include "fourward/fourward_switch.h"

#include <cstdint>
#include <memory>
#include <utility>
#include <vector>

#include "absl/status/statusor.h"
#include "fourward/fake_gnmi_service.h"
#include "fourward/fourward_server.h"
#include "github.com/openconfig/gnmi/proto/gnmi/gnmi.grpc.pb.h"
#include "gutil/status.h"
#include "grpcpp/create_channel.h"
#include "grpcpp/security/credentials.h"
#include "p4/v1/p4runtime.grpc.pb.h"

namespace dvaas {

FourwardSwitch::FourwardSwitch(FourwardServer server,
                               std::unique_ptr<FakeGnmiServer> gnmi_server)
    : server_(std::move(server)), gnmi_server_(std::move(gnmi_server)) {}

absl::StatusOr<FourwardSwitch> FourwardSwitch::Create(
    uint32_t device_id, std::vector<FakeInterface> interfaces) {
  ASSIGN_OR_RETURN(FourwardServer server, FourwardServer::Start(device_id));
  ASSIGN_OR_RETURN(std::unique_ptr<FakeGnmiServer> gnmi_server,
                   FakeGnmiServer::Create(std::move(interfaces)));
  return FourwardSwitch(std::move(server), std::move(gnmi_server));
}

absl::StatusOr<std::unique_ptr<p4::v1::P4Runtime::StubInterface>>
FourwardSwitch::CreateP4RuntimeStub() {
  std::shared_ptr<grpc::Channel> channel = grpc::CreateChannel(
      server_.Address(), grpc::InsecureChannelCredentials());
  return p4::v1::P4Runtime::NewStub(channel);
}

absl::StatusOr<std::unique_ptr<gnmi::gNMI::StubInterface>>
FourwardSwitch::CreateGnmiStub() {
  std::shared_ptr<grpc::Channel> channel = grpc::CreateChannel(
      gnmi_server_->Address(), grpc::InsecureChannelCredentials());
  return gnmi::gNMI::NewStub(channel);
}

}  // namespace dvaas
