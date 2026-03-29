#include "fourward/fourward_switch.h"

#include <cstdint>
#include <memory>
#include <utility>

#include "absl/status/statusor.h"
#include "fourward/fourward_server.h"
#include "gutil/status.h"
#include "grpcpp/create_channel.h"
#include "grpcpp/security/credentials.h"
#include "p4/v1/p4runtime.grpc.pb.h"

namespace dvaas {

FourwardSwitch::FourwardSwitch(FourwardServer server)
    : server_(std::move(server)) {}

absl::StatusOr<FourwardSwitch> FourwardSwitch::Create(uint32_t device_id) {
  ASSIGN_OR_RETURN(FourwardServer server, FourwardServer::Start(device_id));
  return FourwardSwitch(std::move(server));
}

absl::StatusOr<std::unique_ptr<p4::v1::P4Runtime::StubInterface>>
FourwardSwitch::CreateP4RuntimeStub() {
  std::shared_ptr<grpc::Channel> channel = grpc::CreateChannel(
      server_.Address(), grpc::InsecureChannelCredentials());
  return p4::v1::P4Runtime::NewStub(channel);
}

}  // namespace dvaas
