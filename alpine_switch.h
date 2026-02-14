#ifndef PINS_LIB_ALPINE_SWITCH_H_
#define PINS_LIB_ALPINE_SWITCH_H_
#include <cstdint>
#include <memory>
#include <string>
#include "absl/log/log.h"
#include "absl/status/statusor.h"
#include "grpc/grpc.h"
#include "grpcpp/support/channel_arguments.h"
#include "lib/basic_switch.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"
namespace pins_test {
template <class CreateStubPolicy>
class AlpineSwitch : public BasicSwitch<CreateStubPolicy> {
public:
  template <class... Args>
  AlpineSwitch(std::string chassis_name, uint32_t device_id,
               SwitchServices services, Args&&... args)
      : BasicSwitch<CreateStubPolicy>(chassis_name, device_id, services,
                                      std::move(args)...) {}
  template <class... Args>
  AlpineSwitch(BasicSwitch<CreateStubPolicy> basic_switch)
      : BasicSwitch<CreateStubPolicy>(std::move(basic_switch)) {}
  absl::StatusOr<std::unique_ptr<p4::v1::P4Runtime::StubInterface>>
  CreateP4RuntimeStub() override {
    LOG(WARNING) << "Creating P4 Runtime stub for AlpineSwitch";
    grpc::ChannelArguments args;
    args.SetInt(GRPC_ARG_MAX_METADATA_SIZE, pdpi::P4GRPCMaxMetadataSize());
    // Allows grpc::channel to send keepalive ping without on-going traffic.
    args.SetInt(
        GRPC_ARG_KEEPALIVE_TIMEOUT_MS,
        300000 /*5 minutes*/);  // Set the timeout to disconnect a zombie client
    args.SetInt(GRPC_ARG_KEEPALIVE_TIME_MS, 180000 /*3 minutes*/);
    return CreateStubPolicy::Create(
        p4::v1::P4Runtime::NewStub,
        BasicSwitch<CreateStubPolicy>::services_.p4runtime_address,
        BasicSwitch<CreateStubPolicy>::chassis_name_, "P4 Runtime", args);
  }
};
}  // namespace pins_test
#endif  // PINS_LIB_ALPINE_SWITCH_H_
