// Adapts a 4ward server to the thinkit::Switch interface.
//
// Starts a 4ward P4Runtime server subprocess and an in-process fake gNMI
// server, exposing both through the thinkit::Switch API.

#ifndef PINS_FOURWARD_FOURWARD_SWITCH_H_
#define PINS_FOURWARD_FOURWARD_SWITCH_H_

#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "absl/status/statusor.h"
#include "fourward/fake_gnmi_service.h"
#include "fourward/fourward_server.h"
#include "github.com/openconfig/gnmi/proto/gnmi/gnmi.grpc.pb.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "thinkit/switch.h"

namespace dvaas {

class FourwardSwitch : public thinkit::Switch {
 public:
  // Creates a FourwardSwitch by starting a 4ward server subprocess and a fake
  // gNMI server with the given interfaces.
  static absl::StatusOr<FourwardSwitch> Create(
      uint32_t device_id = 1,
      std::vector<FakeInterface> interfaces =
          FakeGnmiService::DefaultInterfaces());

  const std::string& ChassisName() override { return server_.Address(); }
  uint32_t DeviceId() override { return server_.DeviceId(); }

  absl::StatusOr<std::unique_ptr<p4::v1::P4Runtime::StubInterface>>
  CreateP4RuntimeStub() override;

  absl::StatusOr<std::unique_ptr<gnmi::gNMI::StubInterface>>
  CreateGnmiStub() override;

 private:
  FourwardSwitch(FourwardServer server,
                 std::unique_ptr<FakeGnmiServer> gnmi_server);
  FourwardServer server_;
  std::unique_ptr<FakeGnmiServer> gnmi_server_;
};

}  // namespace dvaas

#endif  // PINS_FOURWARD_FOURWARD_SWITCH_H_
