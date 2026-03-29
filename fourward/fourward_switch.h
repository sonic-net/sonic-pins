// Adapts a 4ward server to the thinkit::Switch interface.
//
// Starts a 4ward P4Runtime server subprocess and exposes it as a Switch.
// gNMI is not supported (4ward doesn't implement gNMI); CreateGnmiStub()
// returns UNIMPLEMENTED.

#ifndef PINS_FOURWARD_FOURWARD_SWITCH_H_
#define PINS_FOURWARD_FOURWARD_SWITCH_H_

#include <cstdint>
#include <memory>
#include <string>

#include "absl/status/statusor.h"
#include "fourward/fourward_server.h"
#include "p4/v1/p4runtime.grpc.pb.h"
#include "thinkit/switch.h"

namespace dvaas {

class FourwardSwitch : public thinkit::Switch {
 public:
  // Creates a FourwardSwitch by starting a 4ward server subprocess.
  static absl::StatusOr<FourwardSwitch> Create(uint32_t device_id = 1);

  const std::string& ChassisName() override { return server_.Address(); }
  uint32_t DeviceId() override { return server_.DeviceId(); }

  absl::StatusOr<std::unique_ptr<p4::v1::P4Runtime::StubInterface>>
  CreateP4RuntimeStub() override;

 private:
  explicit FourwardSwitch(FourwardServer server);
  FourwardServer server_;
};

}  // namespace dvaas

#endif  // PINS_FOURWARD_FOURWARD_SWITCH_H_
