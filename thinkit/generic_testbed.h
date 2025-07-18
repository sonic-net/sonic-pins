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

#ifndef PINS_THINKIT_GENERIC_TESTBED_H_
#define PINS_THINKIT_GENERIC_TESTBED_H_

#include <ostream>
#include <string>
#include <tuple>

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "artifacts/otg.grpc.pb.h"
#include "thinkit/control_device.h"
#include "thinkit/proto/generic_testbed.pb.h"
#include "thinkit/switch.h"
#include "thinkit/test_environment.h"

namespace thinkit {

// HttpResponse represents an HTTP response from an Ixia device.
struct HttpResponse {
  int response_code;
  std::string response;
};

inline std::ostream &operator<<(std::ostream &os,
                                const HttpResponse &response) {
  return os << response.response_code << ": " << response.response;
}

// HTTP request types.
enum class RequestType {
  kGet,
  kPost,
  kPatch,
  kDelete,
};

// InterfaceInfo represents the mode of an interface and the name of the peer
// interface.
// - When `interface_modes` are CONTROL_INTERFACE and/or TRAFFIC_GENERATOR,
//   `peer_interface_name` will be populated with the name of the interface on
//   the other end.
// - In the case of CONTROL_INTERFACE, the `peer_interface_name` should be used
//   in functions called on the `ControlDevice` returned by ControlDevice().
// - In the case of multiple CONTROL_INTERFACE, the `peer_device_index` will be
//   used to identify the connected control device. If `peer_device_index` is
//   not provided, ControlDevice(0) will be returned by default.
// - `peer_mac_address` is the MAC address of the peer interface.
// - `peer_ipv4_address` is the IPv4 address of the peer interface.
// - `peer_ipv6_address` is the IPv6 address of the peer interface.
// - `peer_traffic_location` is the location of the OTG traffic port that can be
//   assigned to `otg.Port.location` field.
struct InterfaceInfo {
  absl::flat_hash_set<thinkit::InterfaceMode> interface_modes;
  int peer_device_index;             // Ignore if not applicable.
  std::string peer_interface_name;   // Empty if not applicable.
  std::string peer_mac_address;      // Empty if not applicable.
  std::string peer_ipv4_address;     // Empty if not applicable.
  std::string peer_ipv6_address;     // Empty if not applicable.
  std::string peer_traffic_location; // Empty if not applicable.
  bool operator==(const InterfaceInfo &other) const {
    return std::tie(interface_modes, peer_device_index, peer_interface_name,
                    peer_mac_address, peer_ipv4_address, peer_ipv6_address,
                    peer_traffic_location) ==
           std::tie(other.interface_modes, other.peer_device_index,
                    other.peer_interface_name, other.peer_mac_address,
                    other.peer_ipv4_address, other.peer_ipv6_address,
                    other.peer_traffic_location);
  }
};

// The GenericTestbed interface represents a testbed with control interface and
// Ixia interface.
class GenericTestbed {
public:
  virtual ~GenericTestbed() {}

  // Returns the PINS switch (aka system) under test.
  virtual Switch &Sut() = 0;

  // Returns a default control device responsible for packet injection and
  // various management operations. This could be but isn't limited to being
  // another PINS switch, a non-PINS switch, or a host machine.
  virtual class ControlDevice &ControlDevice() = 0;

  // Returns a control device in the Generic Testbed at the specified index.
  virtual class ControlDevice &ControlDevice(int index) = 0;

  // Returns the test environment in which the test is run.
  virtual TestEnvironment &Environment() = 0;

  // Returns a map from SUT interface name (e.g. Ethernet0) to its
  // `InterfaceInfo`, which describes what it's connected to.
  virtual absl::flat_hash_map<std::string, InterfaceInfo>
  GetSutInterfaceInfo() = 0;

  // Returns a client to interact with the Open Traffic Generator Service, if
  // present, for the testbed.
  virtual absl::StatusOr<otg::Openapi::StubInterface*> GetTrafficClient() {
    return absl::UnimplementedError("GetTrafficClient is not implemented.");
  }

  // Sends a REST request to the Ixia and returns the response.
  // `url` can be either "https://...", "/api/...", or "/ixnetwork/...".
  virtual absl::StatusOr<HttpResponse>
  SendRestRequestToIxia(RequestType type, absl::string_view url,
                        absl::string_view payload) = 0;
};

} // namespace thinkit
#endif // PINS_THINKIT_GENERIC_TESTBED_H_
