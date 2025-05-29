// Copyright 2025 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#ifndef PINS_TESTS_PACKET_CAPTURE_PACKET_CAPTURE_TEST_UTIL_H_
#define PINS_TESTS_PACKET_CAPTURE_PACKET_CAPTURE_TEST_UTIL_H_

#include <cstdint>
#include <ostream>
#include <string>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "proto/gnmi/gnmi.pb.h"
#include "thinkit/mirror_testbed.h"

namespace pins_test {
namespace pctutil {

// Represents a link connecting the switch under test (SUT) to a control device.
struct SutToControlLink {
  std::string sut_ingress_port_gnmi_name;
  std::string control_switch_inject_port_gnmi_name;
  std::string sut_mtp_port_gnmi_name; // mirror to port.
};

std::ostream &operator<<(std::ostream &os, const SutToControlLink &link);

// Nondeterministically picks and returns a `SutToControlLink` that's up, or
// returns an error if no such port is found.
// Currently link is hardcoded to Ethernet1/1/1
absl::StatusOr<SutToControlLink>
PickSutToControlDeviceLinkThatsUp(thinkit::MirrorTestbed &testbed);

// Get vendor port id corresponding to GNMI port name.
// For example, GNMI port name "Ethernet1/1/1" corresponds to a vendor
// port id "1".
absl::StatusOr<std::string>
GetVendorPortId(absl::string_view gnmi_port_name,
                gnmi::gNMI::StubInterface *gnmi_stub);

// Read stat counters from GNMI.
absl::StatusOr<uint64_t> GetGnmiStat(absl::string_view stat_name,
                                     absl::string_view interface,
                                     gnmi::gNMI::StubInterface *gnmi_stub);

// Parse the uint64 observation time from PSAMP header into an absl::Duration
// type. The first 32 bits of the observation time field represent the seconds
// portion of the observation time. The latter 32 bits of the field represent
// the nanosecond portion of the observation time.
absl::Duration ParsePsampHeaderObservationTime(uint64_t observation_time);

} // namespace pctutil
} // namespace pins_test

#endif // PINS_TESTS_PACKET_CAPTURE_PACKET_CAPTURE_TEST_UTIL_H_
