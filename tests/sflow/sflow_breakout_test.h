#ifndef PINS_TESTS_SFLOW_SFLOW_BREAKOUT_TEST_H_
#define PINS_TESTS_SFLOW_SFLOW_BREAKOUT_TEST_H_

#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_format.h"
#include "absl/strings/substitute.h"
#include "p4/config/v1/p4info.pb.h"
#include "tests/thinkit_gnmi_interface_util.h"
#include "thinkit/switch.h"

namespace pins_test {

struct SflowBreakoutTestOption {
  // sFlow config options.

  int sampling_rate;
  int sampling_header_size;
  std::string agent_addr_ipv6;
  std::string collector_ip;
  int collector_port;

  // The port to perform breakout. The test would pick arbitrary one if this
  // field is not present.
  std::optional<RandomPortBreakoutInfo> port_info;
  // Indicates whether the other side has performed a breakout test.
  bool mirror_broken_out;

  std::string DebugString() const;
};

struct SflowBreakoutResult {
  // Selected port info during the breakout test. Store this info so we can
  // perform breakout on the same port later on the other switch.
  RandomPortBreakoutInfo port_info;
  // Ports generated during the breakout test.
  std::vector<std::string> breakout_ports;
};

// This is a function which would perform DPB with sFlow config. The test steps
// would be following:
// 1. Select an interface that is UP and have more than one breakout mode.
// 2. Generate DPB and sFlow config according to breakout info.
// 3. Use gNMI to set generated config.
// 4. Verify breakout and sflow states are as expected.
// In a successful run, it would return the chosen port info and a vector of
// ports after breakout. Otherwise it would return an error. This function can
// be called on both sides of mirrortestbed.
// e.g. Before breakout (2x400)
//     Ethernet1/1/1
//     Ethernet1/1/5
// After breakout (1X400, 2x200)
//     Ethernet1/1/1
//     Ethernet1/1/3
//     Ethernet1/1/7
absl::StatusOr<SflowBreakoutResult> TestBreakoutWithSflowConfig(
    thinkit::Switch& sut, const std::string& platform_json_contents,
    const p4::config::v1::P4Info& p4_info,
    const SflowBreakoutTestOption& option);

}  // namespace pins_test

#endif  // PINS_TESTS_SFLOW_SFLOW_BREAKOUT_TEST_H_
