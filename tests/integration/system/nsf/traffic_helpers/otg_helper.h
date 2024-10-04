// Copyright 2024 Google LLC
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

#ifndef PINS_TESTS_INTEGRATION_SYSTEM_NSF_TRAFFIC_HELPERS_OTG_HELPER_H_
#define PINS_TESTS_INTEGRATION_SYSTEM_NSF_TRAFFIC_HELPERS_OTG_HELPER_H_

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "tests/integration/system/nsf/interfaces/testbed.h"
#include "tests/integration/system/nsf/interfaces/traffic_helper.h"

namespace pins_test {

class OtgHelper : public TrafficHelper {
 public:
  OtgHelper(bool enable_linerate = false) : enable_linerate_(enable_linerate) {}
  // Configures the base settings for the flow:
  // - Packet size
  // - Transmission duration
  // - Transmission rate
  // - Capture metrics
  void ConfigureFlowBaseSettings(::otg::Flow* flow, absl::string_view src_port,
                                 absl::string_view dst_port);
  void ConfigureFlowEthernetHeader(::otg::Flow* flow, absl::string_view src_mac,
                                   absl::string_view dst_mac);
  absl::Status StartTraffic(const Testbed &testbed,
                            absl::string_view config_label) override;
  absl::Status StopTraffic(const Testbed &testbed) override;
  absl::Status ValidateTraffic(const Testbed &testbed,
                               absl::Duration max_acceptable_outage) override;

private:
  bool enable_linerate_;
};

}  // namespace pins_test

#endif  // PINS_TESTS_INTEGRATION_SYSTEM_NSF_TRAFFIC_HELPERS_OTG_HELPER_H_
