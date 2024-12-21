// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#ifndef PINS_TESTS_SFLOW_SFLOW_UTIL_H_
#define PINS_TESTS_SFLOW_SFLOW_UTIL_H_

#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "proto/gnmi/gnmi.grpc.pb.h"

namespace pins {

// Reads value from `state_path` and verifies it is the same with
// `expected_value`. Returns a FailedPreconditionError if not matched.
absl::Status VerifyGnmiStateConverged(gnmi::gNMI::StubInterface* gnmi_stub,
                                      absl::string_view state_path,
                                      absl::string_view expected_value);

// Sets sFLow sampling size to `sampling_size` and checks if it's applied to
// corresponding state path in `timeout`. Returns error if failed.
absl::Status SetSflowSamplingSize(gnmi::gNMI::StubInterface* gnmi_stub,
                                  int sampling_size,
                                  absl::Duration timeout = absl::Seconds(5));

// Sets sFlow config to `enabled` and checks if it's applied to state path in
// `timeout`. Returns error if failed.
absl::Status SetSflowConfigEnabled(gnmi::gNMI::StubInterface* gnmi_stub,
                                   bool enabled,
                                   absl::Duration timeout = absl::Seconds(5));

// Sets sFlow ingress sampling rate of `interface` to `sampling_rate` and checks
// if it's applied to corresponding state path in `timeout`. Returns error if
// failed.
absl::Status SetSflowIngressSamplingRate(
    gnmi::gNMI::StubInterface* gnmi_stub, absl::string_view interface,
    int sampling_rate, absl::Duration timeout = absl::Seconds(5));


}  // namespace pins
#endif  // PINS_TESTS_SFLOW_SFLOW_UTIL_H_
