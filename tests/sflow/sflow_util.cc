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

#include "tests/sflow/sflow_util.h"

#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "absl/strings/substitute.h"
#include "absl/time/time.h"
#include "gutil/status.h"
#include "lib/gnmi/gnmi_helper.h"
#include "lib/validator/validator_lib.h"

namespace pins {
namespace {

// --- Sflow gnmi config paths ---

constexpr absl::string_view kSflowGnmiConfigSampleSizePath =
    "/sampling/sflow/config/sample-size";
constexpr absl::string_view kSflowGnmiConfigEnablePath =
    "/sampling/sflow/config/enabled";
constexpr absl::string_view kSflowGnmiConfigInterfaceSampleRatePath =
    "/sampling/sflow/interfaces/interface[name=$0]/config/"
    "ingress-sampling-rate";

// --- Sflow gnmi state paths ---

constexpr absl::string_view kSflowGnmiStateSampleSizePath =
    "/sampling/sflow/state/sample-size";
constexpr absl::string_view kSflowGnmiStateEnablePath =
    "/sampling/sflow/state/enabled";
constexpr absl::string_view kSflowGnmiStateInterfaceSampleRatePath =
    "/sampling/sflow/interfaces/interface[name=$0]/state/"
    "ingress-sampling-rate";

}  // namespace

absl::Status VerifyGnmiStateConverged(gnmi::gNMI::StubInterface* gnmi_stub,
                                      absl::string_view state_path,
                                      absl::string_view expected_value) {
  ASSIGN_OR_RETURN(std::string state_value,
                   pins_test::GetGnmiStatePathInfo(gnmi_stub, state_path));
  if (expected_value == state_value) {
    return absl::OkStatus();
  }
  return absl::FailedPreconditionError(
      absl::StrCat(state_path, " value is ", state_value,
                   ", which is not equal to ", expected_value));
}

absl::Status SetSflowSamplingSize(gnmi::gNMI::StubInterface* gnmi_stub,
                                  int sampling_size, absl::Duration timeout) {
  std::string ops_val = absl::StrCat(
      "{\"openconfig-sampling-sflow:sample-size\":", sampling_size, "}");

  RETURN_IF_ERROR(SetGnmiConfigPath(gnmi_stub, kSflowGnmiConfigSampleSizePath,
                                    pins_test::GnmiSetType::kUpdate, ops_val));

  return pins_test::WaitForCondition(VerifyGnmiStateConverged, timeout,
                                     gnmi_stub, kSflowGnmiStateSampleSizePath,
                                     ops_val);
}

absl::Status SetSflowConfigEnabled(gnmi::gNMI::StubInterface* gnmi_stub,
                                   bool enabled, absl::Duration timeout) {
  std::string ops_val = absl::StrCat("{\"openconfig-sampling-sflow:enabled\":",
                                     (enabled ? "true" : "false"), "}");
  RETURN_IF_ERROR(SetGnmiConfigPath(gnmi_stub, kSflowGnmiConfigEnablePath,
                                    pins_test::GnmiSetType::kUpdate, ops_val));

  return pins_test::WaitForCondition(VerifyGnmiStateConverged, timeout,
                                     gnmi_stub, kSflowGnmiStateEnablePath,
                                     ops_val);
}

absl::Status SetSflowIngressSamplingRate(gnmi::gNMI::StubInterface* gnmi_stub,
                                         absl::string_view interface,
                                         int sampling_rate,
                                         absl::Duration timeout) {
  std::string ops_val = absl::StrCat(
      "{\"openconfig-sampling-sflow:ingress-sampling-rate\":", sampling_rate,
      "}");

  RETURN_IF_ERROR(SetGnmiConfigPath(
      gnmi_stub,
      absl::Substitute(kSflowGnmiConfigInterfaceSampleRatePath, interface),
      pins_test::GnmiSetType::kUpdate, ops_val));

  return pins_test::WaitForCondition(
      VerifyGnmiStateConverged, timeout, gnmi_stub,
      absl::Substitute(kSflowGnmiStateInterfaceSampleRatePath, interface),
      ops_val);
}
}  // namespace pins
