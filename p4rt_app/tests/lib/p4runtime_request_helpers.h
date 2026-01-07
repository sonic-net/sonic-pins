// Copyright 2021 Google LLC
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
#ifndef PINS_P4RT_APP_TESTS_LIB_P4RUNTIME_REQUEST_HELPERS_H_
#define PINS_P4RT_APP_TESTS_LIB_P4RUNTIME_REQUEST_HELPERS_H_

#include <stdint.h>

#include <optional>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_pdpi/p4_runtime_session.h"
#include "sai_p4/capabilities.pb.h"

namespace p4rt_app {
namespace test_lib {

// Translates a PD write request into a PI write request based on the data from
// a pdpi::IrP4Info object.
absl::StatusOr<p4::v1::WriteRequest>
PdWriteRequestToPi(absl::string_view pd_request,
                   const pdpi::IrP4Info &ir_p4_info);

// Translates an Ir write request string into a PI write request based on the
// data from a pdpi::IrP4Info object.
absl::StatusOr<p4::v1::WriteRequest>
IrWriteRequestToPi(absl::string_view ir_request,
                   const pdpi::IrP4Info &ir_p4_info);

absl::StatusOr<sai::WcmpGroupLimitations> GetWcmpGroupCapabilities(
    pdpi::P4RuntimeSession* session, const std::optional<uint64_t>& device_id);

} // namespace test_lib
} // namespace p4rt_app

#endif // PINS_P4RT_APP_TESTS_LIB_P4RUNTIME_REQUEST_HELPERS_H_
