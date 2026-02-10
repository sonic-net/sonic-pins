// Copyright 2022 Google LLC
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
#ifndef PINS_P4RT_APP_P4RUNTIME_P4INFO_VERIFICATION_SCHEMA_H_
#define PINS_P4RT_APP_P4RUNTIME_P4INFO_VERIFICATION_SCHEMA_H_

// This file provides utility functions for working with
// P4InfoVerificationSchema objects.

#include "absl/status/statusor.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "p4rt_app/p4runtime/p4info_verification_schema.pb.h"

namespace p4rt_app {

// Convert an IrP4Info object into a P4InfoVerificationSchema. Return an error
// if a valid schema cannot be produced.
absl::StatusOr<P4InfoVerificationSchema>
ConvertToSchema(const pdpi::IrP4Info &ir_p4info);

// Returns the P4InfoVerificationSchema that represents the supported fixed
// tables.
absl::StatusOr<P4InfoVerificationSchema> SupportedSchema();

// Returns OK if the IrP4Info is supported by the capabilities schema.
absl::Status
IsSupportedBySchema(const pdpi::IrP4Info &ir_p4info,
                    const P4InfoVerificationSchema &supported_schema);

} // namespace p4rt_app

#endif // PINS_P4RT_APP_P4RUNTIME_P4INFO_VERIFICATION_SCHEMA_H_
