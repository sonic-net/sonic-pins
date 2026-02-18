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

#ifndef PINS_P4_PDPI_IR_TOOLS_H_
#define PINS_P4_PDPI_IR_TOOLS_H_

#include <functional>
#include <string>
#include <vector>

#include "absl/functional/any_invocable.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/types/variant.h"
#include "p4/config/v1/p4types.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
namespace pdpi {

// `TransformValuesOfType` uses `info` to find all values of `target_type`
// in `entry`, then applies `transformer` to them.
//
// This function fails if:
// * the 'transformer' fails.
// * the `info` and the `entry` are incompatible.
//
// Note that the IR does not include enough information about counters, meters,
// or registers to determine if they use a particular P4NamedType. They are thus
// currently ignored by this function.
absl::Status TransformValuesOfType(
    const IrP4Info &info, const p4::config::v1::P4NamedType &target_type,
    IrTableEntry &entry,
    const std::function<absl::StatusOr<std::string>(absl::string_view)>
        &transformer);

// `TransformValuesOfType` uses `info` to find all values of `target_type`
// in `entries`, then applies `transformer` to them. See the
// `TransformValuesOfType` which acts on a single entry above for further
// information. If this function returns an error, a prefix of the `entries` may
// still be transformed by `transformer`.
absl::Status TransformValuesOfType(
    const IrP4Info &info, const p4::config::v1::P4NamedType &target_type,
    std::vector<IrTableEntry> &entries,
    const std::function<absl::StatusOr<std::string>(absl::string_view)>
        &transformer);

// `VisitValuesOfType` uses `info` to find all values of `target_type`
// in `entries`, then applies `visitor` to them.
// WARNING: This function is inefficient because it copies the entries and uses
// `TransformValuesOfType`, mutating every value of `target_type`.
absl::Status VisitValuesOfType(
    const IrP4Info &info, const p4::config::v1::P4NamedType &target_type,
    std::vector<IrTableEntry> entries,
    const absl::AnyInvocable<absl::Status(absl::string_view) const> &visitor);

} // namespace pdpi

#endif // PINS_P4_PDPI_IR_TOOLS_H_
