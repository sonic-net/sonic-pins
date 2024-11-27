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

// This file defines the main API entry point for parsing input files
// into our IR representation.

#ifndef P4_SYMBOLIC_PARSER_H_
#define P4_SYMBOLIC_PARSER_H_

#include <string>

#include "absl/types/span.h"
#include "gutil/status.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_pdpi/ir.pb.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/symbolic.h"

namespace p4_symbolic {

absl::StatusOr<symbolic::Dataplane> ParseToIr(
    const std::string &bmv2_json_path, const std::string &p4info_path,
    const std::string &table_entries_path);

absl::StatusOr<symbolic::Dataplane> ParseToIr(
    const std::string &bmv2_json_path, const std::string &p4info_path,
    absl::Span<const p4::v1::TableEntry> table_entries);

absl::StatusOr<symbolic::Dataplane> ParseToIr(
    const std::string &bmv2_json, const pdpi::IrP4Info &p4info,
    absl::Span<const p4::v1::TableEntry> table_entries);

absl::StatusOr<symbolic::Dataplane> ParseToIr(
    const p4::v1::ForwardingPipelineConfig &config,
    absl::Span<const p4::v1::TableEntry> table_entries);

}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_PARSER_H_
