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

#ifndef P4_SYMBOLIC_IR_PARSER_H_
#define P4_SYMBOLIC_IR_PARSER_H_

#include "absl/status/statusor.h"
#include "absl/types/span.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_symbolic/ir/ir.h"

namespace p4_symbolic::ir {

absl::StatusOr<Dataplane> ParseToIr(
    const p4::v1::ForwardingPipelineConfig &config,
    absl::Span<const p4::v1::Entity> entities);

}  // namespace p4_symbolic::ir

#endif // P4_SYMBOLIC_PARSER_H_
