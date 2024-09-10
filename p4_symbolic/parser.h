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

#include "gutil/status.h"
#include "p4_symbolic/ir/ir.pb.h"
#include "p4_symbolic/symbolic/symbolic.h"

namespace p4_symbolic {

absl::StatusOr<symbolic::Dataplane> ParseToIr(
    const std::string &bmv2_path, const std::string &p4info_path,
    const std::string &table_entries_path);

}  // namespace p4_symbolic

#endif  // P4_SYMBOLIC_PARSER_H_
