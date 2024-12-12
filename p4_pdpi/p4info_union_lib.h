// Copyright 2020 Google LLC
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

#ifndef PINS_P4_PDPI_P4INFO_UNION_LIB_H_
#define PINS_P4_PDPI_P4INFO_UNION_LIB_H_

#include <string>

#include "absl/status/statusor.h"
#include "p4/config/v1/p4info.pb.h"

namespace pdpi {

// Unions `infos` into one unioned version.
// Entities (i.e. tables, actions, etc.) with distinct IDs are unioned as if
// they were declared in the same P4 program. Entities with identical IDs must
// be identical (except for those described below) and are unioned into a single
// copy, or the function will return an error describing the diff. Entities that
// are not supported, such as externs, cause the function to return
// UNIMPLEMENTED.
// Entities that need not be identical include:
// - Tables, which will have their match fields, action refs,
//   direct resource ids and preambles unioned.
absl::StatusOr<::p4::config::v1::P4Info>
UnionP4info(const std::vector<::p4::config::v1::P4Info> &infos);

} // namespace pdpi

#endif // PINS_P4_PDPI_P4INFO_UNION_LIB_H_
