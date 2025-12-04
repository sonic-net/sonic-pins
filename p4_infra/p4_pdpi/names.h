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

#ifndef PINS_P4_INFRA_P4_PDPI_NAMES_H_
#define PINS_P4_INFRA_P4_PDPI_NAMES_H_

#include <string>

#include "absl/status/statusor.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"

namespace pdpi {

// Returns the table name (alias) associated with the given entity.
absl::StatusOr<std::string> EntityToTableName(const IrP4Info& info,
                                              const p4::v1::Entity& entity);

// Returns the table name (alias) associated with the given entity.
absl::StatusOr<std::string> EntityToTableName(const IrEntity& entity);

}  // namespace pdpi

#endif  // PINS_P4_INFRA_P4_PDPI_NAMES_H_
