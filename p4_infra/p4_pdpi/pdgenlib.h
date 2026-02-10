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

#ifndef PINS_P4_PDPI_PDGENLIB_H_
#define PINS_P4_PDPI_PDGENLIB_H_

#include <cstdint>
#include <optional>
#include <string>
#include <vector>

#include "absl/status/statusor.h"
#include "gutil/gutil/status.h"
#include "p4_infra/p4_pdpi/ir.pb.h"

namespace pdpi {

// Configuration options for generated PD proto.
struct PdGenOptions {
  // Package name in generated proto file.
  std::string package;
  // Roles used to filter which tables are included in proto.
  std::vector<std::string> roles;
  // Field number of multicast_group_table_entry. If set to std::nullopt,
  // multicast_group_table is omitted from generated proto.
  std::optional<int16_t> multicast_table_field_number;
};

// Returns the PD proto definition for the given P4 info. May not be fully
// formatted according to any style guide.
absl::StatusOr<std::string> IrP4InfoToPdProto(const IrP4Info &info,
                                              const PdGenOptions &options);

} // namespace pdpi

#endif // PINS_P4_PDPI_PDGENLIB_H_
