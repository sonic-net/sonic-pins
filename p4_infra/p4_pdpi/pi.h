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

// Auxiliary functions for working with PI (p4::v1::*) protobufs.
#ifndef PINS_P4_PDPI_PI_H_
#define PINS_P4_PDPI_PI_H_

#include "absl/status/status.h"
#include "p4/v1/p4runtime.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"

namespace pdpi {

// Pads all match field and action parameter values to their full bitwidth,
// as required by some legacy targets such as BMv2.
//
// Note: The resulting table entry is not P4Runtime standard conform.
absl::Status ZeroPadPiTableEntry(const IrP4Info &info,
                                 p4::v1::TableEntry &pi_entry);

} // namespace pdpi

#endif // PINS_P4_PDPI_PI_H_
