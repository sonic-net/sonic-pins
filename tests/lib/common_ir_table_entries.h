// Copyright 2025 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#ifndef PINS_TESTS_LIB_COMMON_IR_TABLE_ENTRIES_H_
#define PINS_TESTS_LIB_COMMON_IR_TABLE_ENTRIES_H_

// This file contains common IrTableEntry definitions and generators for testing
// against SAI P4 programs.
#include "absl/strings/string_view.h"
#include "p4_infra/p4_pdpi/ir.pb.h"

namespace pins {

// Returns an ACL_INGRESS flow that will match any packet and punt it to a CPU
// queue.
pdpi::IrTableEntry
PuntAllPacketsToControllerIrTableEntry(absl::string_view queue_id);

// Returns an ACL_PRE_INGERSS flow that will set the VRF for all traffic.
pdpi::IrTableEntry SetVrfIdForAllPacketsIrTableEntry(absl::string_view vrf_id);

} // namespace pins

#endif // PINS_TESTS_LIB_COMMON_IR_TABLE_ENTRIES_H_
