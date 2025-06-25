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

#ifndef PINS_P4_INFRA_P4_PDPI_TEST_P4INFO_H_
#define PINS_P4_INFRA_P4_PDPI_TEST_P4INFO_H_

#include "p4/config/v1/p4info.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"

namespace pdpi {

// Returns a reference to a static P4Info message for the PDPI test P4 program.
// The reference is guaranteed to remain valid at all times.
const p4::config::v1::P4Info& GetTestP4Info();

// Returns a reference to a static IrP4info message for the PDPI test P4
// program. The reference is guaranteed to remain valid at all times.
const pdpi::IrP4Info& GetTestIrP4Info();

}  // namespace pdpi

#endif  // PINS_P4_INFRA_P4_PDPI_TEST_P4INFO_H_
