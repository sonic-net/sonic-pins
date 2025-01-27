// Copyright 2024 Google LLC
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
#ifndef PINS_TESTS_LIB_P4INFO_HELPER_H_
#define PINS_TESTS_LIB_P4INFO_HELPER_H_

#include <string>

#include "absl/status/statusor.h"
#include "p4/config/v1/p4info.pb.h"
#include "p4_infra/p4_pdpi/ir.pb.h"
#include "thinkit/switch.h"

namespace pins {

// Searches the IrP4Info for a table matching 'table_name' with a match field
// matching 'field_name'. If either entry cannot be found it will return false.
// Otherwise, it returns true.
bool TableHasMatchField(const pdpi::IrP4Info &ir_p4info,
                        const std::string &table_name,
                        const std::string &field_name);

// Fetches the P4Info in SUT.
absl::StatusOr<p4::config::v1::P4Info> GetP4InfoFromSUT(thinkit::Switch &sut);

} // namespace pins

#endif // PINS_TESTS_LIB_P4INFO_HELPER_H_
