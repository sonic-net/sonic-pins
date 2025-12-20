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

#ifndef PINS_TESTS_INTEGRATION_SYSTEM_NSF_COMPARE_P4FLOWS_H_
#define PINS_TESTS_INTEGRATION_SYSTEM_NSF_COMPARE_P4FLOWS_H_

#include "absl/log/log.h"
#include "p4/v1/p4runtime.pb.h"

namespace pins_test {

// Compares two P4Flow snapshots which are in proto format. One is before the
// NSF reboot and the other is after. There are certain fields which are
// expected to change after NSF. Those fields will be ignored during the
// comparison.
absl::Status
CompareP4FlowSnapshots(const p4::v1::ReadResponse &snapshot_before_nsf,
                       const p4::v1::ReadResponse &snapshot_after_nsf);

} // namespace pins_test

#endif // PINS_TESTS_INTEGRATION_SYSTEM_NSF_COMPARE_P4FLOWS_H_
