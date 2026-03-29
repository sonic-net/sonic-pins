// Copyright 2026 Google LLC
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

// Open-source DataplaneValidationBackend for PINS switches running SAI P4.
//
// Uses 4ward for output prediction and trace collection, SAI P4 ACL entries
// for punt-all, and shared auxiliary entry logic for v1model targets.
// See README.md for design details.

#ifndef PINS_DVAAS_PORTABLE_PINS_BACKEND_PORTABLE_PINS_BACKEND_H_
#define PINS_DVAAS_PORTABLE_PINS_BACKEND_PORTABLE_PINS_BACKEND_H_

#include <memory>

#include "dvaas/dataplane_validation.h"
#include "p4/v1/p4runtime.pb.h"

namespace dvaas {

// Creates a DataplaneValidationBackend that uses 4ward for output prediction
// and SAI P4 infrastructure for punt-all and auxiliary entries.
std::unique_ptr<DataplaneValidationBackend> CreatePortablePinsBackend(
    p4::v1::ForwardingPipelineConfig fourward_config);

}  // namespace dvaas

#endif  // PINS_DVAAS_PORTABLE_PINS_BACKEND_PORTABLE_PINS_BACKEND_H_
