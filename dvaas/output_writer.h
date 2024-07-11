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

#ifndef PINS_DVAAS_OUTPUT_WRITER_H_
#define PINS_DVAAS_OUTPUT_WRITER_H_

#include <functional>

#include "absl/status/status.h"
#include "absl/strings/string_view.h"

namespace dvaas {

// This can be used as input parameter by functions that write output (e.g.
// statistics) but want the client to control how the output is processed.
// TODO: Deprecate and replace OutputWriterFunctionType.
using OutputWriterFunctionType =
    std::function<absl::Status(absl::string_view message)>;

}  // namespace dvaas

#endif  // PINS_DVAAS_OUTPUT_WRITER_H_
