// Copyright (c) 2024, Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#ifndef PINS_DVAAS_SWITCH_API_H_
#define PINS_DVAAS_SWITCH_API_H_

#include <memory>

#include "p4_infra/p4_runtime/p4_runtime_session.h"

namespace dvaas {

// The API used by dataplane validation related tests (Arriba, DVaaS, Ouroboros,
// etc.) to interact with a switch.
struct SwitchApi {
  std::unique_ptr<p4_runtime::P4RuntimeSession> p4rt;
  std::unique_ptr<gnmi::gNMI::StubInterface> gnmi;
};

} // namespace dvaas

#endif // PINS_DVAAS_SWITCH_API_H_
