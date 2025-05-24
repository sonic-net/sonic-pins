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
// limitations under the License

#ifndef PINS_P4_SYMBOLIC_PACKET_SYNTHESIZER_Z3_MODEL_TO_PACKET_H_
#define PINS_P4_SYMBOLIC_PACKET_SYNTHESIZER_Z3_MODEL_TO_PACKET_H_

#include <optional>

#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesizer.pb.h"
#include "p4_symbolic/symbolic/context.h"
#include "p4_symbolic/symbolic/solver_state.h"

namespace p4_symbolic::packet_synthesizer {

absl::StatusOr<SynthesizedPacket> SynthesizePacketFromZ3Model(
    const symbolic::SolverState &solver_state, absl::string_view packet_payload,
    std::optional<bool> should_be_dropped);

absl::StatusOr<packet_synthesizer::SynthesizedPacket>
SynthesizePacketFromZ3Model(const symbolic::SolverState &solver_state,
                            bool dropped,
                            symbolic::SymbolicPerPacketState &headers);

}  // namespace p4_symbolic::packet_synthesizer

#endif // PINS_P4_SYMBOLIC_PACKET_SYNTHESIZER_Z3_MODEL_TO_PACKET_H_
