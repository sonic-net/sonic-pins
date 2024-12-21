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

#ifndef PINS_P4_SYMBOLIC_PACKET_SYNTHESIZER_PACKET_SYNTHESIZER_H_
#define PINS_P4_SYMBOLIC_PACKET_SYNTHESIZER_PACKET_SYNTHESIZER_H_

#include <memory>
#include <optional>
#include <string>
#include <vector>

#include "p4/v1/p4runtime.pb.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesis_criteria.pb.h"
#include "p4_symbolic/packet_synthesizer/packet_synthesizer.pb.h"
#include "p4_symbolic/symbolic/symbolic.h"

namespace p4_symbolic::packet_synthesizer {

// A high-level, stateful interface to packet synthesis via p4-symbolic.
// A PacketSynthesizer object can only be created through a call to `Create`
// with appropriate inputs (P4 program, table entries, etc.).
// Given an instance, one may call `SynthesizePacket` multiple times to
// synthesize packets satisfying the given input criteria (if possible).
//
// Example usage:
//   ASSIGN_OR_RETURN(std::unique_ptr<PacketSynthesizer> synthesizer,
//   PacketSynthesizer::Create(config, entries, ports, translation);
//   ASSIGN_OR_RETURN(PacketSynthesisResult result_1,
//                                  synthesizer->SynthesizePacket(criteria_1));
//   ASSIGN_OR_RETURN(PacketSynthesisResult result_2,
//                                  synthesizer->SynthesizePacket(criteria_2));
//   if (result_1.has_synthesized_packet()) {...}
//
// This class is NOT thread safe. Clients must serialize calls to
// `SynthesizePacket`.
// TODO: Due to p4-symbolic's use of a single global Z3 context, it
// is currently not safe to have more than once instance of this class per
// process.
class PacketSynthesizer {
public:
  // Creates and initializes an instance of PacketSynthesizer given the
  // input (the P4 program, table entries, etc.). Returns a unique pointer to
  // the created object on success. The returned object keeps a state
  // corresponding to the input of this function.
  //
  // This static function is the only way to create an instance of
  // PacketSynthesizer.
  static absl::StatusOr<std::unique_ptr<PacketSynthesizer>>
  Create(const PacketSynthesisParams &params);

  // Attempts to synthesize and return a packet (if any) for the given
  // `criteria`.
  absl::StatusOr<PacketSynthesisResult>
  SynthesizePacket(const PacketSynthesisCriteria &criteria);

  // Disallow copy and move.
  PacketSynthesizer(const PacketSynthesizer &) = delete;
  PacketSynthesizer(PacketSynthesizer &&) = delete;
  PacketSynthesizer &operator=(const PacketSynthesizer &) = delete;
  PacketSynthesizer &operator=(PacketSynthesizer &&) = delete;

  // The order of Z3 frames corresponding to different types of criteria. The
  // criteria type in lower index will be lower in the stack. See
  // `PrepareZ3SolverStack` for more details about the use of Z3 frames. The
  // order is chosen based on empirical results and intuition. For example, we
  // expect the client to change the drop_expectation less frequently than the
  // table frame across the sequence of calls to SynthesizePackets because in
  // the client the loop that iterates over tables is kept inside the loop that
  // iterates over drop_expectations. This is because we have empirically
  // observed that doing so (as opposed to the other way around) leads to better
  // performance.
  // Note that some types of criteria (e.g. PayloadCriteria) do not require Z3
  // constraints. Such criteria excluded from the stack and therefore the order.
  // In the future, it might make sense for the client to specify the order.
  const std::vector<CriteriaVariant::CriteriaCase> kSolverFrameStackOrder = {
      CriteriaVariant::kOutputCriteria,
      CriteriaVariant::kInputPacketHeaderCriteria,
      CriteriaVariant::kTableReachabilityCriteria,
      CriteriaVariant::kTableEntryReachabilityCriteria,
  };

private:
  // A PacketSynthesizer object may only be created through a (successful) call
  // to Create.
  explicit PacketSynthesizer(p4_symbolic::symbolic::SolverState &&solver_state)
      : solver_state_(std::move(solver_state)) {
    // Prepare the solver frame stack.
    for (int i = 0; i < kSolverFrameStackOrder.size(); i++) {
      solver_state_.solver->push();
    }
    solver_frame_stack_size_ = kSolverFrameStackOrder.size();
    current_criteria_ = PacketSynthesisCriteria();
  }

  // The solver state.
  p4_symbolic::symbolic::SolverState solver_state_;

  // The current criteria encoded in solver state (through the use of Z3
  // frames).
  // Invariant: must truly reflect the constraints encoded in Z3. i.e.
  // CriteriaToZ3Stack(current_criteria_) == solver.z3.current_stack. Empty
  // criteria variants correspond to Z3 frames with no assertion.
  PacketSynthesisCriteria current_criteria_;
  // The number of Z3 frames pushed to the solver state.
  // Invariant 1: must truly reflect the number of Z3 frames.
  // Invariant 2: must be equal to kSolverFrameStackOrder.size() at the
  // end of any (successful) call to `Create` and `SynthesizePacket`. This is
  // because we push a frame (even if empty) for each member of
  // kSolverFrameStackOrder.
  int solver_frame_stack_size_ = 0;

  // Pushes a new (Z3) frame to the solver state.
  absl::Status PushSolverFrame();
  // Pops `n` (Z3) frames from the solver state. Returns error if there aren't
  // enough frames to pop.
  absl::Status PopSolverFrames(int n = 1);

  // Adds a new (Z3) frame to the solver state, then adds logical assertions
  // corresponding to the given `criteria_case` of the input `criteria`.
  absl::Status AddFrameForCriteria(CriteriaVariant::CriteriaCase criteria_case,
                                   const PacketSynthesisCriteria &criteria);

  // To use Z3's incremental solver and gain better performance, we keep logical
  // constraints corresponding to different types of criteria in separate Z3
  // frames (the order of which is determined by kSolverFrameStackOrder). Across
  // calls to SynthesizePacket, we adjust the frame stack only if needed. This
  // function adjusts Z3's frame stack based on the previous and new values for
  // packet synthesis criteria. If a part of the criteria is changed, the frames
  // from the lowest changing criteria upward get popped and frames (and
  // constraints) corresponding to the new values get pushed.
  absl::Status PrepareZ3SolverStack(const PacketSynthesisCriteria &criteria);
};

} // namespace p4_symbolic::packet_synthesizer

#endif // PINS_P4_SYMBOLIC_PACKET_SYNTHESIZER_PACKET_SYNTHESIZER_H_
