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

#ifndef PINS_P4_SYMBOLIC_PACKET_SYNTHESIZER_UTIL_H_
#define PINS_P4_SYMBOLIC_PACKET_SYNTHESIZER_UTIL_H_

#include "absl/status/status.h"
#include "p4_symbolic/symbolic/symbolic.h"

// This file contains various utility functions and classes used by packet
// synthesizer.

namespace p4_symbolic::packet_synthesizer {

// TODO: We need extra constraints to avoid generating packets
// the switch deams invalid and drops, such as "martian" packets.
// Ideally this switch behavior would be fully modeled in P4 instead, and this
// function would disappear.
absl::Status
AddSanePacketConstraints(p4_symbolic::symbolic::SolverState &state);

// A simple timer implementation.
// TODO: Move this to third_party/pins_infra/gutil/timer
class Timer {
public:
  // Returns the duration between the current time and the last reset (or
  // initialization).
  absl::Duration GetDuration() { return absl::Now() - start_time_; }
  // Same as GetDuration. Resets the timer as well.
  absl::Duration GetDurationAndReset() {
    auto duration = GetDuration();
    Reset();
    return duration;
  }
  // Subsequent calls to GetDuration will measure the duration between the last
  // call to Reset and those calls.
  void Reset() { start_time_ = absl::Now(); }

private:
  absl::Time start_time_ = absl::Now();
};

// Turns a given IrValue into equivalent Z3 bitvector with length `bitwidth`.
absl::StatusOr<z3::expr> IrValueToZ3Bitvector(const pdpi::IrValue &value,
                                              int bitwidth);

// Return Z3 constraints corresponding to `field` matching the given
// pdpi::IrMatch value assuming the field's size is `bitwidth`.
absl::StatusOr<z3::expr> GetFieldMatchConstraints(z3::expr field, int bitwidth,
                                                  const pdpi::IrMatch &match);

}  // namespace p4_symbolic::packet_synthesizer

#endif // PINS_P4_SYMBOLIC_PACKET_SYNTHESIZER_UTIL_H_
