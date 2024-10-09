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

#ifndef PINS_GUTIL_TIMER_H_
#define PINS_GUTIL_TIMER_H_

#include "absl/time/clock.h"
#include "absl/time/time.h"

namespace gutil {

// A simple timer implementation.
class Timer {
 public:
  // Returns the duration between the current time and the last reset (or
  // initialization).
  absl::Duration GetDuration() { return absl::Now() - start_time_; }

  // Same as GetDuration. Resets the timer as well.
  absl::Duration GetDurationAndReset() {
    absl::Duration duration = GetDuration();
    Reset();
    return duration;
  }

  // Subsequent calls to GetDuration will measure the duration between the last
  // call to Reset and those calls.
  void Reset() { start_time_ = absl::Now(); }

 private:
  absl::Time start_time_ = absl::Now();
};

}  // namespace gutil

#endif  // PINS_GUTIL_TIMER_H_
