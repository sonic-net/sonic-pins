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

#ifndef GOOGLE_LIB_P4RT_P4RT_PROGRAMMING_CONTEXT_H_
#define GOOGLE_LIB_P4RT_P4RT_PROGRAMMING_CONTEXT_H_

#include <functional>
#include <utility>
#include <vector>

#include "absl/functional/bind_front.h"
#include "absl/status/status.h"
#include "p4_infra/p4_runtime/p4_runtime_session.h"

namespace pins_test {

// This class records INSERT and DELETE programming requests going through it
// and provides a function to revert those requests either explicitly or on
// destruction.
class P4rtProgrammingContext {
public:
  // The constructor normally just takes in a pointer to a `P4RuntimeSession`.
  // This pointer needs to be valid during the lifetime of this object.
  //
  // The optional `write_request` function is meant for testing purposes or
  // overriding the write behavior.
  explicit P4rtProgrammingContext(
      p4_runtime::P4RuntimeSession* session,
      std::function<absl::Status(p4_runtime::P4RuntimeSession*,
                                 p4::v1::WriteRequest&)>
          write_request = p4_runtime::SetMetadataAndSendPiWriteRequest)
      : session_(session),
        write_request_(std::move(write_request)),
        inverse_programming_requests_(),
        write_request_function_(
            absl::bind_front(&P4rtProgrammingContext::SendWriteRequest, this)) {
  }

  P4rtProgrammingContext(const P4rtProgrammingContext &other) = delete;
  P4rtProgrammingContext(P4rtProgrammingContext &&other) = default;

  // The destructor reverts the programmed requests, logging an error if it
  // fails to do so.
  ~P4rtProgrammingContext();

  P4rtProgrammingContext &
  operator=(const P4rtProgrammingContext &other) = delete;
  P4rtProgrammingContext &operator=(P4rtProgrammingContext &&other) = default;

  // Returns the `SendWriteRequest` function as a standalone function for
  // convenience.
  const std::function<absl::Status(p4::v1::WriteRequest &)> &
  GetWriteRequestFunction() const {
    return write_request_function_;
  }

  // Sends a write `request` to the `P4RuntimeSession`. This function only
  // supports INSERT and DELETE operations.
  absl::Status SendWriteRequest(p4::v1::WriteRequest &request);

  // Reverts all programmed write requests by sending them back in reverse order
  // with INSERT replaced by DELETE and vice versa.
  absl::Status Revert();

 private:
  p4_runtime::P4RuntimeSession* session_;
  std::function<absl::Status(p4_runtime::P4RuntimeSession*,
                             p4::v1::WriteRequest&)>
      write_request_;
  std::vector<p4::v1::WriteRequest> inverse_programming_requests_;
  std::function<absl::Status(p4::v1::WriteRequest &)> write_request_function_;
};

} // namespace pins_test

#endif // GOOGLE_LIB_P4RT_P4RT_PROGRAMMING_CONTEXT_H_
