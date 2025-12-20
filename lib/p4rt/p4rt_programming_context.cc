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

#include "lib/p4rt/p4rt_programming_context.h"

#include <functional>
#include <iterator>
#include <type_traits>
#include <vector>

#include "absl/log/log.h"
#include "absl/status/status.h"
#include "gutil/gutil/status.h"
#include "p4/v1/p4runtime.pb.h"

namespace pins_test {
namespace {

// Returns the write `request` with INSERT replaced with DELETE or vice versa.
p4::v1::WriteRequest InvertP4rtRequest(p4::v1::WriteRequest request) {
  for (p4::v1::Update& update : *request.mutable_updates()) {
    switch (update.type()) {
      case p4::v1::Update::INSERT:
        update.set_type(p4::v1::Update::DELETE);
        break;
      case p4::v1::Update::DELETE:
        update.set_type(p4::v1::Update::INSERT);
        break;
      default:
        // Should never occur.
        update.set_type(p4::v1::Update::UNSPECIFIED);
        break;
    }
  }
  return request;
}

}  // namespace

P4rtProgrammingContext::~P4rtProgrammingContext() {
  absl::Status status = Revert();
  if (!status.ok()) {
    LOG(ERROR) << "Failed to revert P4RT programming requests: " << status;
  }
}

absl::Status P4rtProgrammingContext::SendWriteRequest(
    p4::v1::WriteRequest& request) {
  for (const p4::v1::Update& update : request.updates()) {
    if (update.type() != p4::v1::Update_Type_INSERT &&
        update.type() != p4::v1::Update_Type_DELETE) {
      return absl::InvalidArgumentError(
          "Only requests that insert or delete table entries are supported.");
    }
  }
  RETURN_IF_ERROR(write_request_(session_, request));
  inverse_programming_requests_.push_back(InvertP4rtRequest(request));
  return absl::OkStatus();
}

absl::Status P4rtProgrammingContext::Revert() {
  for (auto it = inverse_programming_requests_.rbegin();
       it != inverse_programming_requests_.rend(); ++it) {
    RETURN_IF_ERROR(write_request_(session_, *it));
    inverse_programming_requests_.erase(std::next(it).base());
  }
  return absl::OkStatus();
}

}  // namespace pins_test
