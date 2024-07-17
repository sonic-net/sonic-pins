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

#ifndef GOOGLE_THINKIT_CONTROL_INTERFACE_H_
#define GOOGLE_THINKIT_CONTROL_INTERFACE_H_

#include "absl/container/flat_hash_set.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "diag/diag.grpc.pb.h"

namespace thinkit {

enum class LinkState {
  kUnknown,
  kUp,
  kDown,
};

enum class RebootType {
  kUnknown,
  kWarm,
  kCold,
};

class ControlInterface {
 public:
  virtual ~ControlInterface() {}

  // Sets the admin link state on the control interface 'interfaces'.
  virtual absl::Status SetAdminLinkState(
      absl::Span<const std::string> interfaces, LinkState state) = 0;

  // Reboots the control interface.
  virtual absl::Status Reboot(RebootType reboot_type) = 0;

  // BERT functions.
  virtual absl::StatusOr<gnoi::diag::StartBERTResponse> StartBERT(
      const gnoi::diag::StartBERTRequest& request) = 0;

  virtual absl::StatusOr<gnoi::diag::StopBERTResponse> StopBERT(
      const gnoi::diag::StopBERTRequest& request) = 0;

  virtual absl::StatusOr<gnoi::diag::GetBERTResultResponse> GetBERTResult(
      const gnoi::diag::GetBERTResultRequest& request) = 0;

  // Gets the control interface’s `interfaces` with both admin-status and
  // oper-status up.
  virtual absl::StatusOr<absl::flat_hash_set<std::string>> GetUpLinks(
      absl::Span<const std::string> interfaces) = 0;

  // Checks if the control interface is up.
  virtual absl::Status CheckUp() = 0;
};

}  // namespace thinkit

#endif  // GOOGLE_THINKIT_CONTROL_INTERFACE_H_
