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

#ifndef GOOGLE_THINKIT_MOCK_CONTROL_INTERFACE_H_
#define GOOGLE_THINKIT_MOCK_CONTROL_INTERFACE_H_

#include "absl/container/flat_hash_set.h"
#include "absl/status/statusor.h"
#include "diag/diag.grpc.pb.h"
#include "gmock/gmock.h"
#include "thinkit/control_interface.h"

namespace thinkit {
class MockControlInterface : public ControlInterface {
 public:
  MOCK_METHOD(absl::Status, SetAdminLinkState,
              (absl::Span<const std::string> sut_ports, LinkState state),
              (override));
  MOCK_METHOD(absl::Status, Reboot, (RebootType reboot_Type), (override));
  MOCK_METHOD(absl::StatusOr<gnoi::diag::StartBERTResponse>, StartBERT,
              (const gnoi::diag::StartBERTRequest& request), (override));
  MOCK_METHOD(absl::StatusOr<gnoi::diag::StopBERTResponse>, StopBERT,
              (const gnoi::diag::StopBERTRequest& request), (override));
  MOCK_METHOD(absl::StatusOr<gnoi::diag::GetBERTResultResponse>, GetBERTResult,
              (const gnoi::diag::GetBERTResultRequest& request));
  MOCK_METHOD(absl::StatusOr<absl::flat_hash_set<std::string>>, GetUpLinks,
              (absl::Span<const std::string> sut_ports), (override));
  MOCK_METHOD(absl::Status, CheckUp, (), (override));
};

}  // namespace thinkit

#endif  // GOOGLE_THINKIT_MOCK_CONTROL_INTERFACE_H_
