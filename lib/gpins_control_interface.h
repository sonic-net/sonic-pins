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

#ifndef GOOGLE_LIB_GPINS_CONTROL_INTERFACE_H_
#define GOOGLE_LIB_GPINS_CONTROL_INTERFACE_H_

#include <memory>

#include "absl/container/flat_hash_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "diag/diag.grpc.pb.h"
#include "system/system.grpc.pb.h"
#include "thinkit/control_interface.h"
#include "thinkit/switch.h"

namespace pins_test {

class GpinsControlInterface : public thinkit::ControlInterface {
 public:
  GpinsControlInterface(std::unique_ptr<thinkit::Switch> sut)
      : sut_(std::move(sut)) {}

  absl::Status SetAdminLinkState(absl::Span<const std::string> interfaces,
                                 thinkit::LinkState state) override;

  absl::Status Reboot(thinkit::RebootType reboot_type) override;

  absl::StatusOr<::gnoi::diag::StartBERTResponse> StartBERT(
      const ::gnoi::diag::StartBERTRequest& request) override;

  absl::StatusOr<::gnoi::diag::StopBERTResponse> StopBERT(
      const ::gnoi::diag::StopBERTRequest& request) override;

  absl::StatusOr<::gnoi::diag::GetBERTResultResponse> GetBERTResult(
      const ::gnoi::diag::GetBERTResultRequest& request) override;

  absl::StatusOr<absl::flat_hash_set<std::string>> GetUpLinks(
      absl::Span<const std::string> interfaces) override;

  absl::Status CheckUp() override;

 private:
  std::unique_ptr<thinkit::Switch> sut_;
};

}  // namespace pins_test

#endif  // GOOGLE_LIB_GPINS_CONTROL_INTERFACE_H_
