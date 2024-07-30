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

#ifndef PINS_LIB_VALIDATOR_COMMON_BACKEND_H_
#define PINS_LIB_VALIDATOR_COMMON_BACKEND_H_

#include "absl/functional/bind_front.h"
#include "lib/validator/validator.h"
#include "lib/validator/validator_backend.h"
#include "thinkit/ssh_client.h"

namespace pins_test {

class CommonBackend : public ValidatorBackend {
 public:
  // Tags for a single validation.
  static constexpr absl::string_view kPingable = "Pingable";
  static constexpr absl::string_view kSSHable = "Sshable";

  CommonBackend(absl::flat_hash_set<std::string> chassis,
                std::unique_ptr<thinkit::SSHClient> ssh_client)
      : ValidatorBackend(std::move(chassis)),
        ssh_client_(std::move(ssh_client)) {}

  // Checks if the switch can be pinged.
  absl::Status IsPingable(absl::string_view chassis, absl::Duration timeout);

  // Checks if ssh access to the switch is working.
  absl::Status IsSSHable(absl::string_view chassis, absl::Duration timeout);

 protected:
  void SetupValidations() override {
    Callback pingable = absl::bind_front(&CommonBackend::IsPingable, this);
    Callback sshable = absl::bind_front(&CommonBackend::IsSSHable, this);

    AddCallbacksToValidation(kPingable, {pingable});
    AddCallbacksToValidation(kSSHable, {sshable});
    AddCallbacksToValidation(Validator::kReady, {pingable, sshable});
  }

  std::unique_ptr<thinkit::SSHClient> ssh_client_;
};

}  // namespace pins_test

#endif  // PINS_LIB_VALIDATOR_COMMON_BACKEND_H_
