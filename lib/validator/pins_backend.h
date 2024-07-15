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

#ifndef GOOGLE_LIB_VALIDATOR_PINS_BACKEND_H_
#define GOOGLE_LIB_VALIDATOR_PINS_BACKEND_H_

#include "absl/container/flat_hash_map.h"
#include "absl/functional/bind_front.h"
#include "lib/validator/validator.h"
#include "lib/validator/validator_backend.h"
#include "thinkit/switch.h"

namespace pins_test {

class PINSBackend : public ValidatorBackend {
 public:
  // Validates if a P4Runtime can be connected to and used.
  static constexpr absl::string_view kP4RuntimeUsable = "P4RuntimeUsable";
  // Validates if a gNMI can be connected to and used.
  static constexpr absl::string_view kGnmiUsable = "GnmiUsable";

  PINSBackend(std::vector<std::unique_ptr<thinkit::Switch>> switches);

  // Checks if a P4Runtime session could be established.
  absl::Status CanEstablishP4RuntimeSession(absl::string_view chassis,
                                            absl::Duration timeout);

  // Checks if a gNMI get all interface request can be sent and a response
  // received.
  absl::Status CanGetAllInterfaceOverGnmi(absl::string_view chassis,
                                          absl::Duration timeout);

 protected:
  void SetupValidations() override {
    AddCallbacksToValidation(
        kP4RuntimeUsable,
        {absl::bind_front(&PINSBackend::CanEstablishP4RuntimeSession, this)});
    AddCallbacksToValidation(
        kGnmiUsable,
        {absl::bind_front(&PINSBackend::CanGetAllInterfaceOverGnmi, this)});
    AddCallbacksToValidation(
        Validator::kReady,
        {absl::bind_front(&PINSBackend::CanEstablishP4RuntimeSession, this),
         absl::bind_front(&PINSBackend::CanGetAllInterfaceOverGnmi, this)});
  }

 private:
  absl::flat_hash_map<std::string, std::unique_ptr<thinkit::Switch>>
      switches_map_;
};

}  // namespace pins_test
#endif  // GOOGLE_LIB_VALIDATOR_PINS_BACKEND_H_
