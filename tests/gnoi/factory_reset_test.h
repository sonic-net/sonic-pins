// Copyright 2024 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#ifndef PINS_TESTS_GNOI_FACTORY_RESET_TEST_H_
#define PINS_TESTS_GNOI_FACTORY_RESET_TEST_H_

#include "factory_reset/factory_reset.pb.h"
#include "thinkit/mirror_testbed_fixture.h"
#include "thinkit/ssh_client.h"

namespace factory_reset {

void IssueGnoiFactoryResetAndValidateStatus(
    thinkit::Switch &sut, const gnoi::factory_reset::StartRequest &request,
    gnoi::factory_reset::StartResponse *response,
    grpc::Status expected_status = grpc::Status());

void ValidateStackState(thinkit::Switch &sut,
                        absl::Span<const std::string> interfaces);

void TestFactoryResetSuccess(thinkit::Switch &sut,
                             thinkit::SSHClient &ssh_client,
                             absl::Span<const std::string> interfaces);

void TestDuplicateFactoryResetFailure(thinkit::Switch &sut,
                                      thinkit::SSHClient &ssh_client,
                                      absl::Span<const std::string> interfaces);

void TestGnoiFactoryResetGnoiServerUnreachableFail(
    thinkit::Switch &sut, thinkit::SSHClient &ssh_client,
    absl::Span<const std::string> interfaces);

} // namespace factory_reset

#endif // PINS_TESTS_GNOI_FACTORY_RESET_TEST_H_
