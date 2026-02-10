// Copyright 2022 Google LLC
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
#include "p4rt_app/scripts/p4rt_tool_helpers.h"

#include <cstdint>
#include <iostream>
#include <memory>
#include <string>

#include "absl/flags/flag.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_format.h"
#include "absl/strings/string_view.h"
#include "grpcpp/security/credentials.h"
#include "p4_infra/p4_pdpi/p4_runtime_session.h"

ABSL_FLAG(std::string, p4rt_server_address, "unix:/sock/p4rt.sock",
          "Server address of the P4RT service.");
ABSL_FLAG(uint64_t, p4rt_device_id, 183807201,
          "Device ID for the P4RT service");
ABSL_FLAG(bool, use_insecure_credentials, false,
          "Use insecure credentials when connecting to the P4RT service.");

namespace p4rt_app {

void Info(absl::string_view message) {
  std::cout << absl::StreamFormat("%s\n", message);
}

void Warning(absl::string_view message) {
  std::cerr << absl::StreamFormat("\033[1;33m%s\033[0m\n", message);
}

void Error(absl::string_view message) {
  std::cerr << absl::StreamFormat("\033[1;31m%s\033[0m\n", message);
}

absl::StatusOr<std::unique_ptr<pdpi::P4RuntimeSession>> CreateP4rtSession() {
  std::shared_ptr<grpc::ChannelCredentials> credentials;
  if (absl::GetFlag(FLAGS_use_insecure_credentials)) {
    credentials = grpc::InsecureChannelCredentials();
  } else {
    credentials = grpc::experimental::LocalCredentials(UDS);
  }

  auto stub = pdpi::CreateP4RuntimeStub(
      absl::GetFlag(FLAGS_p4rt_server_address), credentials);
  return pdpi::P4RuntimeSession::Create(std::move(stub),
                                        absl::GetFlag(FLAGS_p4rt_device_id));
}

}  // namespace p4rt_app
