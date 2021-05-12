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

#ifndef THINKIT_MOCK_SSH_CLIENT_H_
#define THINKIT_MOCK_SSH_CLIENT_H_

#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"
#include "gmock/gmock.h"
#include "thinkit/ssh_client.h"

namespace thinkit {

class MockSSHClient : public SSHClient {
 public:
  MOCK_METHOD(absl::StatusOr<std::string>, RunCommand,
              (absl::string_view, absl::string_view, absl::Duration),
              (override));
  MOCK_METHOD(absl::Status, PutFile,
              (absl::string_view, const RemotePath&, absl::Duration),
              (override));
  MOCK_METHOD(absl::Status, PutFileContents,
              (absl::string_view, const RemotePath&, absl::Duration),
              (override));
  MOCK_METHOD(absl::Status, GetFile,
              (const RemotePath&, absl::string_view, absl::Duration),
              (override));
  MOCK_METHOD(absl::StatusOr<std::string>, GetFileContents,
              (const RemotePath&, absl::Duration), (override));
  MOCK_METHOD(absl::Status, GetDirectory,
              (const RemotePath&, absl::string_view, absl::Duration),
              (override));
};

}  // namespace thinkit

#endif  // THINKIT_MOCK_SSH_CLIENT_H_
