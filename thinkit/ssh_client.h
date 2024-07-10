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

#ifndef THINKIT_SSH_CLIENT_H_
#define THINKIT_SSH_CLIENT_H_

#include <string>

#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"
#include "absl/time/time.h"

namespace thinkit {

// RemoteFile represents a file on a remote device. It is meant to be used as a
// parameter object with designated initializers.
struct RemoteFile {
  absl::string_view device;
  absl::string_view file_path;
};

// SSHClient handles running remote commands or getting/putting remote files
// onto a specified device. As these operations are whitebox and platform
// specific, this interface should be used sparingly and only when needed.
class SSHClient {
 public:
  virtual ~SSHClient() {}

  // Runs the specified command on the device and returns stdout. If SSH
  // succeeds but the command returns stderr, then this returns an UNKNOWN_ERROR
  // status.
  virtual absl::StatusOr<std::string> RunCommand(absl::string_view device,
                                                 absl::string_view command,
                                                 absl::Duration timeout) = 0;

  // Copies a local file's contents to a remote destination file, creating a new
  // file if needed and replacing any existing contents that was there.
  virtual absl::Status PutFile(absl::string_view source,
                               const RemoteFile& destination,
                               absl::Duration timeout) = 0;

  // Puts the provided contents into a remote destination file, creating a new
  // file if needed and replacing any existing contents that was there.
  virtual absl::Status PutFileContents(absl::string_view contents,
                                       const RemoteFile& destination,
                                       absl::Duration timeout) = 0;

  // Copies a remote file's contents to a local file, creating a new
  // file if needed and replacing any existing contents that was there.
  virtual absl::Status GetFile(const RemoteFile& source,
                               absl::string_view destination,
                               absl::Duration timeout) = 0;

  // Returns the contents of a remote file.
  virtual absl::StatusOr<std::string> GetFileContents(
      const RemoteFile& source, absl::Duration timeout) = 0;
};

}  // namespace thinkit

#endif  // THINKIT_SSH_CLIENT_H_
